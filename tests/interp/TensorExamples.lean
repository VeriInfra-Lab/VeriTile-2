import VeriTile.Interp.Reflect
import VeriTile.Interp.Run.FileProgram
import bench.examples.AdamUpdateGridLaunch.Kernels
import bench.examples.FusedLayerNorm.Kernels
import bench.examples.FusedSiLU.Kernels
import bench.examples.RowWiseMax.Kernels
import bench.examples.RowWiseSum.Kernels
import bench.examples.Welford.Kernels

namespace VeriTile.Interp.Run.Examples
open VeriTile.Triton VeriTile.Bench.Examples

-- Keep the registered source mirrors independent of the full reflection census.
def adam (lr wd b1 b2 : ℝ) (n block : Nat) :=
  AdamUpdateGridLaunch.Kernels.update_fn_kernel "p_ptr" "grad_ptr" "exp_avg_ptr" lr wd b1 b2 n block
def norm (n stride : Nat) (eps : ℝ) :=
  FusedLayerNorm.Kernels.fusedLayerNormKernel "xReg" "γReg" "βReg" "yReg" n stride eps
def maximum (n block : Nat) := RowWiseMax.Kernels.rowWiseMaxKernel "xReg" "yReg" n block
def sumRows (n block : Nat) := RowWiseSum.Kernels.rowWiseSumKernel "xReg" "yReg" n block
def welford (n stride : Nat) := Welford.Kernels.onlineWelfordKernel "xReg" "meanReg" "varReg" n stride
def fused (b : Nat) := FusedSiLU.Kernels.fusedSiLUKernel "xReg" "gateReg" "residualReg" "outReg" b
def gate (b : Nat) := FusedSiLU.Kernels.siluStepGateKernel "xReg" "gateReg" "zReg" b
def activation (b : Nat) := FusedSiLU.Kernels.siluStepSiluKernel "zReg" "siluReg" b
def residual (b : Nat) := FusedSiLU.Kernels.siluStepResidualKernel "siluReg" "residualReg" "outReg" b

reflect_kernel adam
reflect_kernel norm
reflect_kernel maximum
reflect_kernel sumRows
reflect_kernel welford
reflect_kernel fused
reflect_kernel gate
reflect_kernel activation
reflect_kernel residual

def gridX (grid : List Nat) : Except String Nat := do
  let x := grid.headD 0
  unless x > 0 && grid.tail.all (· == 1) do throw "expected a positive one-dimensional grid"
  return x

private def adamEntry : FileEntry where
  inputs := ["p_ptr", "grad_ptr", "exp_avg_ptr"]
  outputs := ["p_ptr", "exp_avg_ptr"]
  carrier := "binary64"
  run cfg dims ts := do
    cfg.check ["BLOCK_SIZE"] ["lr", "wd", "beta1", "beta2", "n_elements", "chunk_elements"]
    let n ← naturalSetting cfg.scalars "n_elements"
    let chunk ← naturalSetting cfg.scalars "chunk_elements"
    let block ← naturalSetting cfg.constants "BLOCK_SIZE"
    let grid ← gridX dims
    unless n > 0 && chunk == n && block > 0 && grid == (n + block - 1) / block do
      throw "Adam expects equal total and chunk lengths and ceil(length/BLOCK_SIZE) programs"
    for t in ts do checkInput t .fp32 [n]
    let k := adam.mirror (← fp32Setting cfg "lr") (← fp32Setting cfg "wd")
      (← fp32Setting cfg "beta1") (← fp32Setting cfg "beta2") n block
    runBinary64Files dims k ((["p_ptr","grad_ptr","exp_avg_ptr"] : List RegionName).zip ts)
      [⟨"p_ptr",.fp32,[n],none⟩, ⟨"exp_avg_ptr",.fp32,[n],none⟩]

private def layerNormEntry : FileEntry where
  inputs := ["xReg", "γReg", "βReg"]
  outputs := ["yReg"]
  carrier := "binary64"
  run cfg dims ts := do
    cfg.check ["N","ε"] ["rowStride"]
    let n ← naturalSetting cfg.constants "N"
    let stride ← naturalSetting cfg.scalars "rowStride"
    let rows ← gridX dims
    unless n > 0 && stride ≥ n do throw "rowStride must be at least N"
    let [x,g,b] := ts | throw "expected x, scale and bias"
    checkInput x .fp32 [rows,stride]
    for t in [g,b] do checkInput t .fp32 [n]
    runBinary64Files dims (norm.mirror n stride (← setting cfg.constants "ε"))
      [("xReg",x),("γReg",g),("βReg",b)] [{ name := "yReg", dtype := .bf16, shape := [rows,n], rowStride := some stride }]

private def rowEntry (kernel : Nat → Nat → QKernel) : FileEntry where
  inputs := ["xReg"]
  outputs := ["yReg"]
  carrier := "binary64"
  run cfg dims ts := do
    cfg.check ["nCol","blockSize"] []
    let rows ← gridX dims
    let n ← naturalSetting cfg.constants "nCol"
    let block ← naturalSetting cfg.constants "blockSize"
    unless n > 0 && block == n do throw "each program must reduce the complete row"
    let [t] := ts | throw "expected one matrix"
    checkInput t .fp32 [rows,n]
    runBinary64Files dims (kernel n block) [("xReg",t)] [⟨"yReg",.fp32,[rows],none⟩]

private def welfordEntry : FileEntry where
  inputs := ["xReg"]
  outputs := ["meanReg","varReg"]
  carrier := "binary64"
  run cfg dims ts := do
    cfg.check ["blockSize"] ["rowStride"]
    let n ← naturalSetting cfg.constants "blockSize"
    let stride ← naturalSetting cfg.scalars "rowStride"
    -- The pinned source writes both statistics at address zero.
    unless (← gridX dims) == 1 && n > 0 && stride ≥ n do throw "Welford expects one row with stride ≥ blockSize"
    let [x] := ts | throw "expected one matrix"
    checkInput x .fp32 [1,stride]
    runBinary64Files dims (welford.mirror n stride) [("xReg",x)] [⟨"meanReg",.bf16,[1],none⟩,⟨"varReg",.bf16,[1],none⟩]

private def siluEntry (inputs : List RegionName) (out : RegionName) (dtype : DType)
    (kernel : Nat → QKernel) : FileEntry where
  inputs := inputs
  outputs := [out]
  carrier := "binary64"
  run cfg dims ts := do
    cfg.check ["blockSize"] []
    let b ← naturalSetting cfg.constants "blockSize"
    unless b > 0 do throw "blockSize must be positive"
    let shape := [(← gridX dims) * b]
    for t in ts do checkInput t .fp64 shape
    runBinary64Files dims (kernel b) (inputs.zip ts) [⟨out,dtype,shape,none⟩]

def tensorExamples : List (String × FileEntry) := [
  ("AdamUpdateGridLaunch",adamEntry), ("FusedLayerNorm",layerNormEntry),
  ("RowWiseMax",rowEntry maximum.mirror), ("RowWiseSum",rowEntry sumRows.mirror),
  ("Welford",welfordEntry),
  ("FusedSiLU",siluEntry ["xReg","gateReg","residualReg"] "outReg" .bf16 fused.mirror),
  ("FusedSiLUGate",siluEntry ["xReg","gateReg"] "zReg" .fp64 gate.mirror),
  ("FusedSiLUActivation",siluEntry ["zReg"] "siluReg" .fp64 activation.mirror),
  ("FusedSiLUResidual",siluEntry ["siluReg","residualReg"] "outReg" .bf16 residual.mirror)]

end VeriTile.Interp.Run.Examples
