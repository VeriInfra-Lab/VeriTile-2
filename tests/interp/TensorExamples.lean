import VeriTile.Interp.Reflect
import VeriTile.Interp.Run.FileProgram
import bench.examples.AdamUpdateGridLaunch.Kernels
import bench.examples.FloatDTypeSoftmax.Kernels
import bench.examples.FusedLayerNorm.Kernels
import bench.examples.FusedSiLU.Kernels
import bench.examples.FusedSwiglu.Kernels
import bench.examples.LogExp.Kernels
import bench.examples.RowWiseMax.Kernels
import bench.examples.RowWiseSum.Kernels
import bench.examples.SoftmaxReciprocal.Kernels
import bench.examples.SoftmaxStable.Kernels
import bench.examples.StableLogSumExp.Kernels
import bench.examples.Welford.Kernels

namespace VeriTile.Interp.Run

/-- The native registry reports the source declaration used to build each runnable entry. -/
structure ExampleBinding (α : Type) where
  source : String
  entry : α

open Lean Elab Term in
/-- Apply the runner's binder to this alias's reflected mirror and retain the
head declaration of the very same alias for the machine-readable manifest. -/
elab "bind_example% " wrapper:ident " => " binder:term : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo wrapper
  let info ← getConstInfo name
  let some body := info.value? | throwErrorAt wrapper "expected a defined example wrapper"
  let rec head : Expr → Expr
    | .lam _ _ e _ | .mdata _ e => head e
    | e => e.getAppFn
  let .const source _ := head body | throwErrorAt wrapper "expected a direct example kernel application"
  unless (`VeriTile.Bench.Examples).isPrefixOf source do
    throwErrorAt wrapper "expected an example kernel, found {source}"
  let mirror := mkIdentFrom wrapper (name ++ `mirror)
  let text := Syntax.mkStrLit source.toString
  elabTerm (← `(ExampleBinding.mk $text ($binder $mirror))) none

end VeriTile.Interp.Run

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
def fp64Softmax (b : Nat) := FloatDTypeSoftmax.Kernels.floatStableSoftmaxKernel "xReg" "yReg" b
def swiglu (n b : Nat) := FusedSwiglu.Kernels.swiglu_fused_kernel "X" "Y" "OUT" n b
def logExp (b : Nat) := LogExp.originalKernel "xReg" "yReg" b
def logExpGuarded (b : Nat) := LogExp.optimizedKernel "xReg" "yReg" b
def reciprocalSoftmax (b : Nat) := SoftmaxReciprocal.Kernels.softmaxRecipKernel "xReg" "yReg" b
def stableSoftmax (b : Nat) := SoftmaxStable.Kernels.stableSoftmaxKernel "xReg" "yReg" b
def stableLSE (b : Nat) := StableLogSumExp.Kernels.optimizedLSEKernel "xReg" "yReg" b

reflect_kernel adam
reflect_kernel norm
reflect_kernel maximum
reflect_kernel sumRows
reflect_kernel welford
reflect_kernel fused
reflect_kernel gate
reflect_kernel activation
reflect_kernel residual
reflect_kernel fp64Softmax
reflect_kernel swiglu
reflect_kernel logExp
reflect_kernel logExpGuarded
reflect_kernel reciprocalSoftmax
reflect_kernel stableSoftmax
reflect_kernel stableLSE

def gridX (grid : List Nat) : Except String Nat := do
  let x := grid.headD 0
  unless x > 0 && grid.tail.all (· == 1) do throw "expected a positive one-dimensional grid"
  return x

private def adamEntry (kernel : ℚ → ℚ → ℚ → ℚ → Nat → Nat → QKernel) : FileEntry where
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
    let k := kernel (← fp32Setting cfg "lr") (← fp32Setting cfg "wd")
      (← fp32Setting cfg "beta1") (← fp32Setting cfg "beta2") n block
    runBinary64Files dims k ((["p_ptr","grad_ptr","exp_avg_ptr"] : List RegionName).zip ts)
      [⟨"p_ptr",.fp32,[n],none⟩, ⟨"exp_avg_ptr",.fp32,[n],none⟩]

private def layerNormEntry (kernel : Nat → Nat → ℚ → QKernel) : FileEntry where
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
    runBinary64Files dims (kernel n stride (← setting cfg.constants "ε"))
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

private def welfordEntry (kernel : Nat → Nat → QKernel) : FileEntry where
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
    runBinary64Files dims (kernel n stride) [("xReg",x)] [⟨"meanReg",.bf16,[1],none⟩,⟨"varReg",.bf16,[1],none⟩]

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

private def roundedRowEntry (widthKey : String) (dtype : DType) (scalarPerRow : Bool)
    (kernel : Nat → QKernel) : FileEntry where
  inputs := ["xReg"]
  outputs := ["yReg"]
  carrier := "source-rounded"
  run cfg dims ts := do
    cfg.check [widthKey] []
    let rows ← gridX dims
    let width ← naturalSetting cfg.constants widthKey
    unless width > 0 do throw "row width must be positive"
    let [t] := ts | throw "expected one matrix"
    checkInput t .fp32 [rows,width]
    let shape := if scalarPerRow then [rows] else [rows,width]
    runFloatFiles Binary64.sourceRoundedAlgebra dims (kernel width) [("xReg",t)]
      [⟨"yReg",dtype,shape,none⟩]

private def logExpEntry (kernel : Nat → QKernel) : FileEntry where
  inputs := ["xReg"]
  outputs := ["yReg"]
  carrier := "source-rounded"
  run cfg dims ts := do
    cfg.check ["blockSize"] []
    let b ← naturalSetting cfg.constants "blockSize"
    unless b > 0 do throw "blockSize must be positive"
    let shape := [(← gridX dims) * b]
    let [t] := ts | throw "expected one vector"
    checkInput t .fp32 shape
    runFloatFiles Binary64.sourceRoundedAlgebra dims (kernel b) [("xReg",t)]
      [⟨"yReg",.fp32,shape,none⟩]

private def swigluEntry (kernel : Nat → Nat → QKernel) : FileEntry where
  inputs := ["X","Y"]
  outputs := ["OUT"]
  carrier := "source-rounded"
  run cfg dims ts := do
    cfg.check ["ncols","BLOCK_N"] []
    let n ← naturalSetting cfg.constants "ncols"
    let b ← naturalSetting cfg.constants "BLOCK_N"
    let grid ← gridX dims
    unless n > 0 && b > 0 && grid == (n + b - 1) / b do
      throw "SwiGLU expects ceil(ncols/BLOCK_N) programs over nonempty vectors"
    for t in ts do checkInput t .fp32 [n]
    runFloatFiles Binary64.sourceRoundedAlgebra dims (kernel n b)
      ((["X","Y"] : List RegionName).zip ts) [⟨"OUT",.bf16,[n],none⟩]

def tensorExamples : List (String × ExampleBinding FileEntry) := [
  ("AdamUpdateGridLaunch", bind_example% adam => adamEntry),
  ("FusedLayerNorm", bind_example% norm => layerNormEntry),
  ("RowWiseMax", bind_example% maximum => rowEntry),
  ("RowWiseSum", bind_example% sumRows => rowEntry),
  ("Welford", bind_example% welford => welfordEntry),
  ("FusedSiLU", bind_example% fused => siluEntry ["xReg","gateReg","residualReg"] "outReg" .bf16),
  ("FusedSiLUGate", bind_example% gate => siluEntry ["xReg","gateReg"] "zReg" .fp64),
  ("FusedSiLUActivation", bind_example% activation => siluEntry ["zReg"] "siluReg" .fp64),
  ("FusedSiLUResidual", bind_example% residual => siluEntry ["siluReg","residualReg"] "outReg" .bf16),
  ("FloatDTypeSoftmax", bind_example% fp64Softmax => roundedRowEntry "blockSize" .fp32 Bool.false),
  ("FusedSwiglu", bind_example% swiglu => swigluEntry),
  ("LogExp", bind_example% logExp => logExpEntry),
  ("LogExpOptimized", bind_example% logExpGuarded => logExpEntry),
  ("SoftmaxReciprocal", bind_example% reciprocalSoftmax => roundedRowEntry "blockSize" .bf16 Bool.false),
  ("SoftmaxStable", bind_example% stableSoftmax => roundedRowEntry "B" .bf16 Bool.false),
  ("StableLogSumExp", bind_example% stableLSE => roundedRowEntry "blockSize" .bf16 Bool.true)]

end VeriTile.Interp.Run.Examples
