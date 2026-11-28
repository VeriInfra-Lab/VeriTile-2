import tests.interp.TensorExamples
import bench.examples.HyperConnectionsDepth.Kernels
import bench.examples.HyperConnectionsWidth.Kernels

namespace VeriTile.Interp.Run.Examples
open VeriTile.Triton VeriTile.Bench.Examples

def depthMatrix (s t d iters : Nat) (tau : ℝ) :=
  HyperConnectionsDepth.Kernels.matrixKernel "resMixReg" "branchOutReg" "hPostReg" "outReg" s t d iters tau
def depthScalar (tau : ℝ) :=
  HyperConnectionsDepth.Kernels.scalarKernel "resMixReg" "branchOutReg" "hPostReg" "outReg" tau
def widthMatrix (s t d iters : Nat) (tau : ℝ) :=
  HyperConnectionsWidth.Kernels.matrixKernel "resReg" "hResReg" "hPreReg" "resMixReg" "branchInReg" s t d iters tau

reflect_kernel depthMatrix
reflect_kernel depthScalar
reflect_kernel widthMatrix

private def dimensions (cfg : Settings) : Except String (Nat × Nat × Nat × Nat × ℚ) := do
  cfg.check ["S","T","D","numIters"] ["tau"]
  let s ← naturalSetting cfg.constants "S"
  let t ← naturalSetting cfg.constants "T"
  let d ← naturalSetting cfg.constants "D"
  let iters ← naturalSetting cfg.constants "numIters"
  let tau ← fp32Setting cfg "tau"
  unless min s (min t d) > 0 && tau > 0 do throw "dimensions and temperature must be positive"
  return (s,t,d,iters,tau)

private def depthEntry (kernel : Nat → Nat → Nat → Nat → ℚ → QKernel) : FileEntry where
  inputs := ["resMixReg","branchOutReg","hPostReg"]
  outputs := ["outReg"]
  carrier := "binary64"
  run cfg grid tensors := do
    let (s,t,d,iters,tau) ← dimensions cfg
    let batches ← gridX grid
    let [mix,branch,post] := tensors | throw "expected residual, branch and post tensors"
    checkInput mix .fp32 [batches,s,d]
    checkInput branch .fp32 [batches,t,d]
    checkInput post .fp32 [t,s]
    runBinary64Files grid (kernel s t d iters tau)
      [("resMixReg",mix),("branchOutReg",branch),("hPostReg",post)] [⟨"outReg",.fp32,[batches,s,d],none⟩]

private def depthScalarEntry (kernel : ℚ → QKernel) : FileEntry where
  inputs := ["resMixReg","branchOutReg","hPostReg"]
  outputs := ["outReg"]
  carrier := "binary64"
  run cfg grid tensors := do
    cfg.check [] ["tau"]
    let tau ← fp32Setting cfg "tau"
    unless tau > 0 do throw "temperature must be positive"
    let batches ← gridX grid
    let [mix,branch,post] := tensors | throw "expected residual, branch and post tensors"
    checkInput mix .fp32 [batches]
    checkInput branch .fp32 [batches]
    checkInput post .fp32 [1]
    runBinary64Files grid (kernel tau)
      [("resMixReg",mix),("branchOutReg",branch),("hPostReg",post)] [⟨"outReg",.fp32,[batches],none⟩]

private def widthEntry (kernel : Nat → Nat → Nat → Nat → ℚ → QKernel) : FileEntry where
  inputs := ["resReg","hResReg","hPreReg"]
  outputs := ["resMixReg","branchInReg"]
  carrier := "binary64"
  run cfg grid tensors := do
    let (s,t,d,iters,tau) ← dimensions cfg
    let batches ← gridX grid
    let [res,hRes,hPre] := tensors | throw "expected residuals, residual logits and pre logits"
    checkInput res .fp32 [batches,s,d]
    checkInput hRes .fp32 [s,s]
    checkInput hPre .fp32 [s,t]
    runBinary64Files grid (kernel s t d iters tau)
      [("resReg",res),("hResReg",hRes),("hPreReg",hPre)]
      [⟨"resMixReg",.fp32,[batches,s,d],none⟩,⟨"branchInReg",.fp32,[batches,t,d],none⟩]

def hyperExamples : List (String × ExampleBinding FileEntry) := [
  ("HyperConnectionsDepth", bind_example% depthMatrix => depthEntry),
  ("HyperConnectionsDepthScalar", bind_example% depthScalar => depthScalarEntry),
  ("HyperConnectionsWidth", bind_example% widthMatrix => widthEntry)]

end VeriTile.Interp.Run.Examples
