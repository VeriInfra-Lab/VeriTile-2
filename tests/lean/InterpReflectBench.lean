/- Reflection and kernel-checked equations for the bench examples, rejection tests,
source coverage, and three executions with rational parameters. -/
import VeriTile.Interp.Reflect
import tests.lean.InterpReflectSmoke
import bench.examples.AdamUpdateGridLaunch.Kernels
import bench.examples.FlatVectorAdd.Kernels
import bench.examples.FloatDTypeAdd.Kernels
import bench.examples.FloatDTypeSoftmax.Kernels
import bench.examples.FusedLayerNorm.Kernels
import bench.examples.FusedSiLU.Kernels
import bench.examples.FusedSwiglu.Kernels
import bench.examples.HyperConnectionsDepth.Kernels
import bench.examples.HyperConnectionsWidth.Kernels
import bench.examples.LogExp.Kernels
import bench.examples.OnlineSoftmax.Kernels
import bench.examples.RowWiseMax.Kernels
import bench.examples.RowWiseSum.Kernels
import bench.examples.SoftmaxReciprocal.Kernels
import bench.examples.SoftmaxStable.Kernels
import bench.examples.StableLogSumExp.Kernels
import bench.examples.VectorAdd.Kernels
import bench.examples.Welford.Kernels

open VeriTile.Bench.Examples

reflect_kernel AdamUpdateGridLaunch.Kernels.update_fn_kernel
reflect_kernel AdamUpdateGridLaunch.Kernels.commuted_update_kernel
reflect_kernel AdamUpdateGridLaunch.Kernels.originalKernel
reflect_kernel AdamUpdateGridLaunch.Kernels.optimizedKernel
reflect_kernel FlatVectorAdd.Kernels.addMaskedKernel
reflect_kernel FlatVectorAdd.Kernels.commutedKernel
reflect_kernel FlatVectorAdd.Kernels.originalKernel
reflect_kernel FlatVectorAdd.Kernels.optimizedKernel
reflect_kernel FloatDTypeAdd.Kernels.floatAddKernel
reflect_kernel FloatDTypeAdd.Kernels.commutedKernel
reflect_kernel FloatDTypeAdd.Kernels.originalKernel
reflect_kernel FloatDTypeAdd.Kernels.optimizedKernel
reflect_kernel FloatDTypeSoftmax.Kernels.floatStableSoftmaxKernel
reflect_kernel FloatDTypeSoftmax.Kernels.floatSoftmaxRecipKernel
/-- error: reflect_kernel: unsupported constructor VeriTile.Triton.ComputeKernel.rec -/
#guard_msgs (error, substring := true) in
reflect_kernel FloatDTypeSoftmax.Kernels.commonPrefix
reflect_kernel FloatDTypeSoftmax.Kernels.originalKernel
reflect_kernel FloatDTypeSoftmax.Kernels.reciprocalKernel
reflect_kernel FusedLayerNorm.Kernels.twoPassLayerNormKernel
reflect_kernel FusedLayerNorm.Kernels.fusedLayerNormKernel
reflect_kernel FusedSiLU.Kernels.fusedSiLUKernel
reflect_kernel FusedSiLU.Kernels.siluStepGateKernel
reflect_kernel FusedSiLU.Kernels.siluStepSiluKernel
reflect_kernel FusedSiLU.Kernels.siluStepResidualKernel
/-- error: reflect_kernel: unsupported constructor VeriTile.Triton.ComputeKernel.rec -/
#guard_msgs (error, substring := true) in
reflect_kernel FusedSiLU.Kernels.unfusedSiLUKernel
reflect_kernel FusedSwiglu.Kernels.swiglu_fused_kernel
reflect_kernel FusedSwiglu.Kernels.silu_step_kernel
reflect_kernel FusedSwiglu.Kernels.mul_step_kernel
/-- error: reflect_kernel: unsupported constructor VeriTile.Triton.ComputeKernel.rec -/
#guard_msgs (error, substring := true) in
reflect_kernel FusedSwiglu.Kernels.swiglu_unfused
reflect_kernel HyperConnectionsDepth.Kernels.matrixKernel
reflect_kernel HyperConnectionsDepth.Kernels.scalarKernel
reflect_kernel HyperConnectionsDepth.Kernels.optimizedKernel
reflect_kernel HyperConnectionsDepth.Kernels.matrixOptimizedKernel
/-- error: reflect_kernel: symbolic dimension dispatch at bench.examples.HyperConnectionsDepth.Kernels:123: match S,T,D,numIters with -/
#guard_msgs in
reflect_kernel HyperConnectionsDepth.Kernels.mhcDepthConnectionKernel
reflect_kernel HyperConnectionsDepth.Kernels.originalKernel
reflect_kernel HyperConnectionsDepth.Kernels.matrixOriginal
reflect_kernel HyperConnectionsWidth.Kernels.matrixKernel
reflect_kernel HyperConnectionsWidth.Kernels.scalarKernel
reflect_kernel HyperConnectionsWidth.Kernels.middleKernel
reflect_kernel HyperConnectionsWidth.Kernels.optimizedKernel
reflect_kernel HyperConnectionsWidth.Kernels.matrixMiddleKernel
reflect_kernel HyperConnectionsWidth.Kernels.matrixOptimizedKernel
/-- error: reflect_kernel: symbolic dimension dispatch at bench.examples.HyperConnectionsWidth.Kernels:218: match S,T,D,numIters with -/
#guard_msgs in
reflect_kernel HyperConnectionsWidth.Kernels.mhcWidthConnectionKernel
reflect_kernel HyperConnectionsWidth.Kernels.originalKernel
reflect_kernel HyperConnectionsWidth.Kernels.matrixOriginal
reflect_kernel LogExp.originalKernel
reflect_kernel OnlineSoftmax.Kernels.stableSoftmaxKernel
reflect_kernel OnlineSoftmax.Kernels.onlineSoftmaxKernel
reflect_kernel OnlineSoftmax.Kernels.batchSoftmaxKernel
reflect_kernel RowWiseMax.Kernels.rowWiseMaxKernel
reflect_kernel RowWiseMax.Kernels.inlinedKernel
-- The smoke tests already provide mirrors for RowWiseSum, VectorAdd and optimized LogExp.
reflect_kernel RowWiseSum.Kernels.reversedKernel
reflect_kernel SoftmaxReciprocal.Kernels.stableSoftmaxKernel
reflect_kernel SoftmaxReciprocal.Kernels.softmaxRecipKernel
/-- error: reflect_kernel: unsupported constructor VeriTile.Triton.ComputeKernel.rec -/
#guard_msgs (error, substring := true) in
reflect_kernel SoftmaxReciprocal.Kernels.commonPrefix
reflect_kernel SoftmaxReciprocal.Kernels.originalKernel
reflect_kernel SoftmaxReciprocal.Kernels.reciprocalKernel
reflect_kernel SoftmaxStable.Kernels.naiveSoftmaxKernel
reflect_kernel SoftmaxStable.Kernels.stableSoftmaxKernel
reflect_kernel StableLogSumExp.Kernels.directLSEKernel
reflect_kernel StableLogSumExp.Kernels.optimizedLSEKernel
reflect_kernel VectorAdd.Kernels.addKernel
reflect_kernel VectorAdd.Kernels.commutedKernel
reflect_kernel VectorAdd.Kernels.optimizedKernel
reflect_kernel Welford.Kernels.twopassWelfordKernel
reflect_kernel Welford.Kernels.onlineWelfordKernel

namespace VeriTile.Tests.InterpReflectBench
open VeriTile Triton Interp
open VeriTile.Triton.FP

private def partialDepth (S : Nat) (tau : ℝ) : ComputeKernel :=
  HyperConnectionsDepth.Kernels.mhcDepthConnectionKernel "res_mix" "branch_out" "h_post" "out" S 1 1 0 tau

/-- error: reflect_kernel: symbolic dimension dispatch at bench.examples.HyperConnectionsDepth.Kernels:122: match S, 1, 1, 0 with -/
#guard_msgs in
reflect_kernel partialDepth

-- Binary64 arithmetic for these small fixtures. An unused mandatory operation
-- produces NaN so an unexpected dependency fails the output checks.
private def testCarrier : CAlgebra Float where
  literal := fun _ _ q => Float.ofInt q.num / q.den.toFloat
  negInf := -1 / 0
  binary := fun _ _ op a b => match op with
    | .add => a + b | .sub => a - b | .mul => a * b | .div => a / b
    | .max => max a b | .pow => a ^ b
  unary := fun _ op a => match op with
    | .neg _ => -a | .exp => a.exp | _ => 0 / 0
  compareLt := fun _ _ => some fun a b => decide (a < b)
  compareEq := fun _ _ => some (· == ·)
  cast := fun _ _ _ a => a
  fromNat := fun _ n => n.toFloat
  fromInt := fun _ => Float.ofInt
  fp32Bits := fun b => (Float32.ofBits b.bits.toNat.toUInt32).toFloat
  fp32Load := id
  reduceMax := fun _ {_} _ _ _ _ => 0 / 0
  reduceSum := fun _ {_} _ _ _ _ => 0 / 0

private def outputs (k : QKernel) (inputs : List (RegionName × Float)) (ports : List RegionName) :
    Option (List Float) := do
  let s ← interp testCarrier k {
    init := fun r _ => .mk .real ((inputs.lookup r).getD (-99))
    pids := fun _ => 0, numPids := fun _ => 1
    undef := fun d _ _ => Structural.defaultValue d }
  return ports.map fun r => (s.read r 0).read .real

-- p=4 shrinks by 1-(1/2)(1/4), then falls by 1/2; momentum becomes (6-2)(1/4)+2.
#guard outputs (AdamUpdateGridLaunch.Kernels.originalKernel.mirror (1/2) (1/4) (1/2) (1/4) 1 1)
  [("p", 4), ("grad", 2), ("exp_avg", 6)] ["p", "exp_avg"] == some [3, 3]

-- tau=1/2: post/tau=2, so 1+2 exp(2) is approximately 15.778112.
#guard match outputs (HyperConnectionsDepth.Kernels.originalKernel.mirror (1/2))
    [("res_mix", 1), ("branch_out", 2), ("h_post", 1)] ["out"] with
  | some [x] => (x - 15.778112).abs < 0.000001
  | _ => Bool.false

-- tau=2: logits 0 and 2 yield 3 and 3 exp(1), independently of the depth example.
#guard match outputs (HyperConnectionsWidth.Kernels.originalKernel.mirror 2)
    [("res", 3), ("h_res", 0), ("h_pre", 2)] ["res_mix", "branch_in"] with
  | some [x, y] => x == 3 && (y - 8.154845).abs < 0.000001
  | _ => Bool.false

end VeriTile.Tests.InterpReflectBench

open Lean in
#eval show Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  -- Read the declarations of the imported example files, independently of the reflection list.
  let mut rows := #[]
  let mut reflected := 0
  for mod in env.header.imports do
    let .str (.str (.str (.str .anonymous "bench") "examples") exampleDir) "Kernels" := mod.module
      | continue
    let some idx := env.getModuleIdx? mod.module | throwError "missing module {mod.module}"
    for info in env.header.moduleData[idx.toNat]!.constants do
      unless info.isDefinition && info.type.getForallBody.isConstOf ``VeriTile.Triton.ComputeKernel do
        continue
      let .str _ name := info.name | continue
      let reason ← if env.contains (info.name ++ `toReal_mirror) then do
        reflected := reflected + 1
        pure "Reflected"
      else
        let id := mkIdent info.name
        let saved ← get
        let messages ← try
          modify fun st => { st with messages := {} }
          Elab.Command.elabCommand (← `(command| reflect_kernel $id:ident))
          pure (← get).messages.toList
        finally set saved
        let [err] := messages.filter (·.severity == .error)
          | throwError "expected one rejection for {info.name}"
        err.data.toString
      let file := s!"bench/examples/{exampleDir}/Kernels.lean"
      let some ranges ← findDeclarationRanges? info.name | throwError "missing source range {info.name}"
      let line := ranges.selectionRange.pos.line
      rows := rows.push ((exampleDir, line), s!"| [{exampleDir}](../{file}#L{line}) | `{name}` | {reason} |")
  for (_, row) in rows.qsort (fun a b => a.1.1 < b.1.1 || (a.1.1 == b.1.1 && a.1.2 < b.1.2)) do IO.println row
  IO.println s!"{reflected} of {rows.size} kernels reflected."
