import VeriTile.Interp.Carrier.SymbolicExport
import VeriTile.Interp.Exec
import VeriTile.Interp.Reflect
import tests.lean.InterpEvalSmoke
import bench.examples.LogExp.Kernels

namespace VeriTile.Tests.InterpSymbolic
open VeriTile Triton Interp FP
open VeriTile.Bench.Examples

-- Reflect this test alias so a corpus-wide reflection can coexist in the same environment.
private def logExpSource := LogExp.originalKernel
reflect_kernel logExpSource

private def outputs (k : QKernel) (size : Nat) : Except String (List Symbolic.Expr) := do
  let init : State Symbolic.Expr := {
    init := fun r i => .mk .real (Symbolic.algebra.literal none .real
      (if r == "x" then (i+1 : ℚ)/3 else if r == "y" then 1/7 else -100))
    pids := fun _ => 0, numPids := fun _ => 1
    undef := fun d _ _ => Structural.defaultValue d }
  let some s := interp Symbolic.algebra k init | throw "kernel failed"
  return (List.range size).map fun i => (s.read "out" i).read .real

private def vector := outputs (VectorAdd.Kernels.originalKernel.mirror 2) 2
private def logExp := outputs (logExpSource.mirror "x" "out" 1) 1

-- The shared files spell out the trees independently, including the load and cast tags.
private def matchesFixture (result : Except String (List Symbolic.Expr)) (expected : String) : Bool :=
  match result.bind Symbolic.exportTrees, Lean.Json.parse expected with
  | .ok actual, .ok wanted => actual == wanted
  | _, _ => Bool.false

#guard matchesFixture vector (include_str "../interp/symbolic/vector-add.json")
#guard matchesFixture logExp (include_str "../interp/symbolic/log-exp.json")
end VeriTile.Tests.InterpSymbolic
