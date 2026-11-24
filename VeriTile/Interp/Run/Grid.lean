/-
One to three Triton program-id axes. FP.Structural.runSchedule passes predecessor memory to
each Invocation; Invocation.initial with clearRegisters gives each program
fresh locals (VeriTile/Triton/Float/ProgramIO.lean, lines 51–73).
Grid.toNumPids and GridIndex.toPids specify 1 and 0 outside the launch rank
(VeriTile/Triton/Launch/Grid.lean, lines 36–38 and 66–71).
-/
import VeriTile.Interp.Exec

namespace VeriTile.Interp.Run

/-- Launch in Triton v3.5.1 interpreter order: x outermost, y next, z innermost.
See [GridExecutor](https://github.com/triton-lang/triton/blob/0add68262ab0a2e33b84524346cb27cbb2787356/python/triton/runtime/interpreter.py#L1278-L1281).
Each program receives the preceding memory state and the initial registers. -/
def runGrid {α : Type} [Inhabited α] (model : CAlgebra α) (kernel : QKernel)
    (dims : List Nat) (initial : State α) : Option (State α) := do
  guard (dims.length > 0 && dims.length ≤ 3)
  let mut s := initial
  for x in [:dims.getD 0 1] do
    for y in [:dims.getD 1 1] do
      for z in [:dims.getD 2 1] do
        s ← interp model kernel { s with
          regs := initial.regs
          pids := fun | 0 => x | 1 => y | 2 => z | _ => 0
          numPids := fun i => dims.getD i 1 }
  return s

end VeriTile.Interp.Run
