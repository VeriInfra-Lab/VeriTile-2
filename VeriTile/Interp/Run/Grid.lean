/-
One to three Triton program-id axes. Axis 0 advances fastest in the chosen
sequential schedule. FP.Structural.runSchedule passes predecessor memory to
each Invocation; Invocation.initial with clearRegisters gives each program
fresh locals (VeriTile/Triton/Float/ProgramIO.lean, lines 51–73).
Grid.toNumPids and GridIndex.toPids specify 1 and 0 outside the launch rank
(VeriTile/Triton/Launch/Grid.lean, lines 36–38 and 66–71).
-/
import VeriTile.Interp.Exec

namespace VeriTile.Interp.Run

def runGrid {α : Type} [Inhabited α] (model : CAlgebra α) (kernel : QKernel)
    (dims : List Nat) (initial : State α) : Option (State α) := do
  guard (dims.length > 0 && dims.length ≤ 3)
  let mut s := initial
  for z in [:dims.getD 2 1] do
    for y in [:dims.getD 1 1] do
      for x in [:dims.getD 0 1] do
        s ← interp model kernel { s with
          regs := initial.regs
          pids := fun | 0 => x | 1 => y | 2 => z | _ => 0
          numPids := fun axis => dims.getD axis 1 }
  return s

end VeriTile.Interp.Run
