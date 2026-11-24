import VeriTile.Interp.Adequacy.Exec

namespace VeriTile.Tests.InterpAdequacyNeg

open VeriTile.Triton VeriTile.Triton.FP VeriTile.Interp

private def subtractKernel (a b : Nat) : QKernel :=
  .mk [] [] [.alg (.assign .nat [] "out" (.sub .nat .nil (.constNat a) (.constNat b)))]

/-- A twin swapping subtraction operands computes 2 - 5 = 0, while the
intended structural program writes 5 - 2 = 3. The exact natural-number fragment is
independent of both the floating-point carrier and the initial state. -/
example {α : Type} [Inhabited α] (M : CAlgebra α) (s : State α) :
    (interp M (subtractKernel 2 5) s).map State.lift ≠
      Structural.exec M.lift (subtractKernel 5 2).toReal s.lift := by
  rw [← interp_eq_structural_exec]
  intro h
  have different := congrArg (fun o : Option (Structural.State α) =>
    o.bind fun t => (t.regs .nat [] "out").map (· PUnit.unit)) h
  simp [subtractKernel, interp, exec, run, step, stepAlg, evalOp, State.lift_setReg,
    Structural.State.setReg, Structural.bop, numeric] at different

end VeriTile.Tests.InterpAdequacyNeg
