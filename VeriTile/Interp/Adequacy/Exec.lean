/- Execution adequacy for the computable interpreter (I3.3). -/
import VeriTile.Interp.Adequacy.EvalOp
import VeriTile.Interp.Exec

namespace VeriTile.Interp

open VeriTile.Triton
open VeriTile.Triton.FP
open Structural (Values)

variable {α : Type} [Inhabited α]

theorem store_eq (M : CAlgebra α) (mem : QMemAccess d sh) (mask : QMaskOpt d sh)
    (values : Values α d sh) (s : State α) : (store M mem mask values s).map State.lift =
      Structural.store M.lift mem.toReal mask.toReal values s.lift := by
  cases mem <;> cases mask <;>
    simp only [QMemAccess.toReal, QMaskOpt.toReal, store, Structural.store, evalOp_eq,
      Option.bind_eq_bind, Option.pure_def, Option.map_bind, Option.map_some,
      Option.bind_some, Function.comp_def, State.lift_scatter]

omit [Inhabited α] in
theorem atomicAddition_eq (M : CAlgebra α) (nd : NumericDType d) :
    atomicAddition M nd = Structural.atomicAddition M.lift nd := by cases nd <;> rfl

theorem atomicAdd_eq (M : CAlgebra α) (nd : NumericDType d) (mem : QMemAccess d sh)
    (mask : QMaskOpt d sh) (values : Values α d sh) (s : State α) :
    (atomicAdd M nd mem mask values s).map State.lift =
      Structural.atomicAdd M.lift nd mem.toReal mask.toReal values s.lift := by
  cases mem <;> cases mask <;>
    simp only [QMemAccess.toReal, QMaskOpt.toReal, atomicAdd, Structural.atomicAdd,
      atomicAddition_eq, evalOp_eq, Option.bind_eq_bind, Option.pure_def,
      Option.map_bind, Option.map_some, Option.bind_some, Function.comp_def, State.lift_scatter]

theorem stepAlg_eq (M : CAlgebra α) (st : QAlgStmt) (s : State α) :
    (stepAlg M st s).map State.lift = Structural.stepAlg M.lift st.toReal s.lift := by
  cases st <;> simp only [stepAlg, QAlgStmt.toReal, Structural.stepAlg, evalOp_eq,
    Option.bind_eq_bind, Option.pure_def, Option.map_some, Option.map_bind, Option.map_none,
    Function.comp_def, State.lift_setReg, store_eq, atomicAdd_eq]

omit [Inhabited α] in
/-- Sequence a computation whose successful states are related by lift. -/
private theorem bind_lift {x : Option (State α)} {up : Option (Structural.State α)}
    {f : State α → Option (State α)} {g : Structural.State α → Option (Structural.State α)}
    (hx : x.map State.lift = up) (hf : ∀ t, (f t).map State.lift = g t.lift) :
    (x.bind f).map State.lift = up.bind g := by
  subst up
  cases x with
  | none => rfl
  | some t => exact hf t

mutual

theorem step_eq (M : CAlgebra α) (st : QStmt) (s : State α) :
    (step M st s).map State.lift = Structural.step M.lift st.toReal s.lift := by
  cases st with
  | alg st => simpa only [step, Structural.step, QStmt.toReal] using stepAlg_eq M st s
  | assign | store | atomicAdd | atomicRMW =>
    simp only [step, QStmt.toReal, Structural.step, evalExpr_eq, Option.bind_eq_bind,
      Option.pure_def, Option.map_bind, Function.comp_def, Option.map_some, Option.map_none,
      State.lift_setReg, store_eq, atomicAdd_eq]
  | forLoop idx n body =>
    simpa only [step, QStmt.toReal, Structural.step] using loop_eq M idx 0 n body s
  | forRange idx start stop stride body =>
    simpa only [step, QStmt.toReal, Structural.step] using range_eq M idx start stop stride body s
  | forRangeDyn idx a b d body =>
    simp only [step, QStmt.toReal, Structural.step, evalOp_eq, Option.bind_eq_bind,
      Option.map_bind, Function.comp_def, range_eq M idx _ _ _ body]
  | forRangeInt idx a b d body =>
    simp only [step, QStmt.toReal, Structural.step, evalOp_eq, Option.bind_eq_bind,
      Option.map_bind, Function.comp_def, rangeInt_eq M idx _ _ _ body]
  | ifThen cond body =>
    simp only [step, QStmt.toReal, Structural.step, evalOp_eq, Option.bind_eq_bind,
      Option.map_bind, Function.comp_def, apply_ite (Option.map State.lift),
      run_eq M body, Option.map_some]
  | ifThenElse cond yes no =>
    simp only [step, QStmt.toReal, Structural.step, evalOp_eq, Option.bind_eq_bind,
      Option.map_bind, Function.comp_def, apply_ite (Option.map State.lift), run_eq M yes, run_eq M no]
  | effectMarker marker =>
    by_cases h : marker = "tl.debug_barrier"
    · subst marker; simp [step, Structural.step, QStmt.toReal]
    · simp [step, Structural.step, QStmt.toReal, h]
termination_by (sizeOf st, 0)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have : 0 < sizeOf idx := by cases idx; simp); omega

theorem run_eq (M : CAlgebra α) (code : List QStmt) (s : State α) :
    (run M code s).map State.lift = Structural.run M.lift (QStmt.toRealList code) s.lift := by
  cases code with
  | nil => simp only [run, QStmt.toRealList, Structural.run, Option.map_some]
  | cons st rest =>
    simp only [run, QStmt.toRealList, Structural.run, Option.bind_eq_bind]
    exact bind_lift (step_eq M st s) (run_eq M rest)
termination_by (sizeOf code, 0)
decreasing_by all_goals (simp_wf; omega)

theorem loop_eq (M : CAlgebra α) (idx : RegName) (start stop : Nat) (body : List QStmt)
    (s : State α) : (loop M idx start stop body s).map State.lift =
      Structural.loop M.lift idx start stop (QStmt.toRealList body) s.lift := by
  rw [loop, Structural.loop]
  split
  · rw [← State.lift_setReg]
    exact bind_lift (run_eq M body _) (loop_eq M idx (start + 1) stop body)
  · rfl
termination_by (sizeOf body + 1, stop - start)
decreasing_by all_goals omega

theorem range_eq (M : CAlgebra α) (idx : RegName) (cur stop stride : Nat) (body : List QStmt)
    (s : State α) : (range M idx cur stop stride body s).map State.lift =
      Structural.range M.lift idx cur stop stride (QStmt.toRealList body) s.lift := by
  rw [range, Structural.range]
  split
  · rfl
  · split
    · rw [← State.lift_setReg]
      exact bind_lift (run_eq M body _) (range_eq M idx (cur + stride) stop stride body)
    · rfl
termination_by (sizeOf body + 1, stop - cur)
decreasing_by all_goals omega

theorem rangeInt_eq (M : CAlgebra α) (idx : RegName) (cur stop : Int) (stride : Nat)
    (body : List QStmt) (s : State α) : (rangeInt M idx cur stop stride body s).map State.lift =
      Structural.rangeInt M.lift idx cur stop stride (QStmt.toRealList body) s.lift := by
  rw [rangeInt, Structural.rangeInt]
  split
  · rfl
  · split
    · rw [← State.lift_setReg]
      exact bind_lift (run_eq M body _) (rangeInt_eq M idx (cur + stride) stop stride body)
    · rfl
termination_by (sizeOf body + 1, (stop - cur).toNat)
decreasing_by all_goals omega

end

theorem exec_eq (M : CAlgebra α) (kq : QKernel) (s : State α) :
    (exec M kq s).map State.lift = Structural.exec M.lift kq.toReal s.lift := by
  cases kq with
  | mk _ _ body => exact run_eq M body s

/-- For every carrier and every algebra, the interpreter and the
structural execution fail together or succeed with the same final state. -/
theorem interp_eq_structural_exec {α : Type} [Inhabited α]
    (M : CAlgebra α) (kq : QKernel) (s : State α) :
    (interp M kq s).map State.lift = Structural.exec M.lift kq.toReal s.lift :=
  exec_eq M kq s

theorem interp_eq_of_reflected (M : CAlgebra α) (kq : QKernel) (k : ComputeKernel)
    (hk : kq.toReal = k) (s : State α) :
    (interp M kq s).map State.lift = Structural.exec M.lift k s.lift :=
  hk ▸ interp_eq_structural_exec M kq s

/-- Even an empty kernel distinguishes an initial structural state other than
the lift when the differing field is observed in the output. -/
example (M : CAlgebra α) (s : State α) (t : Structural.State α) (h : s.lift ≠ t) :
    (interp M (.mk [] [] []) s).map State.lift ≠ Structural.exec M.lift (.mk [] [] []) t := by
  simpa only [interp, exec, run, Structural.exec, Structural.run, Option.map_some, ne_eq,
    Option.some.injEq] using h

end VeriTile.Interp
