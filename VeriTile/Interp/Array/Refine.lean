import VeriTile.Interp.Array.Exec
import VeriTile.Interp.Adequacy.Exec

/-! Array memory and the hash-map interpreter store writes differently.
The array view incorporates writes into its initial reader. Lifting both
results exposes the same registers, memory reads, program ids and undefined
values, and lets refinement compose with structural execution adequacy. -/

namespace VeriTile.Interp.Array

open VeriTile.Triton VeriTile.Triton.FP
open Structural (Values)

variable {α : Type}

private theorem get_product {β γ : Type} (xs : List β) (ys : List γ)
    (i j : Nat) (hi : i < xs.length) (hj : j < ys.length) :
    (xs.flatMap fun x => ys.map (x, ·))[i * ys.length + j]? = some (xs[i], ys[j]) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp [List.flatMap_cons, List.getElem?_append_left (by simpa using hj : j < (ys.map (x, ·)).length),
        List.getElem?_eq_getElem hj]
    | succ i =>
      simp only [List.flatMap_cons, Nat.succ_mul, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by simp; omega), List.length_map]
      convert ih i (by simpa using hi) using 2; omega

private theorem get_allIndices (sh : TileShape) (i : TileIndex sh) :
    (TileShape.allIndices sh)[TileShape.linearIndex sh i]? = some i := by
  induction sh with
  | nil => cases i; rfl
  | cons n sh ih =>
    rcases i with ⟨x, y⟩
    have hy := TileShape.linearIndex_lt sh y
    have he := get_product (List.finRange n) (TileShape.allIndices sh) x.val
      (TileShape.linearIndex sh y) (by simp) (by simpa using hy)
    simpa [TileShape.allIndices_cons, TileShape.linearIndex, List.getElem_finRange,
      (List.getElem?_eq_some_iff.mp (ih y)).2] using he

/-- Tabulation returns the original value at each index, including rank-zero tiles. -/
theorem materialize_eq {β : Type} {sh : TileShape} (f : TileIndex sh → β) : materialize f = f := by
  funext i
  simp [materialize, (List.getElem?_eq_some_iff.mp (get_allIndices sh i)).2]

private theorem read_present (m : Memory α) (r : RegionName) (o : Nat) (initial)
    {j : Nat} (h : m.slots[(r, o)]? = some j) :
    m.read r o initial = m.cells[j]'(m.bounded h) := by
  unfold Memory.read
  split
  next k hk => cases Option.some.inj (hk.symm.trans h); rfl
  next hk => simp_all

private theorem read_absent (m : Memory α) (r : RegionName) (o : Nat) (initial)
    (h : m.slots[(r, o)]? = none) : m.read r o initial = initial r o := by
  unfold Memory.read
  split <;> simp_all

private theorem read_write (m : Memory α) (a : RegionName × Nat) (c : Structural.Cell α)
    (r : RegionName) (o : Nat) (initial : RegionName → Nat → Structural.Cell α) :
    (m.write a c).read r o initial = if (r, o) = a then c else m.read r o initial := by
  unfold Memory.write
  split
  next j had =>
    by_cases same : (r, o) = a
    · subst a
      rw [if_pos rfl]
      refine (read_present _ r o initial (j := j) ?_).trans ?_
      · exact had
      · simp
    · rw [if_neg same]
      cases atKey : m.slots[(r, o)]? with
      | none =>
        rw [read_absent m _ _ _ atKey]
        apply read_absent
        exact atKey
      | some k =>
        have hk : j ≠ k := by rintro rfl; exact same (m.unique atKey had)
        rw [read_present m _ _ _ atKey]
        refine (read_present _ r o initial (j := k) ?_).trans ?_
        · exact atKey
        · simp [Array.getElem_set, hk]
  next had =>
    by_cases same : (r, o) = a
    · subst a
      rw [if_pos rfl, read_present _ _ _ _ (j := m.cells.size) (by simp)]
      simp
    · rw [if_neg same]
      have lookup : (m.slots.insert a m.cells.size)[(r, o)]? = m.slots[(r, o)]? := by
        simp [Std.HashMap.getElem?_insert, Ne.symm same]
      cases atKey : m.slots[(r, o)]? with
      | none => rw [read_absent _ _ _ _ (lookup.trans atKey), read_absent _ _ _ _ atKey]
      | some k =>
        rw [read_present _ _ _ _ (lookup.trans atKey), read_present _ _ _ _ atKey]
        exact Array.getElem_push_lt (m.bounded atKey)

private abbrev lift (s : State α) := s.view.lift

private theorem view_read (s : State α) (r : RegionName) (o : Nat) :
    s.view.read r o = s.read r o := by simp [State.view, Interp.State.read]

private theorem lift_setReg (s : State α) (n : RegName) (d : TileDType) (sh : TileShape)
    (v : Values α d sh) : lift (s.setReg n d sh v) = (lift s).setReg n d sh v := by
  rw [← Interp.State.lift_setReg]
  simp [lift, State.view, State.setReg, Interp.State.setReg, materialize_eq]
  rfl

private theorem lift_write (s : State α) (a : RegionName × Nat) (c : Structural.Cell α) :
    lift (s.write a c) = (lift s).write a.1 a.2 c := by
  rcases a with ⟨r, o⟩
  unfold lift Interp.State.lift Structural.State.write
  congr 1
  funext r' o'
  simp [State.view, State.read, State.write, Interp.State.read, read_write]

open private Array.scatter Array.store Array.atomicAdd Array.stepAlg from VeriTile.Interp.Array.Exec

variable [Inhabited α]

-- Moving the read view through the lane fold preserves the state returned by every
-- earlier lane, including a preceding update at the same address.
local macro "refineLaneFold" : tactic =>
  `(tactic| (
    repeat first | refine congrArg (Option.bind _) (funext fun _ => ?_) | apply congrArg some
    apply (List.foldl_hom lift ?_).symm
    intro t i
    dsimp
    try split_ifs
    all_goals try simp_all [lift_write, view_read]))

private theorem store_refines (M : CAlgebra α) (s : State α) (mem : QMemAccess d sh)
    (mask : QMaskOpt d sh) (v : Values α d sh) :
    (Array.store M s mem mask v).map lift =
      Structural.store M.lift mem.toReal mask.toReal v (lift s) := by
  cases mem <;> cases mask <;>
    simp only [Array.store, Array.scatter, Structural.store, QMemAccess.toReal, QMaskOpt.toReal, evalOp_eq,
      Option.bind_eq_bind, Option.pure_def, Option.map_bind, Option.map_some, Option.bind_some,
      Option.bind_map, Function.comp_def]
  all_goals refineLaneFold

private theorem atomicAdd_refines (M : CAlgebra α) (s : State α) (nd : NumericDType d)
    (mem : QMemAccess d sh) (mask : QMaskOpt d sh) (v : Values α d sh) :
    (Array.atomicAdd M s nd mem mask v).map lift =
      Structural.atomicAdd M.lift nd mem.toReal mask.toReal v (lift s) := by
  cases mem <;> cases mask <;>
    simp only [Array.atomicAdd, Array.scatter, Structural.atomicAdd, Interp.atomicAddition_eq,
      QMemAccess.toReal, QMaskOpt.toReal, evalOp_eq, Option.bind_eq_bind, Option.pure_def,
      Option.map_bind, Option.map_some, Option.bind_some, Option.bind_map, Function.comp_def]
  all_goals refineLaneFold

private theorem stepAlg_refines (M : CAlgebra α) (st : QAlgStmt) (s : State α) :
    (Array.stepAlg M st s).map lift = Structural.stepAlg M.lift st.toReal (lift s) := by
  cases st <;> simp only [Array.stepAlg, QAlgStmt.toReal, Structural.stepAlg, evalOp_eq,
    Option.bind_eq_bind, Option.pure_def, Option.map_some, Option.map_bind, Option.map_none,
    Function.comp_def, lift_setReg, store_refines, atomicAdd_refines]

omit [Inhabited α] in
private theorem bind_refines {x : Option (State α)} {y : Option (Structural.State α)}
    {f : State α → Option (State α)} {g : Structural.State α → Option (Structural.State α)}
    (hx : x.map lift = y) (hf : ∀ t, (f t).map lift = g (lift t)) :
    (x.bind f).map lift = y.bind g := by
  subst y
  cases x with
  | none => rfl
  | some t => exact hf t


mutual

private theorem step_refines (M : CAlgebra α) (st : QStmt) (s : State α) :
    (step M st s).map lift = Structural.step M.lift st.toReal (lift s) := by
  cases st with
  | alg st => simpa only [step, Structural.step, QStmt.toReal] using stepAlg_refines M st s
  | assign | store | atomicAdd | atomicRMW =>
    simp only [step, QStmt.toReal, Structural.step, evalExpr_eq, Option.bind_eq_bind,
      Option.pure_def, Option.map_bind, Function.comp_def, Option.map_some, Option.map_none,
      lift_setReg, store_refines, atomicAdd_refines]
  | forLoop idx n body =>
    simpa only [step, QStmt.toReal, Structural.step] using loop_refines M idx 0 n body s
  | forRange idx start stop stride body =>
    simpa only [step, QStmt.toReal, Structural.step] using range_refines M idx start stop stride body s
  | forRangeDyn idx a b d body =>
    simp only [step, QStmt.toReal, Structural.step, evalOp_eq, Option.bind_eq_bind,
      Option.map_bind, Function.comp_def, range_refines M idx _ _ _ body]
  | forRangeInt idx a b d body =>
    simp only [step, QStmt.toReal, Structural.step, evalOp_eq, Option.bind_eq_bind,
      Option.map_bind, Function.comp_def, rangeInt_refines M idx _ _ _ body]
  | ifThen cond body =>
    simp only [step, QStmt.toReal, Structural.step, evalOp_eq, Option.bind_eq_bind,
      Option.map_bind, Function.comp_def, apply_ite (Option.map lift),
      run_refines M body, Option.map_some]
  | ifThenElse cond yes no =>
    simp only [step, QStmt.toReal, Structural.step, evalOp_eq, Option.bind_eq_bind,
      Option.map_bind, Function.comp_def, apply_ite (Option.map lift), run_refines M yes, run_refines M no]
  | effectMarker marker =>
    by_cases h : marker = "tl.debug_barrier"
    · subst marker; simp [step, Structural.step, QStmt.toReal]
    · simp [step, Structural.step, QStmt.toReal, h]
termination_by (sizeOf st, 0)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have : 0 < sizeOf idx := by cases idx; simp); omega

private theorem run_refines (M : CAlgebra α) (code : List QStmt) (s : State α) :
    (run M code s).map lift = Structural.run M.lift (QStmt.toRealList code) (lift s) := by
  cases code with
  | nil => simp only [run, QStmt.toRealList, Structural.run, Option.map_some]
  | cons st rest =>
    simp only [run, QStmt.toRealList, Structural.run, Option.bind_eq_bind]
    exact bind_refines (step_refines M st s) (run_refines M rest)
termination_by (sizeOf code, 0)
decreasing_by all_goals (simp_wf; omega)

private theorem loop_refines (M : CAlgebra α) (idx : RegName) (start stop : Nat) (body : List QStmt)
    (s : State α) : (loop M idx start stop body s).map lift =
      Structural.loop M.lift idx start stop (QStmt.toRealList body) (lift s) := by
  rw [loop, Structural.loop]
  split
  · rw [← lift_setReg]
    exact bind_refines (run_refines M body _) (loop_refines M idx (start + 1) stop body)
  · rfl
termination_by (sizeOf body + 1, stop - start)
decreasing_by all_goals omega

private theorem range_refines (M : CAlgebra α) (idx : RegName) (cur stop stride : Nat) (body : List QStmt)
    (s : State α) : (range M idx cur stop stride body s).map lift =
      Structural.range M.lift idx cur stop stride (QStmt.toRealList body) (lift s) := by
  rw [range, Structural.range]
  split
  · rfl
  · split
    · rw [← lift_setReg]
      exact bind_refines (run_refines M body _) (range_refines M idx (cur + stride) stop stride body)
    · rfl
termination_by (sizeOf body + 1, stop - cur)
decreasing_by all_goals omega

private theorem rangeInt_refines (M : CAlgebra α) (idx : RegName) (cur stop : Int) (stride : Nat)
    (body : List QStmt) (s : State α) : (rangeInt M idx cur stop stride body s).map lift =
      Structural.rangeInt M.lift idx cur stop stride (QStmt.toRealList body) (lift s) := by
  rw [rangeInt, Structural.rangeInt]
  split
  · rfl
  · split
    · rw [← lift_setReg]
      exact bind_refines (run_refines M body _) (rangeInt_refines M idx (cur + stride) stop stride body)
    · rfl
termination_by (sizeOf body + 1, (stop - cur).toNat)
decreasing_by all_goals omega

end

/-- Array and hash-map executions fail together or return the same observable structural state. -/
theorem interp_refines (M : CAlgebra α) (kq : QKernel) (s : State α) :
    (Array.interp M kq s).map (fun t => t.view.lift) =
      (Interp.interp M kq s.view).map Interp.State.lift := by
  rw [Interp.interp_eq_structural_exec]
  cases kq with
  | mk _ _ code => exact run_refines M code s

private def storeSeven : QKernel :=
  .mk [] [] [.alg (.store .nat [] (.region "out" (.constNat 0)) (.constNat 7) .none)]

/-- After storing 7, `interp_refines` gives equal observable states. Comparing the
representations directly fails: their hash-map patch counts are zero and one. -/
example (M : CAlgebra α) (s : State α) :
    (Array.interp M storeSeven s).map State.view ≠ Interp.interp M storeSeven s.view := by
  intro h
  have sizes := congrArg (Option.map fun t : Interp.State α => t.cells.size) h
  simp [storeSeven, Array.interp, Array.run, Array.step, Array.stepAlg, Array.store, Array.scatter,
    Interp.interp, Interp.exec, Interp.run, Interp.step, Interp.stepAlg, Interp.store,
    Interp.State.scatter, Interp.State.write, State.view, Interp.evalOp, Std.HashMap.size_insert] at sizes

end VeriTile.Interp.Array
