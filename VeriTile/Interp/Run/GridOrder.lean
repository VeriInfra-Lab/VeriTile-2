import VeriTile.Interp.Run.Grid
import VeriTile.Interp.Adequacy.Exec
import VeriTile.Triton.Float.ProgramIO

namespace VeriTile.Interp.Run

/-- Grid coordinates for a launch of rank one to three, in the sequential
Triton interpreter order. Missing axes have extent one. -/
def launchOrder (dims : List Nat) : List (Nat × Nat × Nat) :=
  (List.range (dims.getD 0 1)).flatMap fun x =>
    (List.range (dims.getD 1 1)).flatMap fun y =>
      (List.range (dims.getD 2 1)).map fun z => (x, y, z)

/-- One launch step starts with the initial registers and the memory returned
by the previous program. Axes above z have program ID zero. -/
def interpAt {α : Type} [Inhabited α] (model : CAlgebra α) (kernel : QKernel)
    (dims : List Nat) (initial s : State α) (idx : Nat × Nat × Nat) : Option (State α) :=
  interp model kernel { s with
    regs := initial.regs
    pids := fun | 0 => idx.1 | 1 => idx.2.1 | 2 => idx.2.2 | _ => 0
    numPids := fun i => dims.getD i 1 }

private theorem foldlM_flatMap {α β γ : Type} (xs : List α) (f : α → List β)
    (step : γ → β → Option γ) (s : γ) :
    (xs.flatMap f).foldlM step s = xs.foldlM (fun t x => (f x).foldlM step t) s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [List.foldlM_append, ih, List.foldlM_cons]

private theorem forIn_yield {α β : Type} (xs : List α) (s : β) (step : β → α → Option β) :
    forIn xs s (fun x t => (step t x).bind fun v => some (.yield v)) = xs.foldlM step s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    cases h : step s x <;> simp [List.forIn_cons, List.foldlM_cons, h, ih]

/-- A valid launch executes its index list left to right, stopping at the
first failed program. A zero extent produces an empty list. -/
theorem runGrid_eq_foldlM {α : Type} [Inhabited α] (model : CAlgebra α) (kernel : QKernel)
    (dims : List Nat) (initial : State α) (rank : 0 < dims.length ∧ dims.length ≤ 3) :
    runGrid model kernel dims initial =
      (launchOrder dims).foldlM (interpAt model kernel dims initial) initial := by
  simp [runGrid, launchOrder, interpAt, rank.1, rank.2, foldlM_flatMap, List.foldlM_map,
    Std.Legacy.Range.size, ← List.range_eq_range', forIn_yield] <;> rfl

open VeriTile.Triton
open VeriTile.Triton.FP

private def binding {α : Type} (entry : RegName × Reg α) : Structural.RegisterBinding α :=
  ⟨entry.1, entry.2.dtype, entry.2.shape, entry.2.values⟩

/-- Reinstall the initial ABI registers on every upstream invocation, including
on launches with nonempty entry registers. -/
noncomputable def invocationAt {α : Type} [Inhabited α] (model : CAlgebra α)
    (kernel : QKernel) (dims : List Nat) (initial : State α) (idx : Nat × Nat × Nat) :
    Structural.Invocation α where
  kernel := kernel.toReal
  backend := model.lift
  arguments := initial.regs.toList.map binding
  clearRegisters := true
  pids := fun | 0 => idx.1 | 1 => idx.2.1 | 2 => idx.2.2 | _ => 0
  numPids := some (fun i => dims.getD i 1)

private theorem bind_lift {α : Type} (entries : List (RegName × Reg α)) (s : State α) :
    Structural.bindRegisters (entries.map binding) s.lift =
      ({ s with regs := entries.foldl (fun regs e => regs.insert e.1 e.2) s.regs } : State α).lift := by
  induction entries generalizing s with
  | nil => rfl
  | cons e es ih =>
    change Structural.bindRegisters (es.map binding)
      (s.lift.setReg e.1 e.2.dtype e.2.shape e.2.values) = _
    rw [← State.lift_setReg, ih]
    rfl

private theorem restored_lookup {α : Type} (s : State α) (name : RegName) :
    (s.regs.toList.foldl (fun (regs : Std.HashMap RegName (Reg α)) e => regs.insert e.1 e.2) ∅)[name]? =
      s.regs[name]? := by
  rw [← Std.HashMap.ofList_equiv_foldl.getElem?_eq]
  cases h : s.regs[name]? with
  | none =>
    apply Std.HashMap.getElem?_ofList_of_contains_eq_false
    simp [Std.HashMap.map_fst_toList_eq_keys, Std.HashMap.mem_iff_isSome_getElem?, h]
  | some v =>
    exact Std.HashMap.getElem?_ofList_of_mem (by simp) s.regs.distinct_keys_toList
      (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h)

private theorem invocationAt_run {α : Type} [Inhabited α] (model : CAlgebra α)
    (kernel : QKernel) (dims : List Nat) (initial s : State α) (idx : Nat × Nat × Nat) :
    ((interpAt model kernel dims initial s idx).map State.lift) =
      (invocationAt model kernel dims initial idx).run s.lift := by
  rw [interpAt, interp_eq_structural_exec]
  congr 1
  let base : State α := { s with
    regs := ∅
    pids := fun | 0 => idx.1 | 1 => idx.2.1 | 2 => idx.2.2 | _ => 0
    numPids := fun i => dims.getD i 1 }
  let cleared : Structural.State α := { s.lift with
    regs := fun _ _ _ => none
    pids := base.pids
    numPids := base.numPids }
  have clear : cleared = base.lift := by
    simp [cleared, base, State.lift]
    refine ⟨rfl, ?_⟩
    funext d sh n
    simp [State.getReg]
  change _ = Structural.bindRegisters (initial.regs.toList.map binding) cleared
  rw [clear, bind_lift]
  unfold State.lift
  congr 1
  funext d sh n
  simp only [State.getReg, base, restored_lookup]

/-- Lifting the final executable state gives exactly the upstream structural
schedule for the same coordinates and initial register bindings. -/
theorem runGrid_eq_runSchedule {α : Type} [Inhabited α] (model : CAlgebra α) (kernel : QKernel)
    (dims : List Nat) (initial : State α) (rank : 0 < dims.length ∧ dims.length ≤ 3) :
    (runGrid model kernel dims initial).map State.lift =
      Structural.runSchedule ((launchOrder dims).map (invocationAt model kernel dims initial)) initial.lift := by
  rw [runGrid_eq_foldlM model kernel dims initial rank]
  suffices ∀ (indices : List (Nat × Nat × Nat)) (s : State α),
      (indices.foldlM (interpAt model kernel dims initial) s).map State.lift =
        Structural.runSchedule (indices.map (invocationAt model kernel dims initial)) s.lift from
    this _ _
  intro indices
  induction indices with
  | nil => intro s; rfl
  | cons idx rest ih =>
    intro s
    simp only [List.foldlM_cons, List.map_cons, Structural.runSchedule,
      ← invocationAt_run]
    cases h : interpAt model kernel dims initial s idx with
    | none => rfl
    | some t => exact ih t

end VeriTile.Interp.Run
