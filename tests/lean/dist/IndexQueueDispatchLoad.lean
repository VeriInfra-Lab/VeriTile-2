import tests.lean.dist.IndexQueueSingleSlot
import tests.lean.dist.IndexQueueCellValues

/-! Link the single-slot history theorem to the physical cell and the
value supplied to the receiver continuation on every enabled data load. -/
namespace VeriTile.Tests.G1QueueRefinement.Dispatch.LoadClient
open VeriTile.Dist
open VeriTile.Triton (MemCell)
open VeriTile.Tests.DeepEPChannel (PC receiver tail head slot rel readSlot emptySegment)
open VeriTile.Tests.IndexQueueCellValues
private def Known (x : Occurrence) : Prop :=
  StoreOrSegment slot x ∧ ∀ v i, writeAt slot v i x = IndexQueue.storedAt slot x

private theorem allKnown (pr : Prefix n h) : ∀ x ∈ h, Known x := by
  induction pr with
  | start => simp
  | @noise n h x pr noise ih =>
    have one : Known x := by
      cases noise with
      | segment => exact ⟨trivial, fun v i => by classical simp [writeAt, IndexQueue.storedAt]⟩
      | poll => exact ⟨trivial, fun _ _ => rfl⟩
    intro y hy
    rcases List.mem_append.mp hy with past | last
    · exact ih y past
    · simpa only [List.mem_singleton.mp last] using one
  | @advance n h pr small ih =>
    have one : Known (milestone n) := by
      interval_cases n <;> exact ⟨trivial, fun _ _ => rfl⟩
    intro y hy
    rcases List.mem_append.mp hy with past | last
    · exact ih y past
    · simpa only [List.mem_singleton.mp last] using one

private theorem foldStores (ok : ∀ x ∈ h, Known x) (v : Nat → MemCell) (i : Nat) (seed : MemCell) :
    lastWrite slot v i seed h = ((h.filterMap (IndexQueue.storedAt slot)).getLast?).getD seed := by
  induction h generalizing i seed with
  | nil => rfl
  | cons x xs ih =>
    rw [lastWrite, (ok x (by simp)).2 v i, ih (fun y hy => ok y (by simp [hy]))]
    cases hx : IndexQueue.storedAt slot x with
    | none => simp [hx]
    | some a =>
      simp [hx, List.getLast?_cons]

/-- The slot in every reachable machine contains the last data store at that prefix. -/
theorem actualMemory (w : CellWrites) (s : DistState)
    (ht : (s.cell tail).readAs .nat = some 0) (hh : (s.cell head).readAs .nat = some 0)
    (r : Run (launch rel w) ((launch rel w).initial s) sched c) :
    c.mem.cell slot = IndexQueue.lastValue s c.history slot c.history.length := by
  obtain ⟨n, pr⟩ := runPrefix w s ht hh r
  let val := fun (_ : Nat) => s.cell slot
  have frame : CellFrame (launch rel w) slot := by
    intro a pc before after ran _
    have eq : some before = some after := ran
    cases eq; rfl
  have writes : SegmentValues (launch rel w) s slot val := by
    intro _ _ _ a pc after _ _ inside
    exact False.elim inside
  rw [memory_eq_lastWrite r frame writes (fun x hx => (allKnown pr x hx).1),
      foldStores (allKnown pr)]
  simp [IndexQueue.lastValue]

/-- At any enabled receiver data load, the actual value returned by the
scheduler equals the payload of this take. Its generation is computed from
the preceding history. No assumed target history or matched value is needed. -/
theorem actualLoad (w : CellWrites) (s : DistState)
    (ht : (s.cell tail).readAs .nat = some 0) (hh : (s.cell head).readAs .nat = some 0)
    (before : Run (launch rel w) ((launch rel w).initial s) sched c)
    (waiting : c.pc receiver = some (.waiting (readSlot receiver) [] k))
    (fires : FireGroup (launch rel w) receiver c.toMachine [readSlot receiver] out values) :
    values = [some ((Q1 rel).payload (c.history.countP (Q1 rel).isTake))] := by
  have owned : ∀ x ∈ [readSlot receiver], x.actor.within receiver := by
    intro x hx; obtain rfl := List.mem_singleton.mp hx; exact DeepEPChannel.own _
  have stepRead := step.fire waiting owned fires
  have extended := DeepEPChannel.appendRuns before (.cons stepRead (.nil _))
  cases fires with
  | cons access free ordered fire rest =>
    cases rest
    cases fire
    have tak : (Q1 rel).view.Take (c.history ++ [.issued receiver (readSlot receiver)])
        (c.history.countP (Q1 rel).isTake) c.history.length := by
      constructor
      · exact ⟨.issued receiver (readSlot receiver), by simp, rfl⟩
      · simp [IndexQueue.view]
    have data := Dispatch.takeValue w s ht hh extended tak
    change IndexQueue.lastValue s (c.history ++ [_]) slot c.history.length = _ at data
    rw [← data, actualMemory w s ht hh before]
    simp [IndexQueue.lastValue]
#print axioms actualMemory
#print axioms actualLoad
end VeriTile.Tests.G1QueueRefinement.Dispatch.LoadClient
