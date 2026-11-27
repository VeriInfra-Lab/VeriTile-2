/-
VeriTile.Dist.Event.Transfer

Pattern (c) of the Dist event interface (ticket S2.5): asynchronous
transfers. Frozen by ticket S2.1 in `VeriTile/Staging/Dist/EventSpec.lean`
and moved here with proofs, under the same names and types. The `Transfer`
type itself already lives in `VeriTile/Dist/Event.lean` (forced by `Event`
in S2.3).
-/
import VeriTile.Dist.Event.Counter

namespace VeriTile.Dist

/-! ## Pattern (c): asynchronous transfer (S2.5) -/

/-- Owner: S2.5 (#41). How often the transfer `t` has
been initiated in `tr` and has not completed yet. -/
def Transfer.pending (t : Transfer) (tr : Trace) : Nat :=
  tr.countP (fun x => x.2 = .initiate t) - tr.countP (fun x => x.2 = .complete t)

/-- Owner: S2.5 (#41). After `tr` the cell `p` is the destination of
a transfer that has not completed: it holds unspecified data, and the
execution semantics rejects an access to it. -/
def InFlight (tr : Trace) (p : Addr) : Prop :=
  ∃ t : Transfer, 0 < t.pending tr ∧ p ∈ t.dst

/-- Signed. Proved by S2.5 (#41). The destination of a transfer that was
initiated and has not completed is in flight. This covers a transfer that
never completes (W5) and a non-blocking put without `quiet`. -/
theorem inFlight_of_initiate {tr : Trace} {a : Agent} {t : Transfer} {p : Addr}
    (hi : (a, Event.initiate t) ∈ tr) (hc : ∀ x ∈ tr, x.2 ≠ Event.complete t)
    (hp : p ∈ t.dst) : InFlight tr p := by
  refine ⟨t, ?_, hp⟩
  have hcomp : tr.countP (fun x => x.2 = .complete t) = 0 := by
    rw [List.countP_eq_zero]
    intro x hx
    simpa using hc x hx
  have hinit : 0 < tr.countP (fun x => x.2 = .initiate t) := by
    rw [List.countP_pos_iff]
    exact ⟨(a, .initiate t), hi, by simp⟩
  simpa [Transfer.pending, hcomp] using hinit

/-- Signed. Proved by S2.5 (#41). The completion of a transfer conflicts
with every access to a destination cell, whatever the mode of that access. -/
theorem conflict_complete {a : Agent} {t : Transfer} {y : Agent × Event} {kind : AccessKind}
    {p : Addr} {mode : Mode} (hp : p ∈ t.dst) (hy : (kind, p, mode) ∈ y.2.accesses) :
    Conflict (a, Event.complete t) y := by
  have hx : (AccessKind.store, p, Mode.plain) ∈ (Event.complete t).accesses := by
    simp only [Event.accesses]
    exact List.mem_append_left _ <| List.mem_append_left _ <| List.mem_map_of_mem hp
  exact conflict_of_plain hx hy (Or.inl rfl)

/-- Signed. Proved by S2.5 (#41). The only edge out of a completion goes
through the counter that the transfer is bound to. -/
theorem SyncEdge.of_complete {reach : ShmemReach} {p : Addr} {a : Agent} {t : Transfer}
    {y : Agent × Event} (h : SyncEdge reach p (a, Event.complete t) y) :
    ∃ b m, t.completion = some b ∧ y.2.acquireOf? = some (b.counter, m) := by
  obtain ⟨c, m, m', hr, ha, _⟩ := h
  cases hc : t.completion with
  | none =>
    simp [Event.releaseOf?, hc] at hr
  | some b =>
    simp [Event.releaseOf?, hc] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨b, m', rfl, ha⟩

private def nbiPut (region : VeriTile.Triton.RegionName) : Transfer :=
  ⟨[], [⟨.global 0, region, 0⟩], true,
    some ⟨.delivered (.rank 0), .add, 1, .atomic .sys .release⟩⟩

/-- Negative example of S2.5: a non-blocking put without `quiet` leaves the
destination in flight, and a load of that cell conflicts with the completion. -/
example (region : VeriTile.Triton.RegionName) :
    InFlight [(.rank 0, .initiate (nbiPut region))] ⟨.global 0, region, 0⟩ ∧
      Conflict (.rank 0, .complete (nbiPut region))
        (.rank 0, .access .load ⟨.global 0, region, 0⟩ .plain) := by
  refine ⟨?_, ?_⟩
  · refine inFlight_of_initiate (a := .rank 0) (t := nbiPut region)
      (p := ⟨.global 0, region, 0⟩) (List.mem_singleton.2 rfl) ?_
      (List.mem_singleton.2 rfl)
    intro x hx
    have hx' : x = (.rank 0, .initiate (nbiPut region)) := List.mem_singleton.1 hx
    subst hx'
    intro h
    cases h
  · exact conflict_complete (t := nbiPut region) (List.mem_singleton.2 rfl)
      (List.mem_singleton.2 rfl)

/-- Negative example of S2.5: with the completion and a wait on its counter,
the necessary conditions of an edge hold. -/
example (region : VeriTile.Triton.RegionName) :
    SyncEdge .global ⟨.global 0, region, 0⟩
      (.rank 0, .complete (nbiPut region))
      (.rank 0, .wait (.delivered (.rank 0)) .ge 1 (.atomic .sys .acquire)) ∧
    ∃ b m, (nbiPut region).completion = some b ∧
      Event.acquireOf? (.wait (.delivered (.rank 0)) .ge 1 (.atomic .sys .acquire)) =
        some (b.counter, m) := by
  have hedge :
      SyncEdge .global ⟨.global 0, region, 0⟩
        (.rank 0, .complete (nbiPut region))
        (.rank 0, .wait (.delivered (.rank 0)) .ge 1 (.atomic .sys .acquire)) :=
    ⟨.delivered (.rank 0), .atomic .sys .release, .atomic .sys .acquire,
      by simp [nbiPut, Event.releaseOf?], by simp [Event.acquireOf?],
      by simp [Mode.Pairs, MemOrder.releases, MemOrder.acquires, Scope.covers]⟩
  exact ⟨hedge, SyncEdge.of_complete hedge⟩

/-- Tutorial 07 as written (inference I6): the plain store of the host's
`set_signal` conflicts with the `dl.wait` of the kernel on the same word. -/
example (p : Addr) (host waiter : Agent) :
    Conflict (host, .bump ⟨.word p, .set, 1, .plain⟩)
      (waiter, .wait (.word p) .ge 1 (.atomic .gpu .acquire)) :=
  ⟨.store, .load, p, .plain, .atomic .gpu .acquire,
    by simp [Event.accesses, Bump.accesses, SignalOp.kind], by simp [Event.accesses],
    Or.inl rfl, by simp [Mode.AtomicFor]⟩

end VeriTile.Dist
