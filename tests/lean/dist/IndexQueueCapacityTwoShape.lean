import tests.lean.dist.IndexQueueSingleSlotShape
import tests.lean.dist.IndexQueueCapacityTwoRuns

namespace VeriTile.Tests.G1QueueRefinement.CapacityTwo
open VeriTile.Dist
open DeepEPChannel (sender receiver tail head slot rel acq publishTail loadTail waitRoom)
open VeriTile.Triton (MemCell)

private def puts (n : Nat) : Nat := if 8 < n then 3 else if 1 < n then 2 else if 0 < n then 1 else 0
private def takes (n : Nat) : Nat := if 11 < n then 3 else if 5 < n then 2 else if 4 < n then 1 else 0
private def published (n : Nat) : Option MemCell :=
  if 9 < n then some (.of .nat 3) else if 2 < n then some (.of .nat 2) else none

private theorem silent {x} (q : Dispatch.Noise x) :
    queue.isPut x = false ∧ queue.isTake x = false ∧ IndexQueue.storedAt tail x = none := by
  cases q <;> exact ⟨rfl,rfl,rfl⟩

private theorem stats {n h} (p : Prefix n h) :
    h.countP queue.isPut = puts n ∧ h.countP queue.isTake = takes n ∧
    (h.filterMap (IndexQueue.storedAt tail)).getLast? = published n := by
  induction p with
  | start => exact ⟨rfl,rfl,rfl⟩
  | noise prev quiet ih =>
    obtain ⟨wp,rd,pub⟩ := silent quiet
    simpa [List.countP_append, List.countP_cons, wp, rd, pub] using ih
  | @advance n h prev bound ih =>
    obtain ⟨wp,rd,pub⟩ := ih
    simp only [List.countP_append, List.filterMap_append, List.getLast?_append, wp, rd, pub]
    interval_cases n <;> exact ⟨rfl,rfl,rfl⟩

private theorem slotWrite {n h k i} (p : Prefix n h) (atPut : queue.view.Put h k i) :
    (k = 0 ∧ Prefix 0 (h.take i) ∧ h[i]? = some (milestone 0)) ∨
    (k = 1 ∧ Prefix 1 (h.take i) ∧ h[i]? = some (milestone 1)) ∨
    (k = 2 ∧ Prefix 8 (h.take i) ∧ h[i]? = some (milestone 8)) := by
  obtain ⟨⟨x,hx,tag⟩,count⟩ := atPut
  obtain ⟨m,before,quiet | ⟨lt,rfl⟩⟩ := p.before hx
  · change queue.isPut x = true at tag
    rw [(silent quiet).1] at tag
    contradiction
  · change (h.take i).countP queue.isPut = k at count
    rw [(stats before).1] at count
    have mb : m < 13 := lt_of_lt_of_le lt p.bound
    interval_cases m <;> first | contradiction | exact Or.inl ⟨count.symm,before,hx⟩ |
      exact Or.inr (Or.inl ⟨count.symm,before,hx⟩) | exact Or.inr (Or.inr ⟨count.symm,before,hx⟩)

private theorem slotRead {n h k j} (p : Prefix n h) (atTake : queue.view.Take h k j) :
    (k = 0 ∧ Prefix 4 (h.take j) ∧ h[j]? = some (milestone 4)) ∨
    (k = 1 ∧ Prefix 5 (h.take j) ∧ h[j]? = some (milestone 5)) ∨
    (k = 2 ∧ Prefix 11 (h.take j) ∧ h[j]? = some (milestone 11)) := by
  obtain ⟨⟨x,hx,tag⟩,count⟩ := atTake
  obtain ⟨m,before,quiet | ⟨lt,rfl⟩⟩ := p.before hx
  · change queue.isTake x = true at tag
    rw [(silent quiet).2.1] at tag
    contradiction
  · change (h.take j).countP queue.isTake = k at count
    rw [(stats before).2.1] at count
    have mb : m < 13 := lt_of_lt_of_le lt p.bound
    interval_cases m <;> first | contradiction | exact Or.inl ⟨count.symm,before,hx⟩ |
      exact Or.inr (Or.inl ⟨count.symm,before,hx⟩) | exact Or.inr (Or.inr ⟨count.symm,before,hx⟩)

private theorem alwaysAllowed {m} (bounded : m < 13) : queue.Allowed (milestone m) := by
  interval_cases m <;>
    simp [milestone, IndexQueue.Allowed, put, take, publishTail, ack,
      loadTail, waitRoom, queue, IndexQueue.slotOf, physical, IndexQueue.isSlot, List.finRange_succ, List.finRange_zero]

private theorem releaseValue {m v} (bounded : m < 13)
    (ev : milestone m = .issued sender ⟨sender, .access .store tail rel, .store v⟩) :
    v.readAs .nat = some (puts m) := by
  interval_cases m <;> first | (cases ev <;> rfl) |
    (simp [milestone, put, IndexQueue.slotOf, queue, physical, slot, tail] at ev)

private theorem ackValue {m v} (bounded : m < 13)
    (ev : milestone m = .issued receiver ⟨receiver, .access .store head rel, .store v⟩) :
    v.readAs .nat = some (takes m) := by
  interval_cases m <;> cases ev <;> rfl

/-- All eight queue obligations hold from every zero-counter initial memory. -/
theorem shaped (w : CellWrites) (s : DistState) (ht : (s.cell tail).readAs .nat = some 0)
    (hh : (s.cell head).readAs .nat = some 0) : queue.Shaped (launch 1 w) s := by
  constructor
  · intro sched final run i x p kd mode hx access _
    obtain ⟨n,pr⟩ := runPrefix w s ht hh run
    obtain ⟨m, _, quiet | ⟨lt,rfl⟩⟩ := pr.before hx
    · cases quiet with
      | segment a => cases kd <;> cases mode <;> simp [Occurrence.access] at access
      | poll => exact alwaysAllowed (m := 3) (by decide)
    · exact alwaysAllowed (lt_of_lt_of_le lt pr.bound)
  · intro sched final run k i put
    obtain ⟨_,pr⟩ := runPrefix w s ht hh run
    rcases slotWrite pr put with ⟨rfl,_,ev⟩ | ⟨rfl,_,ev⟩ | ⟨rfl,_,ev⟩ <;> exact ev
  · intro sched final run k j take
    obtain ⟨_,pr⟩ := runPrefix w s ht hh run
    rcases slotRead pr take with ⟨rfl,_,ev⟩ | ⟨rfl,_,ev⟩ | ⟨rfl,_,ev⟩ <;> exact ev
  · intro sched final run k i put reuse
    obtain ⟨_,pr⟩ := runPrefix w s ht hh run
    rcases slotWrite pr put with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ | ⟨rfl,prior,_⟩
    · exact (by decide : ¬ queue.cap ≤ 0).elim reuse
    · exact (by decide : ¬ queue.cap ≤ 1).elim reuse
    · obtain ⟨j,lt,ev,_⟩ := prior.earlier (m := 7) (by decide)
      exact ⟨j, 1, lt, by decide, ev⟩
  · intro sched final run i v hx
    obtain ⟨n,pr⟩ := runPrefix w s ht hh run
    obtain ⟨m,prior,quiet | ⟨lt,ev⟩⟩ := pr.before hx
    · cases quiet
    · exact ⟨puts m, releaseValue (lt_of_lt_of_le lt pr.bound) ev.symm, (stats prior).1.symm⟩
  · intro sched final run k j take
    obtain ⟨_,pr⟩ := runPrefix w s ht hh run
    rcases slotRead pr take with ⟨rfl,prior,_⟩ | ⟨rfl,prior,_⟩ | ⟨rfl,prior,_⟩
    · obtain ⟨i,lt,ev,past⟩ := prior.earlier (m := 3) (by decide)
      have value : (IndexQueue.lastValue s final.history tail i).readAs .nat = some 2 := by
        rw [IndexQueue.lastValue, (stats past).2.2]
        rfl
      exact ⟨i, 2, lt, by decide, value, ev⟩
    · obtain ⟨i,lt,ev,past⟩ := prior.earlier (m := 3) (by decide)
      have value : (IndexQueue.lastValue s final.history tail i).readAs .nat = some 2 := by
        rw [IndexQueue.lastValue, (stats past).2.2]
        rfl
      exact ⟨i, 2, lt, by decide, value, ev⟩
    · obtain ⟨i,lt,ev,past⟩ := prior.earlier (m := 10) (by decide)
      have value : (IndexQueue.lastValue s final.history tail i).readAs .nat = some 3 := by
        rw [IndexQueue.lastValue, (stats past).2.2]
        rfl
      exact ⟨i, 3, lt, by decide, value, ev⟩
  · intro sched final run j v hx
    obtain ⟨n,pr⟩ := runPrefix w s ht hh run
    obtain ⟨m,prior,quiet | ⟨lt,ev⟩⟩ := pr.before hx
    · cases quiet
    · exact ⟨takes m, ackValue (lt_of_lt_of_le lt pr.bound) ev.symm, (stats prior).2.1.symm⟩
  · intro sched final run complete
    exact (stats (completePrefix w s ht hh run complete)).2.1

#print axioms shaped
end VeriTile.Tests.G1QueueRefinement.CapacityTwo
