import tests.lean.dist.IndexQueueSingleSlotModel

namespace VeriTile.Tests.G1QueueRefinement.Dispatch
open VeriTile.Dist
open VeriTile.Tests.DeepEPChannel (sender receiver tail head slot rel acq segOcc writeSlot publishTail
  loadTail waitRoom readSlot)
open VeriTile.Triton (MemCell)

-- Every position has a protocol phase just before it. Repeated unsuccessful polls
-- or empty segments may separate two adjacent milestones by any number of entries.
theorem prefixBefore {n h} (p : Prefix n h) {i : Nat} {x : Occurrence} (hx : h[i]? = some x) :
    ∃ m, Prefix m (h.take i) ∧ (Noise x ∨ (m < n ∧ x = milestone m)) := by
  induction p generalizing i x with
  | start => simp at hx
  | @noise n h y prev quiet ih =>
    by_cases earlier : i < h.length
    · rw [List.getElem?_append_left earlier] at hx
      rw [List.take_append_of_le_length (Nat.le_of_lt earlier)]
      exact ih hx
    · rw [List.getElem?_append_right (by omega)] at hx
      cases d : i - h.length with
      | zero =>
        have hi : i = h.length := by omega
        subst i
        simp at hx
        subst x
        exact ⟨n, by simpa using prev, Or.inl quiet⟩
      | succ k => simp [d] at hx
  | @advance n h prev bound ih =>
    by_cases earlier : i < h.length
    · rw [List.getElem?_append_left earlier] at hx
      rw [List.take_append_of_le_length (Nat.le_of_lt earlier)]
      obtain ⟨m, before, noisy | ⟨lt, eq⟩⟩ := ih hx
      · exact ⟨m, before, Or.inl noisy⟩
      · exact ⟨m, before, Or.inr ⟨by omega, eq⟩⟩
    · rw [List.getElem?_append_right (by omega)] at hx
      cases d : i - h.length with
      | zero =>
        have hi : i = h.length := by omega
        subst i
        simp at hx
        subst x
        exact ⟨n, by simpa using prev, Or.inr ⟨by omega, rfl⟩⟩
      | succ k => simp [d] at hx

/-- Retrieve a particular milestone, even when identical poll events also arise as noise. -/
theorem prefixLocate {n h} (p : Prefix n h) {m : Nat} (hm : m < n) :
    ∃ i, i < h.length ∧ h[i]? = some (milestone m) ∧ Prefix m (h.take i) := by
  induction p with
  | start => omega
  | @noise n h y prev quiet ih =>
    obtain ⟨i, hi, hx, before⟩ := ih hm
    exact ⟨i, by simp; omega, by rwa [List.getElem?_append_left hi],
      by rwa [List.take_append_of_le_length (Nat.le_of_lt hi)]⟩
  | @advance n h prev bound ih =>
    by_cases last : m = n
    · subst m
      exact ⟨h.length, by simp, by simp, by simpa using prev⟩
    · obtain ⟨i, hi, hx, before⟩ := ih (by omega)
      exact ⟨i, by simp; omega, by rwa [List.getElem?_append_left hi],
        by rwa [List.take_append_of_le_length (Nat.le_of_lt hi)]⟩

theorem prefixBound {n h} (p : Prefix n h) : n ≤ 11 := by
  induction p with
  | start => decide
  | noise _ _ ih => exact ih
  | advance _ bound _ => omega

private theorem phaseCases {n : Nat} (bound : n < 11) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨
    n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 := by omega

private abbrev queue := Q1 rel
private def puts (n : Nat) : Nat := if 6 < n then 2 else if 0 < n then 1 else 0
private def takes (n : Nat) : Nat := if 9 < n then 2 else if 3 < n then 1 else 0
private def published (n : Nat) : Option MemCell :=
  if 7 < n then some (.of .nat 2) else if 1 < n then some (.of .nat 1) else none

private theorem silent {x} (q : Noise x) :
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
    rcases phaseCases (n := n) (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl,rfl,rfl⟩

/-- The two-token sender never puts a third item, including on incomplete schedules. -/
theorem prefix_put_bound {n h} (p : Prefix n h) : h.countP (Q1 rel).isPut ≤ (Q1 rel).items := by
  rw [(stats p).1]
  change (if 6 < n then 2 else if 0 < n then 1 else 0) ≤ 2
  split_ifs <;> decide

private theorem slotWrite {n h k i} (p : Prefix n h) (atPut : queue.view.Put h k i) :
    (k = 0 ∧ Prefix 0 (h.take i) ∧ h[i]? = some (milestone 0)) ∨
    (k = 1 ∧ Prefix 6 (h.take i) ∧ h[i]? = some (milestone 6)) := by
  obtain ⟨⟨x,hx,tag⟩,count⟩ := atPut
  obtain ⟨m,before,quiet | ⟨lt,rfl⟩⟩ := prefixBefore p hx
  · change queue.isPut x = true at tag
    rw [(silent quiet).1] at tag
    contradiction
  · change (h.take i).countP queue.isPut = k at count
    rw [(stats before).1] at count
    have := prefixBound p
    rcases phaseCases (n := m) (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | exact Or.inl ⟨count.symm,before,hx⟩ |
      exact Or.inr ⟨count.symm,before,hx⟩

private theorem slotRead {n h k j} (p : Prefix n h) (atTake : queue.view.Take h k j) :
    (k = 0 ∧ Prefix 3 (h.take j) ∧ h[j]? = some (milestone 3)) ∨
    (k = 1 ∧ Prefix 9 (h.take j) ∧ h[j]? = some (milestone 9)) := by
  obtain ⟨⟨x,hx,tag⟩,count⟩ := atTake
  obtain ⟨m,before,quiet | ⟨lt,rfl⟩⟩ := prefixBefore p hx
  · change queue.isTake x = true at tag
    rw [(silent quiet).2.1] at tag
    contradiction
  · change (h.take j).countP queue.isTake = k at count
    rw [(stats before).2.1] at count
    have := prefixBound p
    rcases phaseCases (n := m) (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | exact Or.inl ⟨count.symm,before,hx⟩ |
      exact Or.inr ⟨count.symm,before,hx⟩

private theorem alwaysAllowed {m} (bounded : m < 11) : queue.Allowed (milestone m) := by
  rcases phaseCases (n := m) (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [milestone, IndexQueue.Allowed, writeSlot, readSlot, publishTail, storeHead,
      loadTail, waitRoom, Q1, IndexQueue.isSlot, List.finRange_succ, List.finRange_zero]

private theorem releaseValue {m v} (bounded : m < 11)
    (ev : milestone m = .issued sender ⟨sender, .access .store tail rel, .store v⟩) :
    v.readAs .nat = some (puts m) := by
  rcases phaseCases (n := m) (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | (cases ev <;> rfl) |
    (simp [milestone, writeSlot, slot, tail] at ev)

private theorem ackValue {m v} (bounded : m < 11)
    (ev : milestone m = .issued receiver ⟨receiver, .access .store head rel, .store v⟩) :
    v.readAs .nat = some (takes m) := by
  rcases phaseCases (n := m) (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases ev <;> rfl

private theorem earlierMilestone {phase j m : Nat} {h : History} (before : Prefix phase (h.take j)) (hm : m < phase) :
    ∃ i, i < j ∧ h[i]? = some (milestone m) ∧ Prefix m (h.take i) := by
  obtain ⟨i,hi,hx,past⟩ := prefixLocate before hm
  have earlier : i < j := by simp only [List.length_take] at hi; omega
  rw [List.getElem?_take_of_lt earlier] at hx
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt earlier)] at past
  exact ⟨i, earlier, hx, past⟩

/-- These are precisely the eight shape fields. Reachability supplies the prefix
phase, and completion rules out stopping before the second acknowledgement. -/
theorem shaped_of_prefix {w : CellWrites} {s : DistState}
    (reachable : ∀ sched final, Run (launch rel w) ((launch rel w).initial s) sched final →
      ∃ n, Prefix n final.history)
    (finished : ∀ sched final, Run (launch rel w) ((launch rel w).initial s) sched final →
      Complete final → Prefix 11 final.history) : (Q1 rel).Shaped (launch rel w) s := by
  constructor
  · intro sched final run i x p kd mode hx access _
    obtain ⟨n,pr⟩ := reachable sched final run
    obtain ⟨m, _, quiet | ⟨lt,rfl⟩⟩ := prefixBefore pr hx
    · cases quiet with
      | segment a => cases kd <;> cases mode <;> simp [Occurrence.access] at access
      | poll => exact alwaysAllowed (m := 2) (by decide)
    · exact alwaysAllowed (lt_of_lt_of_le lt (prefixBound pr))
  · intro sched final run k i put
    obtain ⟨_,pr⟩ := reachable sched final run
    rcases slotWrite pr put with ⟨rfl,_,ev⟩ | ⟨rfl,_,ev⟩ <;> exact ev
  · intro sched final run k j take
    obtain ⟨_,pr⟩ := reachable sched final run
    rcases slotRead pr take with ⟨rfl,_,ev⟩ | ⟨rfl,_,ev⟩ <;> exact ev
  · intro sched final run k i put reuse
    obtain ⟨_,pr⟩ := reachable sched final run
    rcases slotWrite pr put with ⟨rfl,_,_⟩ | ⟨rfl,prior,_⟩
    · exact (by decide : ¬ queue.cap ≤ 0).elim reuse
    · obtain ⟨j,lt,ev,_⟩ := earlierMilestone prior (m := 5) (by decide)
      exact ⟨j, 1, lt, by decide, ev⟩
  · intro sched final run i v hx
    obtain ⟨n,pr⟩ := reachable sched final run
    obtain ⟨m,prior,quiet | ⟨lt,ev⟩⟩ := prefixBefore pr hx
    · cases quiet
    · exact ⟨puts m, releaseValue (lt_of_lt_of_le lt (prefixBound pr)) ev.symm, (stats prior).1.symm⟩
  · intro sched final run k j take
    obtain ⟨_,pr⟩ := reachable sched final run
    rcases slotRead pr take with ⟨rfl,prior,_⟩ | ⟨rfl,prior,_⟩
    · obtain ⟨i,lt,ev,past⟩ := earlierMilestone prior (m := 2) (by decide)
      have value : (IndexQueue.lastValue s final.history tail i).readAs .nat = some 1 := by
        rw [IndexQueue.lastValue, (stats past).2.2]
        rfl
      exact ⟨i, 1, lt, by decide, value, ev⟩
    · obtain ⟨i,lt,ev,past⟩ := earlierMilestone prior (m := 8) (by decide)
      have value : (IndexQueue.lastValue s final.history tail i).readAs .nat = some 2 := by
        rw [IndexQueue.lastValue, (stats past).2.2]
        rfl
      exact ⟨i, 2, lt, by decide, value, ev⟩
  · intro sched final run j v hx
    obtain ⟨n,pr⟩ := reachable sched final run
    obtain ⟨m,prior,quiet | ⟨lt,ev⟩⟩ := prefixBefore pr hx
    · cases quiet
    · exact ⟨takes m, ackValue (lt_of_lt_of_le lt (prefixBound pr)) ev.symm, (stats prior).2.1.symm⟩
  · intro sched final run complete
    exact (stats (finished sched final run complete)).2.1

#print axioms shaped_of_prefix
end VeriTile.Tests.G1QueueRefinement.Dispatch
