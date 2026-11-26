import tests.lean.dist.IndexQueueSingleSlotShape

/-! Handoff and reuse in every prefix of the release-head dispatch program. -/
namespace VeriTile.Tests.G1QueueRefinement.Dispatch
open VeriTile.Dist
open VeriTile.Tests.DeepEPChannel (sender receiver tail head slot rel acq
  loadTail waitRoom publishTail writeSlot readSlot)

private structure At (h : History) (m i : Nat) : Prop where
  occurrence : h[i]? = some (milestone m)
  before : Prefix m (h.take i)

private theorem At.earlier {h m i} (atM : At h m i) {b} (lt : b < m) :
    ∃ j, j < i ∧ At h b j := by
  obtain ⟨j, bound, event, before⟩ := prefixLocate atM.before lt
  have smaller : j < i := by simp only [List.length_take] at bound; omega
  refine ⟨j, smaller, ?_, ?_⟩
  · rwa [List.getElem?_take_of_lt smaller] at event
  · simpa [List.take_take, Nat.min_eq_left smaller.le] using before

private def phaseCount (f : Occurrence → Bool) (m : Nat) :=
  ((List.range m).map milestone).countP f

private theorem countPhases {m h} (st : Prefix m h) (f : Occurrence → Bool)
    (quiet : ∀ x, Noise x → f x = false) : h.countP f = phaseCount f m := by
  induction st with
  | start => rfl
  | noise pre hx ih => simp [quiet _ hx, ih]
  | advance pre bound ih => simp [phaseCount, List.range_succ] at ih ⊢; exact ih

private def writesAt (p : Addr) : Occurrence → Bool
  | .issued _ e => e.event.accesses.any fun (k,q,_) => k.writes && q == p
  | _ => false

private theorem noiseWrites (p : Addr) (x) (hx : Noise x) : writesAt p x = false := by
  cases hx <;> rfl

private theorem accessWrites {n h} {i : Nat} {x : Occurrence} (pre : Prefix n h) (atX : h[i]? = some x)
    {p kd md} (acc : x.access p kd md) (write : kd.writes = true) : writesAt p x = true := by
  obtain ⟨m, _, quiet | ⟨lt, rfl⟩⟩ := prefixBefore pre atX
  · cases quiet with
    | segment a => cases kd <;> cases md <;> simp_all [Occurrence.access]
    | poll => simp [Occurrence.access, loadTail, Event.accesses] at acc; simp_all [AccessKind.writes]
  · have issued : ∃ a e, milestone m = .issued a e := by
      have b := prefixBound pre
      have upper : m < 11 := by omega
      interval_cases m <;> exact ⟨_, _, rfl⟩
    obtain ⟨a, e, eq⟩ := issued
    rw [eq] at acc ⊢
    exact List.any_eq_true.mpr ⟨(kd,p,md), acc, by simp [write]⟩

private theorem countStep {h : History} {i x} (atX : h[i]? = some x)
    (f : Occurrence → Bool) (yes : f x = true) :
    (h.take (i+1)).countP f = (h.take i).countP f + 1 := by
  obtain ⟨lt, eq⟩ := List.getElem?_eq_some_iff.mp atX
  simp [List.take_succ_eq_append_getElem lt, eq, yes]

/-- Counting all writes to the specified physical word rules out an intervening write.
Empty segments and retry polls do not contribute to this count. -/
private theorem unchangedBetween {n h a b i j} (pre : Prefix n h)
    (first : At h a i) (last : At h b j) (p : Addr)
    (wrote : writesAt p (milestone a) = true)
    (counts : phaseCount (writesAt p) a + 1 = phaseCount (writesAt p) b) :
    NoWriteBetween h p i j := by
  intro k x lo hi actual kd md acc
  by_contra wrong
  have yes : kd.writes = true := by simpa using wrong
  let f := writesAt p
  have ci := countPhases first.before f (noiseWrites p)
  have cj := countPhases last.before f (noiseWrites p)
  have incI := countStep first.occurrence f wrote
  have incK := countStep actual f (accessWrites pre actual acc yes)
  have le₁ := (List.take_prefix_take_left (l := h) (i := i+1) (j := k) lo).countP_le (p := f)
  have le₂ := (List.take_prefix_take_left (l := h) (i := k+1) (j := j) hi).countP_le (p := f)
  change phaseCount f a + 1 = phaseCount f b at counts
  omega

private theorem po {h w a b i j} (first : At h a i) (last : At h b j) (lt : i < j)
    (same : ∃ who, (milestone a).program? = some who ∧ (milestone b).program? = some who) :
    HB (launch rel w) h slot i j :=
  .single ⟨_, _, first.occurrence, last.occurrence, lt, Or.inl same⟩

private theorem synchronize {h w a b i j} (first : At h a i) (last : At h b j) (lt : i < j)
    (p : Addr) (noWrite : NoWriteBetween h p i j) {release acquire : Agent × Event}
    (r : (milestone a).event? = some release) (q : (milestone b).event? = some acquire)
    (src : release.2.releaseOf? = some (.word p, rel))
    (dst : acquire.2.acquireOf? = some (.word p, acq)) :
    HB (launch rel w) h slot i j := by
  have pair : Mode.Pairs (launch rel w).reach slot release.1 acquire.1 rel acq := by
    simp [Mode.Pairs, rel, acq, Scope.covers, MemOrder.releases, MemOrder.acquires]
  exact SyncEdge.hb_of_readsFrom ⟨_, _, _, src, dst, pair⟩
    (by simpa [first.occurrence] using r) (by simpa [last.occurrence] using q)
    src ⟨lt, noWrite⟩


private theorem quietPut (x) (q : Noise x) : (Q1 rel).isPut x = false := by
  cases q <;> rfl
private theorem quietTake (x) (q : Noise x) : (Q1 rel).isTake x = false := by
  cases q <;> rfl

private theorem atNth {h m i} (atM : At h m i) (f : Occurrence → Bool)
    (quiet : ∀ x, Noise x → f x = false)
    (yes : f (milestone m) = true) : NthAt f h (phaseCount f m) i :=
  ⟨⟨_, atM.occurrence, yes⟩, countPhases atM.before _ quiet⟩

private theorem classifyNth {n h f i k} (pre : Prefix n h)
    (nth : NthAt f h k i) (quiet : ∀ x, Noise x → f x = false) :
    ∃ m, m < 11 ∧ At h m i ∧ f (milestone m) = true ∧ k = phaseCount f m := by
  obtain ⟨⟨x, hx, yes⟩, count⟩ := nth
  obtain ⟨m, before, noise | ⟨lt, rfl⟩⟩ := prefixBefore pre hx
  · rw [quiet _ noise] at yes
    contradiction
  · exact ⟨m, Nat.lt_of_lt_of_le lt (prefixBound pre), ⟨hx,before⟩, yes,
      count.symm.trans (countPhases before _ quiet)⟩

/-- The three edges witnessing handoff are producer program order, the release/acquire
pair on the tail word, and receiver program order. The slot is protected throughout. -/
private theorem handoff {n h w first last j} (pre : Prefix n h) (atRead : At h last j)
    (distance : first + 3 = last)
    (programs : (milestone first).program? = some sender ∧
      (milestone (first+1)).program? = some sender ∧
      (milestone (first+2)).program? = some receiver ∧ (milestone last).program? = some receiver)
    (publication : (milestone (first+1)).event? = some (sender, .access .store tail rel))
    (poll : (milestone (first+2)).event? = some (receiver, .access .load tail acq))
    (writes : writesAt slot (milestone first) = true ∧ writesAt tail (milestone (first+1)) = true)
    (countSlot : phaseCount (writesAt slot) first + 1 = phaseCount (writesAt slot) last)
    (countTail : phaseCount (writesAt tail) (first+1) + 1 = phaseCount (writesAt tail) (first+2)) :
    ∃ i, At h first i ∧ i < j ∧ NoWriteBetween h slot i j ∧ HB (launch rel w) h slot i j := by
  obtain ⟨pollPos, pr, atPoll⟩ := atRead.earlier (b := first+2) (by omega)
  obtain ⟨pubPos, pp, atPub⟩ := atPoll.earlier (b := first+1) (by omega)
  obtain ⟨i, ip, atPut⟩ := atPub.earlier (b := first) (by omega)
  have e1 := po (w := w) atPut atPub ip ⟨_, programs.1, programs.2.1⟩
  have e2 := synchronize (w := w) atPub atPoll pp tail
    (unchangedBetween pre atPub atPoll tail writes.2 countTail) publication poll rfl rfl
  have e3 := po (w := w) atPoll atRead pr ⟨_, programs.2.2.1, programs.2.2.2⟩
  exact ⟨i, atPut, by omega, unchangedBetween pre atPut atRead slot writes.1 countSlot,
    (e1.trans e2).trans e3⟩

/-- The first read, release of head 1, acquire room wait and second write form the
release-head reuse chain. Intervening empty segments and retry polls are allowed. -/
private theorem reuse {n h w i} (pre : Prefix n h) (put : At h 6 i) :
    ∃ j, At h 3 j ∧ j < i ∧ HB (launch rel w) h slot j i := by
  obtain ⟨roomPos, rw', room⟩ := put.earlier (b := 5) (by decide)
  obtain ⟨ackPos, ar, ack⟩ := room.earlier (b := 4) (by decide)
  obtain ⟨j, ja, take⟩ := ack.earlier (b := 3) (by decide)
  have e1 := po (w := w) take ack ja ⟨receiver, rfl, rfl⟩
  have e2 := synchronize (w := w) ack room ar head
    (unchangedBetween pre ack room head (by decide) (by decide))
    (release := (receiver, .access .store head rel)) (acquire := (sender, .wait (.word head) .ge 1 acq))
    rfl rfl rfl rfl
  have e3 := po (w := w) room put rw' ⟨sender, rfl, rfl⟩
  exact ⟨j, take, by omega, (e1.trans e2).trans e3⟩

/-- Both token handoffs and the reuse of the only slot hold on all prefixes. -/
theorem prefixRefines {n h} (pre : Prefix n h) (w : CellWrites) :
    (∀ k j, (Q1 rel).view.Take h k j → ∃ i, (Q1 rel).view.Put h k i ∧ i < j ∧
      NoWriteBetween h slot i j ∧ HB (launch rel w) h slot i j) ∧
    (∀ k i, (Q1 rel).view.Put h (k + 1) i → ∃ j, (Q1 rel).view.Take h k j ∧ j < i ∧
      HB (launch rel w) h slot j i) := by
  constructor
  · intro k j taken
    obtain ⟨m, bound, here, yes, ord⟩ := classifyNth pre taken quietTake
    have which : m = 3 ∨ m = 9 := by
      interval_cases m <;> first | decide | contradiction
    rcases which with rfl | rfl
    · obtain ⟨i, wr, lt, clear, hb⟩ := handoff (w := w) (first := 0) pre here
        rfl ⟨rfl,rfl,rfl,rfl⟩ rfl rfl ⟨rfl,rfl⟩ (by decide) (by decide)
      subst k
      exact ⟨i, atNth wr _ quietPut rfl, lt, clear, hb⟩
    · obtain ⟨i, wr, lt, clear, hb⟩ := handoff (w := w) (first := 6) pre here
        rfl ⟨rfl,rfl,rfl,rfl⟩ rfl rfl ⟨rfl,rfl⟩ (by decide) (by decide)
      subst k
      exact ⟨i, atNth wr _ quietPut rfl, lt, clear, hb⟩
  · intro k i put
    obtain ⟨m, bound, here, yes, ord⟩ := classifyNth pre put quietPut
    have which : m = 0 ∨ m = 6 := by
      interval_cases m <;> first | decide | contradiction
    rcases which with rfl | rfl
    · change k + 1 = 0 at ord
      omega
    · change k + 1 = 1 at ord
      obtain rfl : k = 0 := by omega
      obtain ⟨j, rd, lt, hb⟩ := reuse (w := w) pre here
      exact ⟨j, atNth rd _ quietTake rfl, lt, hb⟩

private theorem slotStores {m h} (pre : Prefix m h) :
    h.filterMap (IndexQueue.storedAt slot) =
      ((List.range m).map milestone).filterMap (IndexQueue.storedAt slot) := by
  induction pre with
  | start => rfl
  | @noise _ _ x before q ih =>
    have noStore : IndexQueue.storedAt slot x = none := by cases q <;> rfl
    simp [noStore, ih]
  | advance before bound ih => simp [List.range_succ, ih]

/-- Immediately before either take, the last store to the reused physical cell
carries that take's token. This value is independent of the initial slot cell. -/
theorem takeLastStore {n h k j} (pre : Prefix n h) (s : DistState)
    (taken : (Q1 rel).view.Take h k j) :
    IndexQueue.lastValue s h slot j = (Q1 rel).payload k := by
  obtain ⟨m, bound, here, yes, ord⟩ := classifyNth pre taken quietTake
  have which : m = 3 ∨ m = 9 := by
    interval_cases m <;> first | decide | contradiction
  unfold IndexQueue.lastValue
  rw [slotStores here.before, ord]
  rcases which with rfl | rfl <;> rfl

#print axioms prefixRefines
#print axioms takeLastStore

end VeriTile.Tests.G1QueueRefinement.Dispatch
