import tests.lean.dist.IndexQueueSingleSlot

/-! #651. Derive race freedom of every queue slot from the hand-off and reuse
edges at arbitrary capacity. Specialize it to the release-head dispatch. -/
namespace VeriTile.Tests.G1QueueRefinement
open VeriTile.Dist

/-- The ordinary DataRace predicate specialized to a single physical cell. -/
def RaceOn (l : Launch P) (h : History) (p : Addr) : Prop :=
  ∃ i j x y kd kd' m m', i < j ∧ h[i]? = some x ∧ h[j]? = some y ∧
    x.access p kd m ∧ y.access p kd' m' ∧ (kd.writes = true ∨ kd'.writes = true) ∧
    ¬ Mode.AtomicFor x.owner y.owner m m' ∧ ¬ HB l h p i j

/-- Every access to a slot belongs to a put or a read-only take on that cell. -/
def SlotOnly (l : Launch P) (s : DistState) (V : QueueView) : Prop :=
  ∀ sched final, Run l (l.initial s) sched final → ∀ (i : Nat) x p kd m n,
    final.history[i]? = some x → x.access p kd m → p = V.slotOf n →
      ∃ k, V.slotOf k = p ∧ (V.Put final.history k i ∨ (V.Take final.history k i ∧ kd.writes = false))

/-- The count at the later of two matching events includes the earlier one. -/
private theorem nth_increases {f h k k' i j} (first : NthAt f h k i) (second : NthAt f h k' j)
    (lt : i < j) : k < k' := by
  obtain ⟨⟨x, hx, yes⟩, ci⟩ := first
  obtain ⟨_, cj⟩ := second
  obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp hx
  have count : (h.take (i+1)).countP f = k + 1 := by
    simp [List.take_succ_eq_append_getElem bound, eq, yes, ci]
  have le := (List.take_prefix_take_left (l := h) (i := i+1) (j := j) lt).countP_le (p := f)
  omega

private theorem nth_unique (a : NthAt f h k i) (b : NthAt f h k j) : i = j := by
  rcases lt_trichotomy i j with lt | eq | gt
  · exact False.elim ((Nat.lt_irrefl k) (nth_increases a b lt))
  · exact eq
  · exact False.elim ((Nat.lt_irrefl k) (nth_increases b a gt))

/-- The even positions of one slot's life cycle are its puts; the odd positions are its takes. -/
private def SlotMark (V : QueueView) (h : History) (base phase i : Nat) : Prop :=
  let item := base + (phase / 2) * V.cap
  if phase % 2 = 0 then V.Put h item i else V.Take h item i

private theorem sameSlot {V : QueueView} (periodic : ∀ k, V.slotOf (k + V.cap) = V.slotOf k) (base turns : Nat) :
    V.slotOf (base + turns * V.cap) = V.slotOf base := by
  induction turns with
  | zero => simp
  | succ n ih => simpa [Nat.succ_mul, ← Nat.add_assoc] using (periodic (base + n * V.cap)).trans ih

private theorem slotPred (refines : QueueRefines l s V)
    (periodic : ∀ k, V.slotOf (k + V.cap) = V.slotOf k)
    (run : Run l (l.initial s) sched c) (next : SlotMark V c.history base (n+1) j) :
    ∃ i, SlotMark V c.history base n i ∧ i < j ∧ HB l c.history (V.slotOf base) i j := by
  obtain ⟨handoff, reuse⟩ := refines _ _ run
  by_cases even : n % 2 = 0
  · have odd : (n+1) % 2 ≠ 0 := by omega
    have half : (n+1)/2 = n/2 := by omega
    simp only [SlotMark, odd, if_false, half] at next
    obtain ⟨i, put, lt, _, hb⟩ := handoff _ _ next
    exact ⟨i, by simpa [SlotMark, even] using put, lt, by simpa [sameSlot periodic] using hb⟩
  · have even' : (n+1) % 2 = 0 := by omega
    have half : (n+1)/2 = n/2+1 := by omega
    simp only [SlotMark, even', if_true, half, Nat.succ_mul, ← Nat.add_assoc] at next
    obtain ⟨i, take, lt, hb⟩ := reuse _ _ next
    exact ⟨i, by simpa [SlotMark, even] using take, lt, by simpa [sameSlot periodic] using hb⟩

private theorem mark_unique (a : SlotMark V h base n i) (b : SlotMark V h base n j) : i = j := by
  by_cases even : n % 2 = 0 <;> simp [SlotMark, even] at a b <;> exact nth_unique a b

private theorem orderedMarks (refines : QueueRefines l s V)
    (periodic : ∀ k, V.slotOf (k + V.cap) = V.slotOf k) (r : Run l (l.initial s) sched c)
    {base a b i j} (first : SlotMark V c.history base a i) (last : SlotMark V c.history base b j)
    (lt : a < b) : i < j ∧ HB l c.history (V.slotOf base) i j := by
  induction b generalizing j with
  | zero => omega
  | succ b ih =>
    obtain ⟨k, middle, before, edge⟩ := slotPred refines periodic r last
    by_cases eq : a = b
    · subst a
      obtain rfl := mark_unique first middle
      exact ⟨before, edge⟩
    · have ⟨earlier, chain⟩ := ih middle (by omega)
      exact ⟨Nat.lt_trans earlier before, chain.trans edge⟩

theorem QueueRefines.slot_race_free (refines : QueueRefines l s V) (onlySlots : SlotOnly l s V)
    (periodic : ∀ k, V.slotOf (k + V.cap) = V.slotOf k)
    (separate : ∀ a b, V.slotOf a = V.slotOf b → a % V.cap = b % V.cap) :
    ∀ sched final, Run l (l.initial s) sched final → ∀ k, ¬ RaceOn l final.history (V.slotOf k) := by
  intro sched c run k race
  obtain ⟨i,j,x,y,kd,kd',m,m',ij,hx,hy,ax,ay,_,_,unordered⟩ := race
  have mark {p o ak mode} (atO : c.history[p]? = some o) (access : o.access (V.slotOf k) ak mode) :
      ∃ phase, SlotMark V c.history (k % V.cap) phase p := by
    obtain ⟨t, same, event⟩ := onlySlots _ _ run p o _ ak mode k atO access rfl
    have base := separate _ _ same
    have idx : k % V.cap + t / V.cap * V.cap = t := by rw [← base, Nat.mul_comm, Nat.mod_add_div]
    rcases event with put | ⟨take,_⟩
    · exact ⟨2 * (t / V.cap), by simpa [SlotMark, idx] using put⟩
    · exact ⟨2 * (t / V.cap) + 1, by simpa [SlotMark, idx, Nat.add_div] using take⟩
  obtain ⟨a, first⟩ := mark hx ax
  obtain ⟨b, last⟩ := mark hy ay
  have p : V.slotOf k = V.slotOf (k % V.cap) := by
    conv => lhs; rw [← Nat.mod_add_div k V.cap]
    simpa [Nat.mul_comm] using sameSlot periodic (k % V.cap) (k / V.cap)
  rcases lt_trichotomy a b with lt | eq | gt
  · exact unordered (p ▸ (orderedMarks refines periodic run first last lt).2)
  · subst b; exact (Nat.ne_of_lt ij) (mark_unique first last)
  · exact (Nat.not_lt_of_ge (Nat.le_of_lt ij)) (orderedMarks refines periodic run last first gt).1

/-- The queue's source-shape conditions account for every physical slot access. -/
theorem IndexQueue.Shaped.slotOnly {Q : IndexQueue} (shape : Q.Shaped l s) : SlotOnly l s Q.view := by
  intro cs c run i x p kd m n hx access addr
  subst p
  let pos : Fin Q.cap := ⟨n % Q.cap, Nat.mod_lt _ Q.cap_pos⟩
  have isSlot : Q.isSlot (Q.view.slotOf n) = true :=
    List.any_eq_true.mpr ⟨pos, List.mem_finRange _, beq_self_eq_true _⟩
  have allowed := shape.cells _ _ run _ _ _ _ _ hx access (Or.inr (Or.inr isSlot))
  have nt : Q.view.slotOf n ≠ Q.tail := Q.slot_ne_tail pos
  have nh : Q.view.slotOf n ≠ Q.head := Q.slot_ne_head pos
  cases x with
  | segment | delivered => exact False.elim allowed
  | issued a e =>
    rcases e with ⟨b, event, data⟩
    rcases allowed with ⟨rfl, ⟨rfl, send⟩ | ⟨rfl, recv⟩⟩
    · rcases send with rfl | ⟨t,rfl⟩ | ⟨q, qs, rfl⟩
      · simp [Occurrence.access, Event.accesses, nt] at access
      · simp [Occurrence.access, Event.accesses, nh] at access
      · simp [Occurrence.access, Event.accesses] at access
        obtain ⟨rfl, rfl, rfl⟩ := access
        change Q.isSlot (Q.slotOf n) = true at qs
        let token := (c.history.take i).countP Q.isPut
        have put : Q.view.Put c.history token i := ⟨⟨_, hx, by simp [IndexQueue.view, IndexQueue.isPut, qs]⟩, rfl⟩
        have actual := shape.putSlot _ _ run _ _ put
        rw [hx] at actual
        exact ⟨token, by simp at actual; exact actual.1.symm, Or.inl put⟩
    · rcases recv with rfl | rfl | ⟨q, qs, rfl⟩
      · simp [Occurrence.access, Event.accesses, nt] at access
      · simp [Occurrence.access, Event.accesses, nh] at access
      · simp [Occurrence.access, Event.accesses] at access
        obtain ⟨rfl, rfl, rfl⟩ := access
        change Q.isSlot (Q.slotOf n) = true at qs
        let token := (c.history.take i).countP Q.isTake
        have take : Q.view.Take c.history token i := ⟨⟨_, hx, by simp [IndexQueue.view, IndexQueue.isTake, qs]⟩, rfl⟩
        have actual := shape.takeSlot _ _ run _ _ take
        rw [hx] at actual
        exact ⟨token, by simp at actual; exact actual.1.symm, Or.inr ⟨take, rfl⟩⟩

theorem IndexQueue.slotRaceFree {Q : IndexQueue} (shape : Q.Shaped l s)
    (refines : QueueRefines l s Q.view) (run : Run l (l.initial s) cs c) (n : Nat) :
    ¬ RaceOn l c.history (Q.slotOf n) := by
  apply refines.slot_race_free shape.slotOnly _ _ _ _ run n
  · intro k
    simp [IndexQueue.view, IndexQueue.slotOf]
  · intro a b eq
    exact congrArg Fin.val (Q.slots_inj eq)

theorem Dispatch.slotRaceFree (w : CellWrites) (s : DistState)
    (ht : (s.cell DeepEPChannel.tail).readAs .nat = some 0)
    (hh : (s.cell DeepEPChannel.head).readAs .nat = some 0)
    (r : Run (Dispatch.launch DeepEPChannel.rel w) ((Dispatch.launch DeepEPChannel.rel w).initial s) cs c) :
    ¬ RaceOn (Dispatch.launch DeepEPChannel.rel w) c.history DeepEPChannel.slot :=
  IndexQueue.slotRaceFree (Dispatch.shaped w s ht hh) (IndexQueue.refines_singleSlot w s ht hh) r 0

#print axioms IndexQueue.Shaped.slotOnly
#print axioms Dispatch.slotRaceFree
#print axioms QueueRefines.slot_race_free
end VeriTile.Tests.G1QueueRefinement
