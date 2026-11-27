import tests.lean.dist.IndexQueueSingleSlotModel

/-! A sender's successful room wait reads the current physical head word, including all
earlier emissions in its group. The trace reconstructs that word because shape permits
only stores to write it and the sound segment frame preserves it outside a write set. -/
namespace VeriTile.Tests.G1QueueRefinement.IndexQueue
open VeriTile.Dist
open VeriTile.Triton (MemCell)

private def current (s : DistState) (p : Addr) (h : History) : MemCell :=
  (h.filterMap (storedAt p)).getLast?.getD (s.cell p)

private theorem current_append (x : Occurrence) (h : History) :
    current s p (h ++ [x]) = (storedAt p x).getD (current s p h) := by
  cases hx : storedAt p x <;> simp [current, hx]

private def Good (Q : IndexQueue) (x : Occurrence) : Prop :=
  ∀ k m, x.access Q.head k m → Q.Allowed x

private def WaitAt (Q : IndexQueue) (n : Nat) : Occurrence :=
  .issued Q.sender ⟨Q.sender, .wait (.word Q.head) .ge n Q.room, .noValue⟩

private def Valid (Q : IndexQueue) (s : DistState) (m : Machine) : Prop :=
  m.mem.cell Q.head = current s Q.head m.history ∧
  ∀ i n, m.history[i]? = some (WaitAt Q n) →
    ∃ h, (lastValue s m.history Q.head i).readAs .nat = some h ∧ n ≤ h

private theorem extendValid (v : Valid Q s m) (x : Occurrence) (mem : DistState)
    (pending : List Outstanding) (next : mem.cell Q.head = (storedAt Q.head x).getD (m.mem.cell Q.head))
    (wait : ∀ n, x = WaitAt Q n → ∃ h, (m.mem.cell Q.head).readAs .nat = some h ∧ n ≤ h) :
    Valid Q s ⟨mem, m.history ++ [x], pending⟩ := by
  refine ⟨next.trans (by rw [v.1, current_append]), ?_⟩
  intro i n atI
  change (m.history ++ [x])[i]? = _ at atI
  by_cases earlier : i < m.history.length
  · rw [List.getElem?_append_left earlier] at atI
    simpa [lastValue, List.take_append_of_le_length (Nat.le_of_lt earlier)] using v.2 i n atI
  · have bound := (List.getElem?_eq_some_iff.mp atI).1
    simp at bound
    have : i = m.history.length := by omega
    subst i
    have same : x = WaitAt Q n := by simpa using atI
    simpa [lastValue, current, v.1, List.take_append_of_le_length (Nat.le_refl _)] using wait n same

private theorem noBump (ok : Good Q (.issued a ⟨b,.bump update,d⟩)) :
    update.counter ≠ .word Q.head := by
  intro eq
  have allowed := ok update.op.kind update.mode (by simp [Occurrence.access, Event.accesses, Bump.accesses, eq])
  simp [Allowed] at allowed

private theorem fireCell (fire : Fire l m e mem pending v) (ok : Good Q (.issued a e)) :
    mem.cell Q.head = (storedAt Q.head (.issued a e)).getD (m.mem.cell Q.head) := by
  cases fire with
  | store who q mode val =>
    by_cases eq : q = Q.head
    · subst q; simp [storedAt, l.cells.read_same]
    · simp [storedAt, eq, l.cells.read_other _ _ _ _ (Ne.symm eq)]
  | update who q mode f =>
    apply l.cells.read_other
    intro eq
    have allowed := ok .update mode (by simp [Occurrence.access, Event.accesses, eq])
    simp [Allowed] at allowed
  | bump who b old read =>
    have other := noBump ok
    obtain ⟨counter,op,n,mode⟩ := b
    cases counter with
    | word q => exact l.cells.read_other _ _ _ _ (fun eq => other (by rw [eq]))
    | phase | rendezvous | delivered => rfl
  | discardAdd => exact l.cells.read_other _ _ _ _ (fun eq => noBump ok (by rw [eq]))
  | load | fence | wait | initiate => rfl

private theorem groupHistory (g : FireGroup l a m xs f vs) :
    f.history = m.history ++ xs.map (.issued a) := by
  induction g with
  | nil => simp
  | cons _ _ _ _ _ ih => simpa [List.append_assoc] using ih

private theorem groupValid (g : FireGroup l a m xs f vs) (v : Valid Q s m)
    (good : ∀ e ∈ xs, Good Q (.issued a e)) : Valid Q s f := by
  induction g with
  | nil => exact v
  | cons access available ordered fire rest ih =>
    apply ih (extendValid v _ _ _ (fireCell fire (good _ (by simp))) ?_) (fun _ he => good _ (by simp [he]))
    intro n eq
    cases eq
    cases fire with
    | wait _ _ _ _ _ h read enabled => exact ⟨h,read,enabled⟩

private theorem copyOther (w : CellWrites) (dst : List Addr) (data : List MemCell)
    (mem : DistState) (outside : p ∉ dst) :
    ((dst.zip data).foldl (fun s qv => w.put s qv.1 qv.2) mem).cell p = mem.cell p := by
  induction dst generalizing data mem with
  | nil => rfl
  | cons q qs ih =>
    cases data with
    | nil => rfl
    | cons v vs =>
      simp only [List.mem_cons, not_or] at outside
      change ((qs.zip vs).foldl _ (w.put mem q v)).cell p = _
      exact (ih vs _ outside.2).trans (w.read_other _ _ _ _ outside.1)

private theorem stepValid (sound : SoundLaunch l) (move : step l c ch d) (v : Valid Q s c.toMachine)
    (good : ∀ x ∈ d.history, Good Q x) : Valid Q s d.toMachine := by
  classical
  cases move with
  | @segment a pc seg mem cursor code owner access ran =>
    subst seg
    apply extendValid v _ _ _ _ (by intro n e; cases e)
    apply Segment.frame (sound.footprints a pc) ran
    intro inside
    exact good (.segment a _ (((l.program a).segment pc).writes c.mem))
      (List.mem_append_right _ (List.mem_singleton_self _)) .store .plain inside
  | fire cursor owned group =>
    apply groupValid group v
    intro e he
    apply good
    rw [groupHistory group]
    exact List.mem_append_right _ (List.mem_map_of_mem he)
  | @deliver pre post o b old outstanding bound counter ordered disjoint access free =>
    have ok := good (.delivered o.owner o.transfer o.start) (by simp)
    have outside : Q.head ∉ o.transfer.dst := by
      intro inside
      apply ok .store .plain
      simp [Occurrence.access, Event.accesses, inside]
    have other : b.counter ≠ .word Q.head := by
      intro eq
      apply ok b.op.kind b.mode
      simp [Occurrence.access, Event.accesses, bound, Bump.accesses, eq]
    apply extendValid v _ _ _ _ (by intro n e; cases e)
    obtain ⟨bc,op,n,mode⟩ := b
    cases bc with
    | word q =>
      exact (l.cells.read_other _ _ _ _ (fun eq => other (by rw [eq]))).trans
        (copyOther l.cells _ _ _ outside)
    | phase | rendezvous | delivered => exact copyOther l.cells _ _ _ outside

/-- A room wait at any position in a reachable history has a physical natural-number
witness at that exact prefix, with the requested threshold already reached. -/
theorem roomWaitValue {Q : IndexQueue} (sound : SoundLaunch l) (shape : Q.Shaped l s)
    (r : Run l (l.initial s) cs f) {i n}
    (hit : f.history[i]? = some (.issued Q.sender ⟨Q.sender,.wait (.word Q.head) .ge n Q.room,.noValue⟩)) :
    ∃ h, (lastValue s f.history Q.head i).readAs .nat = some h ∧ n ≤ h := by
  suffices walk : ∀ {c d cs}, Run l c cs d → ∀ {pre}, Run l (l.initial s) pre c →
      Valid Q s c.toMachine → Valid Q s d.toMachine by
    apply (walk r (.nil _) ⟨rfl, by simp [Launch.initial]⟩).2 i n hit
  intro c d cs run
  induction run with
  | nil => exact fun _ v => v
  | @cons c m d ch cs st rest ih =>
    intro pre reachable v
    have next := DeepEPChannel.appendRuns reachable (.cons st (.nil _))
    apply ih next (stepValid sound st v ?_)
    intro x hx kd mode access
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    exact shape.cells _ _ next _ _ _ _ _ hi access (Or.inr (Or.inl rfl))

#print axioms roomWaitValue
end VeriTile.Tests.G1QueueRefinement.IndexQueue
