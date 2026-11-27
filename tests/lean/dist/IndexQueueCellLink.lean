import tests.lean.dist.IndexQueueSlotRace
import tests.lean.dist.IndexQueueCells

/-! A one-cell entry uses the slot access itself as its completion marker.
The link compares the cell-set and original queue contracts on those histories. -/
namespace VeriTile.Tests.G1QueueRefinement
open VeriTile.Dist IndexQueueCells

def IndexQueue.cellView (Q : IndexQueue) : View where
  cap := Q.cap
  cap_pos := Q.cap_pos
  slots j := {Q.slots j}
  slot_nonempty _ := Finset.singleton_nonempty _
  putEnd := Q.isPut
  takeEnd := Q.isTake
  writers _ _ a := a = Q.sender
  readers _ _ a := a = Q.receiver

private theorem mem_cellView {Q : IndexQueue} {p k} :
    p ∈ Q.cellView.slotOf k ↔ p = Q.slotOf k := Finset.mem_singleton

private theorem ordinal_lt {f h k m i j} (a : Boundary f h k i) (b : Boundary f h m j) :
    i < j ↔ k < m := by
  have forward : ∀ {k m i j}, Boundary f h k i → Boundary f h m j → i < j → k < m := by
    intro k m i j first second lt
    obtain ⟨⟨x, hx, yes⟩, ci⟩ := first
    obtain ⟨_, cj⟩ := second
    obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp hx
    have count : (h.take (i+1)).countP f = k + 1 := by
      simp [List.take_succ_eq_append_getElem bound, eq, yes, ci]
    have le := (List.take_prefix_take_left (l := h) (i := i+1) (j := j) lt).countP_le (p := f)
    omega
  refine ⟨forward a b, fun lt => ?_⟩
  rcases lt_trichotomy i j with before | rfl | after
  · exact before
  · exact False.elim (by have := a.2; have := b.2; omega)
  · exact False.elim (by have := forward b a after; omega)

private theorem componentAt {v : View} {f h k stop p} (mark : Boundary f h k stop) :
    v.Component f h k stop p stop :=
  ⟨le_rfl, fun _ _ lt _ old => (ordinal_lt old mark).2 lt⟩

private theorem uniqueComponent {v : View} {f h k stop p i t}
    (stopMark : Boundary f h k stop) (mark : Boundary f h t i)
    (same : p ∈ v.slotOf t) (part : v.Component f h k stop p i) : i = stop := by
  by_contra neq
  have lt := (ordinal_lt mark stopMark).1 (Nat.lt_of_le_of_ne part.1 neq)
  exact Nat.lt_irrefl i (part.2 t i lt same mark)

private theorem putAt {Q : IndexQueue} (sh : Q.Shaped l s) (run : Run l (l.initial s) cs c)
    {k i} (b : Q.view.Put c.history k i) :
    Q.cellView.PutComponent c.history k i (Q.slotOf k) i ∧ Writes c.history i (Q.slotOf k) := by
  have atI := sh.putSlot _ _ run _ _ b
  exact ⟨⟨componentAt b, _, atI, rfl⟩, _, .store, .plain, atI, by simp [Occurrence.access, Event.accesses], rfl⟩

private theorem takeAt {Q : IndexQueue} (sh : Q.Shaped l s) (run : Run l (l.initial s) cs c)
    {k j} (b : Q.view.Take c.history k j) :
    Q.cellView.TakeComponent c.history k j (Q.slotOf k) j ∧ Reads c.history j (Q.slotOf k) := by
  have atJ := sh.takeSlot _ _ run _ _ b
  exact ⟨⟨componentAt b, _, atJ, rfl⟩, _, .plain, atJ, by simp [Occurrence.access, Event.accesses]⟩

private theorem putAt_unique {Q : IndexQueue} (sh : Q.Shaped l s) (run : Run l (l.initial s) cs c)
    {k stop i} (b : Q.view.Put c.history k stop)
    (part : Q.cellView.PutComponent c.history k stop (Q.slotOf k) i) (w : Writes c.history i (Q.slotOf k)) :
    i = stop := by
  obtain ⟨x,kd,m,hx,access,writes⟩ := w
  obtain ⟨t,same,marked | ⟨_,read⟩⟩ := sh.slotOnly _ _ run _ _ _ _ _ k hx access rfl
  · exact uniqueComponent b marked (mem_cellView.mpr same.symm) part.1
  · simp [writes] at read

/-- Every shaped one-cell queue satisfying the cell-set contract satisfies the
original queue contract, for arbitrary capacity, including incomplete runs. -/
theorem IndexQueue.refines_of_cellView {Q : IndexQueue} (sh : Q.Shaped l s)
    (cells : Q.cellView.Refines l s) : QueueRefines l s Q.view := by
  intro cs c run
  obtain ⟨puts, hand, reuse⟩ := cells _ _ run
  constructor
  · intro k j take
    obtain ⟨stop,put,_,choose⟩ := hand k j take
    obtain ⟨component,read⟩ := takeAt sh run take
    obtain ⟨i,part,w,lt,last,hb⟩ := choose _ (mem_cellView.mpr rfl) _ component read
    obtain rfl := putAt_unique sh run put.1 part w
    refine ⟨i,put.1,lt,?_,hb⟩
    intro u x lower upper hx kd m access
    cases e : kd.writes with
    | false => rfl
    | true => exact False.elim (last u lower upper ⟨x,kd,m,hx,access,e⟩)
  · intro k i put
    change Q.view.Put c.history (k + Q.cap) i at put
    have later : k < k + Q.cap := Nat.lt_add_of_pos_right Q.cap_pos
    have same : Q.slotOf (k + Q.cap) = Q.slotOf k := by simp [IndexQueue.slotOf]
    obtain ⟨j,_,take,_,order⟩ := reuse k _ i later
      ⟨_,mem_cellView.mpr rfl,mem_cellView.mpr same.symm⟩ (puts _ _ put)
    obtain ⟨tc,rc⟩ := takeAt sh run take.1
    obtain ⟨pc,wc⟩ := putAt sh run put
    rw [same] at pc wc
    exact ⟨j,take.1, order _ (mem_cellView.mpr rfl) (mem_cellView.mpr same.symm) _ _ tc rc pc wc⟩

private theorem takeAt_unique {Q : IndexQueue} (sh : Q.Shaped l s) (run : Run l (l.initial s) cs c)
    {k stop i} (b : Q.view.Take c.history k stop)
    (part : Q.cellView.TakeComponent c.history k stop (Q.slotOf k) i) (read : Reads c.history i (Q.slotOf k)) :
    i = stop := by
  obtain ⟨x,m,hx,access⟩ := read
  obtain ⟨t,same,marked | ⟨take,_⟩⟩ := sh.slotOnly _ _ run _ _ _ _ _ k hx access rfl
  · have atPut := sh.putSlot _ _ run _ _ marked
    rw [hx] at atPut
    cases atPut
    simp [Occurrence.access, Event.accesses] at access
  · exact uniqueComponent b take (mem_cellView.mpr same.symm) part.1

/-- Chain one-lap reuse through the intervening handoffs on this slot. -/
private theorem reuseAfterLaps {Q : IndexQueue} (ref : QueueRefines l s Q.view)
    (run : Run l (l.initial s) cs c) (k n i : Nat)
    (put : Q.view.Put c.history (k + (n + 1) * Q.cap) i) :
    ∃ j, Q.view.Take c.history k j ∧ j < i ∧ HB l c.history (Q.slotOf k) j i := by
  obtain ⟨hand,reuse⟩ := ref _ _ run
  induction n generalizing i with
  | zero => exact reuse k i (by simpa using put)
  | succ n ih =>
    let m := k + (n + 1) * Q.cap
    have same : Q.view.slotOf m = Q.slotOf k := by simp [IndexQueue.view, IndexQueue.slotOf, m]
    obtain ⟨j,take,ji,hop⟩ := reuse m i (by simpa [m,Nat.succ_mul,← Nat.add_assoc] using put)
    obtain ⟨prev,p,prevj,_,forward⟩ := hand m j take
    obtain ⟨first,t,lt,earlier⟩ := ih prev p
    exact ⟨first,t,lt.trans (prevj.trans ji),earlier.trans (same ▸ forward.trans hop)⟩

/-- A shaped one-cell queue realizes the cell-set contract, including reuse of
a cell after several ring revolutions and the absence of intervening writes. -/
theorem IndexQueue.cellView_of_refines {Q : IndexQueue} (sh : Q.Shaped l s)
    (ref : QueueRefines l s Q.view) : Q.cellView.Refines l s := by
  intro cs c run
  have put {k i} (b : Q.view.Put c.history k i) : Q.cellView.Put c.history k i := by
    exact ⟨b, fun p hp => (mem_cellView.mp hp) ▸ ⟨i,putAt sh run b⟩⟩
  have take {k j} (b : Q.view.Take c.history k j) : Q.cellView.Take c.history k j := by
    exact ⟨b, fun p hp => (mem_cellView.mp hp) ▸ ⟨j,takeAt sh run b⟩⟩
  refine ⟨fun _ _ => put, ?_, ?_⟩
  · intro k j b
    obtain ⟨i,prev,lt,nw,hb⟩ := (ref _ _ run).1 _ _ b
    refine ⟨i,put prev,take b,?_⟩
    intro p hp j' tc rc
    obtain rfl := mem_cellView.mp hp
    obtain rfl := takeAt_unique sh run b tc rc
    refine ⟨i,(putAt sh run prev).1,(putAt sh run prev).2,lt,?_,hb⟩
    rintro u iu uj ⟨x,kd,m,hx,act,yes⟩
    simpa [yes] using nw u x iu uj hx kd m act
  · rintro old later i lt ⟨p,hp,hq⟩ marked
    have same := (mem_cellView.mp hp).symm.trans (mem_cellView.mp hq)
    have modEq : old % Q.cap = later % Q.cap := congrArg Fin.val (Q.slots_inj same)
    obtain ⟨n, hn⟩ := (Nat.modEq_iff_dvd' lt.le).mp modEq
    cases n with
    | zero => simp at hn; omega
    | succ n =>
      have eq : later = old + (n+1)*Q.cap := by rw [Nat.mul_comm] at hn; omega
      obtain ⟨j,b,ji,hb⟩ := reuseAfterLaps ref run old n i (eq ▸ marked.1)
      refine ⟨j,lt,take b,marked,?_⟩
      intro q ho hl j' i' tc rc pc wc
      obtain rfl := mem_cellView.mp ho
      have t := takeAt_unique sh run b tc rc
      rw [same] at pc wc
      have u := putAt_unique sh run marked.1 pc wc
      simpa [t,u] using And.intro ji hb

theorem Dispatch.singleCellRefines (w : CellWrites) (s : DistState)
    (ht : (s.cell DeepEPChannel.tail).readAs .nat = some 0)
    (hh : (s.cell DeepEPChannel.head).readAs .nat = some 0) :
    (Q1 DeepEPChannel.rel).cellView.Refines (launch DeepEPChannel.rel w) s :=
  IndexQueue.cellView_of_refines (Dispatch.shaped w s ht hh) (IndexQueue.refines_singleSlot w s ht hh)

#print axioms IndexQueue.refines_of_cellView
#print axioms IndexQueue.cellView_of_refines
#print axioms Dispatch.singleCellRefines
end VeriTile.Tests.G1QueueRefinement
