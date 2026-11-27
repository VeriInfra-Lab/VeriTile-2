import tests.lean.dist.IndexQueueHandoff
import tests.lean.dist.IndexQueueRoomWait
import tests.lean.dist.IndexQueueSound

/-! Refinement of an arbitrary shaped index queue. The tail observation locates
the matching payload write. The room wait orders a later reuse after the take. -/

namespace VeriTile.Tests.G1QueueRefinement
open VeriTile.Dist
open VeriTile.Triton (MemCell)

private theorem latest {α β : Type} (f : α → Option β) (xs : List α) {v : β}
    (hit : (xs.filterMap f).getLast? = some v) :
    ∃ (i : Nat) (x : α), xs[i]? = some x ∧ f x = some v ∧ ∀ (u : Nat) (y : α), i < u → xs[u]? = some y → f y = none := by
  induction xs using List.reverseRecOn with
  | nil => simp at hit
  | append_singleton xs x ih =>
    cases hx : f x with
    | some a =>
      simp [List.filterMap_append,hx] at hit
      subst a
      refine ⟨xs.length,x,by simp,hx,?_⟩
      intro u y gt atU
      have len := (List.getElem?_eq_some_iff.mp atU).1
      simp at len
      omega
    | none =>
      simp [List.filterMap_append,hx] at hit
      obtain ⟨i,z,atI,fz,last⟩ := ih (by simpa using hit)
      have il := (List.getElem?_eq_some_iff.mp atI).1
      refine ⟨i,z,by simpa [List.getElem?_append_left il] using atI,fz,?_⟩
      intro u y gt atU
      by_cases h : u < xs.length
      · exact last _ _ gt (by simpa [List.getElem?_append_left h] using atU)
      · rw [List.getElem?_append_right (by omega)] at atU
        cases d : u - xs.length with
        | zero => simpa [d] using (show f y = none from (by simpa [d] using atU) ▸ hx)
        | succ n => simp [d] at atU

private def StoreData : Occurrence → Prop
  | .issued _ ⟨_,.access .store _ _,d⟩ => ∃ v, d = .store v
  | _ => True

private theorem storeData {l : Launch P} (r : Run l (l.initial s) cs c) : ∀ x ∈ c.history, StoreData x := by
  have group {a : Agent} {m f : Machine} {xs vs} (g : FireGroup l a m xs f vs)
      (ok : ∀ x ∈ m.history, StoreData x) : ∀ x ∈ f.history, StoreData x := by
    induction g with
    | nil => exact ok
    | cons _ _ _ fire _ ih =>
      apply ih
      intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with old | rfl
      · exact ok _ old
      · cases fire <;> simp [StoreData]
  have walk {start final : Config P} {sched} (run : Run l start sched final)
      (ok : ∀ x ∈ start.history, StoreData x) : ∀ x ∈ final.history, StoreData x := by
    induction run with
    | nil => exact ok
    | cons step _ ih =>
      apply ih
      cases step with
      | segment | deliver =>
        intro y hy
        rcases List.mem_append.mp hy with old | singleton
        · exact ok y old
        · simp only [List.mem_singleton] at singleton
          subst y; trivial
      | fire _ _ fires => exact group fires ok
  exact walk r (by simp [Launch.initial])

private theorem slot_ne_control {Q : IndexQueue} {q p} (hq : Q.isSlot q = true)
    (hp : p = Q.head ∨ p = Q.tail) : q ≠ p := by
  obtain ⟨j,_,hj⟩ := List.any_eq_true.mp hq
  have eq : Q.slots j = q := by simpa using hj
  rcases hp with rfl | rfl
  · exact eq ▸ Q.slot_ne_head j
  · exact eq ▸ Q.slot_ne_tail j

/-- On either control word every actual write has a recorded store payload. -/
private theorem recorded_of_write {Q : IndexQueue} (sh : Q.Shaped l s) (run : Run l (l.initial s) cs c)
    {i : Nat} {x p kd m} (atI : c.history[i]? = some x) (hp : p = Q.head ∨ p = Q.tail)
    (access : x.access p kd m) (write : kd.writes = true) :
    ∃ v, IndexQueue.storedAt p x = some v := by
  have allowed := sh.cells _ _ run _ _ _ _ _ atI access (hp.elim (fun h => Or.inr (Or.inl h)) Or.inl)
  have data := storeData run x (List.mem_of_getElem? atI)
  cases x with
  | segment | delivered => exact False.elim allowed
  | issued a e =>
    rcases e with ⟨b,ev,d⟩
    rcases allowed with ⟨rfl, ⟨rfl, send⟩ | ⟨rfl,recv⟩⟩
    · rcases send with rfl | ⟨t,rfl⟩ | ⟨q,hq,rfl⟩
      · obtain ⟨v,rfl⟩ := data
        simp [Occurrence.access, Event.accesses] at access
        simp [IndexQueue.storedAt,access.2.1]
      · simp [Occurrence.access, Event.accesses] at access; simp [access.1, AccessKind.writes] at write
      · simp [Occurrence.access, Event.accesses] at access
        exact False.elim (slot_ne_control hq hp access.2.1.symm)
    · rcases recv with rfl | rfl | ⟨q,hq,rfl⟩
      · simp [Occurrence.access, Event.accesses] at access; simp [access.1, AccessKind.writes] at write
      · obtain ⟨v,rfl⟩ := data
        simp [Occurrence.access, Event.accesses] at access
        simp [IndexQueue.storedAt,access.2.1]
      · simp [Occurrence.access, Event.accesses] at access; simp [access.1, AccessKind.writes] at write

private theorem controlStore {Q : IndexQueue} (sh : Q.Shaped l s) (run : Run l (l.initial s) cs c)
    {i : Nat} {x p v} (atI : c.history[i]? = some x) (stored : IndexQueue.storedAt p x = some v)
    (hp : p = Q.head ∨ p = Q.tail) :
    (p = Q.head → x = .issued Q.receiver ⟨Q.receiver,.access .store p Q.ack,.store v⟩) ∧
    (p = Q.tail → x = .issued Q.sender ⟨Q.sender,.access .store p Q.publish,.store v⟩) := by
  unfold IndexQueue.storedAt at stored
  split at stored
  · split at stored
    · rename_i same
      subst same
      cases stored
      rename_i program actor addr mode
      have allowed := sh.cells _ _ run _ _ addr .store mode atI (by simp [Occurrence.access, Event.accesses])
        (hp.elim (fun h => Or.inr (Or.inl h)) Or.inl)
      rcases allowed with ⟨rfl, ⟨rfl,h⟩ | ⟨rfl,h⟩⟩
      · rcases h with e | ⟨_,e⟩ | ⟨q,hq,e⟩
        · cases e; exact ⟨fun he => False.elim (Q.tail_ne_head he),fun _ => rfl⟩
        · cases e
        · cases e; exact False.elim (slot_ne_control hq hp rfl)
      · rcases h with e | e | ⟨q,hq,e⟩
        · cases e
        · cases e; exact ⟨fun _ => rfl,fun he => False.elim (Q.tail_ne_head he.symm)⟩
        · cases e
    · contradiction
  · contradiction

/-- A positive observation of a zero-initialized control word has an actual
immediately preceding store, with no intervening write even inside a group. -/
private theorem latestControl {Q : IndexQueue} (sh : Q.Shaped l s) (run : Run l (l.initial s) cs c)
    {p : Addr} {j n : Nat} (hp : p = Q.head ∨ p = Q.tail) (zero : (s.cell p).readAs .nat = some 0)
    (obs : (IndexQueue.lastValue s c.history p j).readAs .nat = some n) (pos : 0 < n) :
    ∃ (i : Nat) (x : Occurrence) (v : MemCell), c.history[i]? = some x ∧ IndexQueue.storedAt p x = some v ∧
      v.readAs .nat = some n ∧ ReadsFrom c.history i j (.word p) := by
  unfold IndexQueue.lastValue at obs
  cases hit : ((c.history.take j).filterMap (IndexQueue.storedAt p)).getLast? with
  | none => rw [hit] at obs; rw [show (none : Option MemCell).getD (s.cell p) = s.cell p from rfl,zero] at obs; cases obs; omega
  | some v =>
    rw [hit] at obs
    obtain ⟨i,x,hx,stored,last⟩ := latest _ _ hit
    have len := (List.getElem?_eq_some_iff.mp hx).1
    rw [List.length_take] at len
    have before : i < j := by omega
    rw [List.getElem?_take_of_lt before] at hx
    refine ⟨i,x,v,hx,stored,obs,before,?_⟩
    intro u y iu uj hy kd m access
    cases eq : kd.writes with
    | false => rfl
    | true =>
      obtain ⟨v,real⟩ := recorded_of_write sh run hy hp access eq
      have missing := last u y iu (by rwa [List.getElem?_take_of_lt uj])
      simp [real] at missing

private theorem po {l : Launch P} {h : History} {i j : Nat} {x y a}
    (hx : h[i]? = some x) (hy : h[j]? = some y) (before : i < j)
    (left : x.program? = some a) (right : y.program? = some a) (p : Addr) : HB l h p i j :=
  .single ⟨x,y,hx,hy,before,Or.inl ⟨a,left,right⟩⟩

private theorem handoff {Q : IndexQueue} (sh : Q.Shaped l s) (run : Run l (l.initial s) cs c)
    (zero : (s.cell Q.tail).readAs .nat = some 0)
    (modes : ∀ p, Mode.Pairs l.reach p Q.sender Q.receiver Q.publish Q.poll) {k j}
    (take : Q.view.Take c.history k j) :
    ∃ i, Q.view.Put c.history k i ∧ i < j ∧ HB l c.history (Q.slotOf k) i j := by
  obtain ⟨poll,n,pj,kn,obs,atPoll⟩ := sh.pollFirst _ _ run _ _ take
  obtain ⟨release,x,v,atRel,stored,reads,source⟩ := latestControl (n := n) sh run (Or.inr rfl) zero obs (Nat.zero_lt_of_lt kn)
  have pub := (controlStore sh run atRel stored (Or.inr rfl)).2 rfl
  subst x
  obtain ⟨t,encoded,tc⟩ := sh.publishWritten _ _ run _ _ atRel
  rw [reads] at encoded
  cases encoded
  obtain ⟨i,ir,put⟩ := NthAt.exists_before_of_lt_countP (h := c.history) (tc ▸ kn)
  have atPut := sh.putSlot _ _ run _ _ put
  have atTake := sh.takeSlot _ _ run _ _ take
  have sync : SyncEdge l.reach (Q.slotOf k) (Q.sender,.access .store Q.tail Q.publish)
      (Q.receiver,.access .load Q.tail Q.poll) := ⟨_,_,_,rfl,rfl,modes _⟩
  have edge := sync.hb_of_readsFrom (by simp [atRel,Occurrence.event?]) (by simp [atPoll,Occurrence.event?]) rfl source
  exact ⟨i,put,ir.trans (source.1.trans pj),(po atPut atRel ir rfl rfl _).trans (edge.trans (po atPoll atTake pj rfl rfl _))⟩

private theorem reuse {Q : IndexQueue} (sound : SoundLaunch l) (sh : Q.Shaped l s) (run : Run l (l.initial s) cs c)
    (zero : (s.cell Q.head).readAs .nat = some 0)
    (modes : ∀ p, Mode.Pairs l.reach p Q.receiver Q.sender Q.ack Q.room)
    {k i} (put : Q.view.Put c.history (k + Q.cap) i) :
    ∃ j, Q.view.Take c.history k j ∧ j < i ∧ HB l c.history (Q.slotOf k) j i := by
  obtain ⟨u,n,ui,threshold,atWait⟩ := sh.roomFirst _ _ run _ _ put (by omega)
  obtain ⟨h,obs,ge⟩ := IndexQueue.roomWaitValue sound sh run atWait
  change n ≤ (h : Nat) at ge
  have kh : k < h := by omega
  obtain ⟨release,x,v,atRel,stored,reads,source⟩ := latestControl sh run (Or.inl rfl) zero obs (Nat.zero_lt_of_lt kh)
  have ack := (controlStore sh run atRel stored (Or.inl rfl)).1 rfl
  subst x
  obtain ⟨t,encoded,tc⟩ := sh.ackRead _ _ run _ _ atRel
  rw [reads] at encoded
  cases encoded
  obtain ⟨j,jr,take⟩ := NthAt.exists_before_of_lt_countP (h := c.history) (tc ▸ kh)
  have atPut := sh.putSlot _ _ run _ _ put
  have atTake := sh.takeSlot _ _ run _ _ take
  have sync : SyncEdge l.reach (Q.slotOf k) (Q.receiver,.access .store Q.head Q.ack)
      (Q.sender,.wait (.word Q.head) .ge n Q.room) := ⟨_,_,_,rfl,rfl,modes _⟩
  have edge := sync.hb_of_readsFrom (by simp [atRel,Occurrence.event?]) (by simp [atWait,Occurrence.event?]) rfl source
  exact ⟨j,take,jr.trans (source.1.trans ui),(po atTake atRel jr rfl rfl _).trans (edge.trans (po atWait atPut ui rfl rfl _))⟩


/-- Acquire observations read published counts, and the releases order the
matching slot traffic for each finite prefix. Neither direction needs a bound
on the total number of puts. -/
theorem IndexQueue.refines {Q : IndexQueue} (sound : SoundLaunch l) (sh : Q.Shaped l s)
    (publishPairs : ∀ p, Mode.Pairs l.reach p Q.sender Q.receiver Q.publish Q.poll)
    (ackPairs : ∀ p, Mode.Pairs l.reach p Q.receiver Q.sender Q.ack Q.room)
    (tail0 : (s.cell Q.tail).readAs .nat = some 0) (head0 : (s.cell Q.head).readAs .nat = some 0) :
    QueueRefines l s Q.view :=
  IndexQueue.refines_of_ordered_handoffs sh
    (fun _ _ run _ _ take => handoff sh run tail0 publishPairs take)
    (fun _ _ run _ _ put => reuse sound sh run head0 ackPairs put)

/-- Apply the general theorem to the release-head dispatch and expose the
cell-set contract directly at its client entry. -/
theorem Dispatch.cellRefines_of_soundShape (w : CellWrites) (s : DistState)
    (ht : (s.cell DeepEPChannel.tail).readAs .nat = some 0)
    (hh : (s.cell DeepEPChannel.head).readAs .nat = some 0) :
    (Q1 DeepEPChannel.rel).cellView.Refines (launch DeepEPChannel.rel w) s := by
  have sh := Dispatch.shaped w s ht hh
  exact IndexQueue.cellView_of_refines sh (IndexQueue.refines (launchSound _ w) sh
    (publish_pairs _ w) (release_ack_pairs w) ht hh)

/-- The released, one-slot/two-token dispatcher completes from two ranks with
zeroed cells. The general theorem gives its cell contract at all prefixes; the
delivery corollary locates each of the two distinct physical reads. -/
theorem Dispatch.completeGeneralClient :
    let Q := Q1 DeepEPChannel.rel
    let l := launch DeepEPChannel.rel Tutorial01.putCellWrites
    let s := HiddenShaped.zero
    Q.cellView.Refines l s ∧ ∃ cs final, Run l (l.initial s) cs final ∧ Complete final ∧
      ∃ i j, Q.view.Take final.history 0 i ∧ Q.view.Take final.history 1 j ∧ i < j := by
  dsimp only
  have sh := shaped Tutorial01.putCellWrites HiddenShaped.zero rfl rfl
  refine ⟨cellRefines_of_soundShape _ _ rfl rfl,?_⟩
  obtain ⟨cs,final,run,done,_⟩ := SingleSlotWitness.completeScheduled Tutorial01.putCellWrites HiddenShaped.zero
  obtain ⟨i,first⟩ := IndexQueue.delivers sh cs final run done 0 (by decide)
  obtain ⟨j,second⟩ := IndexQueue.delivers sh cs final run done 1 (by decide)
  exact ⟨cs,final,run,done,i,j,first,second,(NthAt.ordinal_lt first second).2 (by decide)⟩

#print axioms Dispatch.completeGeneralClient
#print axioms HiddenShaped.counterexample
#print axioms HiddenShaped.unsound
#print axioms Dispatch.relaxed_not_refines
#print axioms Dispatch.DecreasingTail.not_shaped
#print axioms IndexQueue.refines
#print axioms Dispatch.cellRefines_of_soundShape
end VeriTile.Tests.G1QueueRefinement
