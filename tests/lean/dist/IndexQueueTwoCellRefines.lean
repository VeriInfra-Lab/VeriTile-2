import tests.lean.dist.IndexQueueTwoCellRuns
import tests.lean.dist.IndexQueueWarpOrder

namespace VeriTile.Tests.IndexQueueCells.Client
open VeriTile.Dist IndexQueueWarpOrder
open DeepEPChannel (sender receiver tail head slot rel acq segOcc)

/-- The phase index has at most one actual position for each protocol event.
The other positions are empty segments. -/
private theorem uniquePosition (tr : TokenTrace n h) (pred : Occurrence → Prop) (tag : Nat)
    (quiet : ∀ a, ¬ pred (segOcc a))
    (only : ∀ i, i < 7 → pred (tokenEvent i) → i = tag)
    (seen : h[u]? = some x) (matchPred : pred x) : tag < n ∧ u = tr.pos tag := by
  rcases tr.covers u x seen with ⟨a,rfl⟩ | ⟨i,hi,rfl⟩
  · exact False.elim (quiet a matchPred)
  · rw [tr.atEvent i hi] at seen
    cases seen
    have eq := only i (by have := tr.bound; omega) matchPred
    subst i
    exact ⟨hi,rfl⟩

private theorem boundaryAt (tr : TokenTrace n h) (ends : Occurrence → Bool) (tag : Nat)
    (quiet : ∀ a, ends (segOcc a) ≠ true)
    (only : ∀ i, i < 7 → ends (tokenEvent i) = true → i = tag)
    (yes : ends (tokenEvent tag) = true) (ht : tag < n) :
    Boundary ends h 0 (tr.pos tag) := by
  refine ⟨⟨_,tr.atEvent tag ht,yes⟩,List.countP_eq_zero.mpr ?_⟩
  intro x member hit
  obtain ⟨u,hu,eq⟩ := List.mem_take_iff_getElem.mp member
  have atU : h[u]? = some x := by simp [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hu (min_le_right _ _)),eq]
  have pos := (uniquePosition tr (fun o => ends o = true) tag quiet only atU hit).2
  omega

private def putOnly (i : Nat) (bound : i < 7) : view.putEnd (tokenEvent i) = true → i = 2 := by
  interval_cases i <;> decide
private def takeOnly (i : Nat) (bound : i < 7) : view.takeEnd (tokenEvent i) = true → i = 6 := by
  interval_cases i <;> decide

private theorem boundaryInfo (tr : TokenTrace n h) (ends : Occurrence → Bool) (tag : Nat)
    (quiet : ∀ a, ends (segOcc a) ≠ true)
    (only : ∀ i, i < 7 → ends (tokenEvent i) = true → i = tag)
    (yes : ends (tokenEvent tag) = true) (b : Boundary ends h k u) :
    tag < n ∧ u = tr.pos tag ∧ k = 0 := by
  obtain ⟨⟨x,hx,matched⟩,count⟩ := b
  obtain ⟨lt,rfl⟩ := uniquePosition tr (fun o => ends o = true) tag quiet only hx matched
  exact ⟨lt,rfl,count.symm.trans (boundaryAt tr ends tag quiet only yes lt).2⟩

private def word : Bool → Addr | false => slot | true => metadata
private def writePhase : Bool → Nat | false => 0 | true => 1
private def readPhase : Bool → Nat | false => 4 | true => 5

private theorem wordCases (member : p ∈ view.slotOf k) : ∃ b, p = word b := by
  obtain rfl | rfl := (show p = slot ∨ p = metadata by simpa [view, View.slotOf] using member)
  · exact ⟨false,rfl⟩
  · exact ⟨true,rfl⟩

private theorem emptyAccess (a : Agent) (p : Addr) (kd : AccessKind) (m : Mode) :
    ¬ (segOcc a).access p kd m := by cases kd <;> cases m <;> simp [segOcc,Occurrence.access]

private theorem writeUnique (tr : TokenTrace n h) (b : Bool) (wr : Writes h u (word b)) :
    u = tr.pos (writePhase b) := by
  obtain ⟨x,kd,m,hx,access,writing⟩ := wr
  refine (uniquePosition tr (fun o => ∃ k mode, o.access (word b) k mode ∧ k.writes = true)
    (writePhase b) ?_ ?_ hx ⟨kd,m,access,writing⟩).2
  · rintro a ⟨k,mo,seen,_⟩
    exact emptyAccess a _ k mo seen
  · rintro i hi ⟨k,mo,acc,w⟩
    interval_cases i <;> cases b <;> cases k <;> cases mo <;> first
      | rfl
      | contradiction
      | simp [word,tokenEvent,written,Occurrence.access,Event.accesses,
          slot,metadata,tail,head] at acc

private theorem readUnique (tr : TokenTrace n h) (b : Bool) (rd : Reads h u (word b)) :
    u = tr.pos (readPhase b) := by
  obtain ⟨x,m,hx,access⟩ := rd
  refine (uniquePosition tr (fun o => ∃ mode, o.access (word b) .load mode)
    (readPhase b) ?_ ?_ hx ⟨m,access⟩).2
  · rintro a ⟨mo,seen⟩; exact emptyAccess a _ _ mo seen
  · rintro i hi ⟨mo,acc⟩
    interval_cases i <;> cases b <;> cases mo <;> first
      | rfl
      | simp [word,tokenEvent,written,loadData,awaitTail,Occurrence.access,Event.accesses,
          slot,metadata,tail,head] at acc

private theorem putInfo (tr : TokenTrace n h) (b : Boundary view.putEnd h k i) :
    2 < n ∧ i = tr.pos 2 ∧ k = 0 :=
  boundaryInfo tr _ 2 (fun _ h => Bool.noConfusion h) putOnly rfl b

private theorem takeInfo (tr : TokenTrace n h) (b : Boundary view.takeEnd h k i) :
    6 < n ∧ i = tr.pos 6 ∧ k = 0 :=
  boundaryInfo tr _ 6 (fun _ h => Bool.noConfusion h) takeOnly rfl b

private theorem component (i : Nat) (order : i ≤ stop) : view.Component ends h 0 stop p i :=
  ⟨order,fun _ _ lt => False.elim (Nat.not_lt_zero _ lt)⟩

private theorem writer (tr : TokenTrace n h) (b : Bool) (hn : 2 < n) :
    view.PutComponent h 0 (tr.pos 2) (word b) (tr.pos (writePhase b)) ∧
    Writes h (tr.pos (writePhase b)) (word b) := by
  have lt : writePhase b < 2 := by cases b <;> decide
  have atW := tr.atEvent (writePhase b) (by omega)
  refine ⟨⟨component _ (Nat.le_of_lt (tr.ordered _ _ lt hn)),⟨_,atW,?_⟩⟩,⟨_,.store,.plain,atW,?_,rfl⟩⟩
  all_goals cases b <;> first | rfl | exact List.mem_cons_self

private theorem reader (tr : TokenTrace n h) (b : Bool) (hn : 6 < n) :
    view.TakeComponent h 0 (tr.pos 6) (word b) (tr.pos (readPhase b)) ∧
    Reads h (tr.pos (readPhase b)) (word b) := by
  have lt : readPhase b < 6 := by cases b <;> decide
  have atR := tr.atEvent (readPhase b) (by omega)
  refine ⟨⟨component _ (Nat.le_of_lt (tr.ordered _ _ lt hn)),⟨_,atR,?_⟩⟩,⟨_,.plain,atR,?_⟩⟩
  all_goals cases b <;> first | rfl | exact List.mem_cons_self

private theorem indexedPut (tr : TokenTrace n h) (b : Boundary view.putEnd h k i) :
    view.Put h k i := by
  obtain ⟨hn,rfl,rfl⟩ := putInfo tr b
  refine ⟨b,?_⟩
  intro p member; obtain ⟨b,rfl⟩ := wordCases member; exact ⟨_,writer tr b hn⟩

private theorem indexedTake (tr : TokenTrace n h) (b : Boundary view.takeEnd h k i) :
    view.Take h k i := by
  obtain ⟨hn,rfl,rfl⟩ := takeInfo tr b
  refine ⟨b,?_⟩
  intro p member; obtain ⟨b,rfl⟩ := wordCases member; exact ⟨_,reader tr b hn⟩

private theorem route (tr : TokenTrace n h) (b : Bool) (w : CellWrites) (hn : 6 < n) :
    Nonempty (TailHandoff (launch false w) h (word b) (tr.pos (writePhase b)) (tr.pos (readPhase b))) := by
  have wLt : writePhase b < 2 := by cases b <;> decide
  have rLt : 3 < readPhase b ∧ readPhase b < 6 := by cases b <;> decide
  have pub := tr.atEvent 2 (by omega)
  have obs := tr.atEvent 3 (by omega)
  have wr := tr.atEvent (writePhase b) (by omega)
  have rd := tr.atEvent (readPhase b) (by omega)
  refine ⟨{tail := tail, publication := tr.pos 2, poll := tr.pos 3, producer := sender, consumer := receiver,
           release := rel, acquire := acq, event := .wait (.word tail) .ge 1 acq,
           sender := ⟨(writer tr b (by omega)).2,by rw [pub]; rfl,.program (a := sender)
             ⟨tr.ordered _ _ wLt (by omega),by rw [wr]; cases b <;> rfl,by rw [pub]; rfl⟩⟩,
           observed := by rw [obs]; rfl, acquired := rfl,
           modes := ⟨rfl,rfl,trivial,trivial⟩,
           receiver := .program (a := receiver) ⟨tr.ordered _ _ rLt.1 (by omega),by rw [obs]; rfl,
             by rw [rd]; cases b <;> rfl⟩,
           source := ⟨tr.ordered _ _ (by decide) (by omega),?_⟩}⟩
  intro u x lo hi entry kd m acc
  rcases tr.covers u x entry with ⟨a,rfl⟩ | ⟨k,hk,rfl⟩
  · exact False.elim (emptyAccess a _ _ _ acc)
  · by_cases low : k ≤ 2
    · rcases Nat.lt_or_eq_of_le low with lt | rfl
      · have := tr.ordered _ _ lt (by omega : 2 < n); omega
      · omega
    · by_cases eq : k = 3
      · subst k; omega
      · have := tr.ordered _ _ (by omega : 3 < k) hk; omega

theorem allIndexedWords (w : CellWrites) (s : DistState) (tail0 : (s.cell tail).readAs .nat = some 0)
    (run : Run (launch false w) ((launch false w).initial s) sched final) :
    IndexedWords view (launch false w) final.history := by
  obtain ⟨n,⟨tr⟩⟩ := tokenTrace w s tail0 run
  refine ⟨fun _ _ => indexedPut tr,fun _ _ => indexedTake tr,?_,?_⟩
  · intro k takeStop take
    obtain ⟨hn,rfl,rfl⟩ := takeInfo tr take.1
    have b := boundaryAt tr view.putEnd 2 (fun _ h => Bool.noConfusion h) putOnly rfl (by omega)
    refine ⟨_,indexedPut tr b,?_⟩
    intro p hp j _ rd; obtain ⟨cell,rfl⟩ := wordCases hp
    obtain rfl := readUnique tr cell rd
    refine ⟨_,(writer tr cell (by omega)).1,?_,route tr cell w hn⟩
    intro u before _ wr; have := writeUnique tr cell wr; omega
  · intro old later i lt _ put; have := (putInfo tr put.1).2.2; omega

/-- Every prefix of every real schedule satisfies the two-cell contract. The
initial published count is zero; other initial cells and the write port are arbitrary. -/
theorem allSchedules (w : CellWrites) (s : DistState) (tail0 : (s.cell tail).readAs .nat = some 0) :
    view.Refines (launch false w) s :=
  refines_of_indexedWords (fun _ _ run => allIndexedWords w s tail0 run)

/-- The all-schedules proof and a completed run use the same concrete initial
state and cell implementation. The continuation records data 11 and metadata 29. -/
theorem concreteAllSchedules :
    let s := (DistState.single default).putCell tail (.of .nat 0)
    let l := launch false Tutorial01.putCellWrites
    view.Refines l s ∧ ∃ mid final, Run l (l.initial s) schedule final ∧ Complete final ∧
      Run l (l.initial s) (List.replicate 6 (.agent sender) ++ List.replicate 8 (.agent receiver)) mid ∧
      mid.pc receiver = some (.ready (4,[.of .nat 1,.of .nat 11,.of .nat 29])) ∧
      final.mem.cell slot = .of .nat 11 ∧ final.mem.cell metadata = .of .nat 29 := by
  dsimp only
  constructor
  · exact allSchedules _ _ (by rw [DistState.cell_putCell]; rfl)
  · obtain ⟨mid,final,run,done,_,reached,returned,values⟩ := execution false Tutorial01.putCellWrites
      ((DistState.single default).putCell tail (.of .nat 0))
    exact ⟨mid,final,run,done,reached,returned,values⟩

private def loadIsPlain (x : Occurrence) : Bool :=
  match x.event? with
  | some (_, .access .load _ m) => m == .plain
  | _ => true

/-- Regression for the original load-only observer. The very same complete run
uses a word wait and its only physical load events are plain data reads. -/
theorem oldObserverRejected (w : CellWrites) (p : Addr) (i j : Nat)
    (route : TailHandoff (launch false w) (history false) p i j) :
    route.event ≠ .access .load route.tail route.acquire := by
  intro load
  obtain ⟨x,atPoll,read⟩ := Option.bind_eq_some_iff.mp route.observed
  have allPlain : (history false).all loadIsPlain := by decide
  have plain := List.all_eq_true.mp allPlain x (List.mem_of_getElem? atPoll)
  simp [loadIsPlain,read,load] at plain
  have modes := route.modes
  rw [plain] at modes
  cases e : route.release <;> simp [e, Mode.Pairs] at modes

#print axioms concreteAllSchedules
#print axioms oldObserverRejected
#print axioms allIndexedWords
#print axioms allSchedules
end VeriTile.Tests.IndexQueueCells.Client
