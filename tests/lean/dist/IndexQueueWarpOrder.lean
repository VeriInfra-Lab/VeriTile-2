import tests.lean.dist.DeepEPChannel
import tests.lean.dist.IndexQueueCells

/-! The sender's part of an index-queue handoff (#651). Each warp or group
has its own program order. Crossing from one program to another requires the
documented collective's actual round, with an arrival from every roster member. -/
namespace VeriTile.Tests.IndexQueueWarpOrder
open VeriTile.Dist

/-- The two occurrences belong to a single program in the indicated order. -/
structure ProgramOrder (h : History) (a : Agent) (i j : Nat) : Prop where
  ordered : i < j
  first : (h[i]? >>= Occurrence.program?) = some a
  last : (h[j]? >>= Occurrence.program?) = some a

theorem ProgramOrder.hb (order : ProgramOrder h a i j) (l : Launch P) (p : Addr) :
    HB l h p i j := by
  obtain ⟨x, ix, owner⟩ := Option.bind_eq_some_iff.mp order.first
  obtain ⟨y, jy, same⟩ := Option.bind_eq_some_iff.mp order.last
  exact .single ⟨x, y, ix, jy, order.ordered, .inl ⟨a, owner, same⟩⟩

private theorem roundHB {l : Launch P} (round : RoundEdge l h p i j) : HB l h p i j := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lt, first, last, _⟩ := id round
  obtain ⟨x, ix, _⟩ := Option.bind_eq_some_iff.mp first
  obtain ⟨y, jy, _⟩ := Option.bind_eq_some_iff.mp last
  exact .single ⟨x, y, ix, jy, lt, .inr (.inl round)⟩

/-- Program order to an arrival, the completed collective round, and program
order from its wait. Concatenation models consecutive warp and group rounds. -/
inductive LocalPath (l : Launch P) (h : History) (p : Addr) : Nat → Nat → Prop where
  | program : ProgramOrder h a i j → LocalPath l h p i j
  | round : RoundEdge l h p i j → LocalPath l h p i j
  | trans : LocalPath l h p i j → LocalPath l h p j k → LocalPath l h p i k

theorem LocalPath.hb (path : LocalPath l h p i j) : HB l h p i j := by
  induction path with
  | program po => exact po.hb _ _
  | round r => exact roundHB r
  | trans _ _ left right => exact left.trans right

/-- The particular publisher has been identified by the caller. No assumption
about which lane wins a source-level election is hidden in this interface. -/
structure SenderPublication (l : Launch P) (h : History) (p : Addr)
    (write publication : Nat) (publisher : Agent) (tail : Addr) (release : Mode) : Prop where
  wrote : ∃ x kind mode, h[write]? = some x ∧ x.access p kind mode ∧ kind.writes = true
  stored : (h[publication]? >>= Occurrence.event?) = some (publisher, .access .store tail release)
  path : LocalPath l h p write publication

/-- A K28 sender-only client can use this conclusion without supplying a
receiver. Multiple publishers require a witness for the particular store used. -/
theorem SenderPublication.orders (s : SenderPublication l h p write publication publisher tail release) :
    HB l h p write publication := s.path.hb

/-- The receiver can use the same local-path rule after observing a pointer.
The read-from witness rules out an intervening update of the pointer. -/
theorem handoff {l : Launch P} {h : History} {p tail : Addr} {i publication poll j : Nat}
    {producer consumer : Agent} {release acquire : Mode}
    (sender : SenderPublication l h p i publication producer tail release)
    (obs : (h[poll]? >>= Occurrence.event?) = some (consumer, .access .load tail acquire))
    (pair : Mode.Pairs l.reach p producer consumer release acquire)
    (read : ReadsFrom h publication poll (.word tail)) (receiver : LocalPath l h p poll j) :
    HB l h p i j := by
  have sync : SyncEdge l.reach p (producer, .access .store tail release)
      (consumer, .access .load tail acquire) := by
    exact ⟨.word tail, release, acquire, rfl, rfl, pair⟩
  exact (sender.orders.trans (sync.hb_of_readsFrom sender.stored obs rfl read)).trans receiver.hb

/-- Reverse direction for reuse. A completed group of readers can acknowledge a
slot to a different sender. Its word wait has to read that acknowledgement. -/
theorem reuse {l : Launch P} {h : History} {p head : Addr} {j ack room i : Nat}
    {reader sender : Agent} {release acquire : Mode} {n : Nat}
    (readers : LocalPath l h p j ack)
    (stored : (h[ack]? >>= Occurrence.event?) = some (reader, .access .store head release))
    (waited : (h[room]? >>= Occurrence.event?) = some (sender, .wait (.word head) .ge n acquire))
    (modes : Mode.Pairs l.reach p reader sender release acquire)
    (source : ReadsFrom h ack room (.word head)) (writers : LocalPath l h p room i) :
    HB l h p j i := by
  have sync : SyncEdge l.reach p (reader, .access .store head release)
      (sender, .wait (.word head) .ge n acquire) :=
    ⟨.word head, release, acquire, rfl, rfl, modes⟩
  exact (readers.hb.trans (sync.hb_of_readsFrom stored waited rfl source)).trans writers.hb

/-- A tail publication for this cell, a concrete poll of its word, and the
receiver-side path. The release and acquire modes are checked for this cell. -/
structure TailHandoff (l : Launch P) (h : History) (p : Addr) (i j : Nat) where
  tail : Addr
  publication : Nat
  poll : Nat
  producer : Agent
  consumer : Agent
  release : Mode
  acquire : Mode
  sender : SenderPublication l h p i publication producer tail release
  observed : (h[poll]? >>= Occurrence.event?) = some (consumer, .access .load tail acquire)
  modes : Mode.Pairs l.reach p producer consumer release acquire
  source : ReadsFrom h publication poll (.word tail)
  receiver : LocalPath l h p poll j

theorem TailHandoff.hb (proof : TailHandoff l h p i j) : HB l h p i j :=
  handoff proof.sender proof.observed proof.modes proof.source proof.receiver

/-- The reverse edge uses the observed head acknowledgement and the next
sender's word wait. The two local paths may belong to different rosters. -/
structure HeadReuse (l : Launch P) (h : History) (p : Addr) (j i : Nat) where
  head : Addr
  acknowledgement : Nat
  room : Nat
  reader : Agent
  sender : Agent
  release : Mode
  acquire : Mode
  threshold : Nat
  readers : LocalPath l h p j acknowledgement
  stored : (h[acknowledgement]? >>= Occurrence.event?) = some (reader, .access .store head release)
  waited : (h[room]? >>= Occurrence.event?) = some (sender, .wait (.word head) .ge threshold acquire)
  modes : Mode.Pairs l.reach p reader sender release acquire
  source : ReadsFrom h acknowledgement room (.word head)
  writers : LocalPath l h p room i

theorem HeadReuse.hb (proof : HeadReuse l h p j i) : HB l h p j i :=
  reuse proof.readers proof.stored proof.waited proof.modes proof.source proof.writers

open VeriTile.Tests.IndexQueueCells

/-- Source-specific obligations over the positions of physical accesses,
word stores, polls, waits and collective rounds. A frontend that supplies
these for every reachable trace obtains the cell-set queue contract. -/
structure IndexedWords (v : View) (l : Launch P) (h : History) : Prop where
  written : ∀ k i, Boundary v.putEnd h k i → v.Put h k i
  taken : ∀ k j, Boundary v.takeEnd h k j → v.Take h k j
  tails : ∀ k takeStop, v.Take h k takeStop → ∃ putStop, v.Put h k putStop ∧
    ∀ p ∈ v.slotOf k, ∀ j, v.TakeComponent h k takeStop p j → Reads h j p → ∃ i,
      v.PutComponent h k putStop p i ∧
      (∀ u, i < u → u < j → ¬ Writes h u p) ∧ Nonempty (TailHandoff l h p i j)
  heads : ∀ old later putStop, old < later → (∃ p ∈ v.slotOf old, p ∈ v.slotOf later) →
    v.Put h later putStop → ∃ takeStop, v.Take h old takeStop ∧
      ∀ p ∈ v.slotOf old, p ∈ v.slotOf later → ∀ j i,
        v.TakeComponent h old takeStop p j → Reads h j p →
        v.PutComponent h later putStop p i → Writes h i p → Nonempty (HeadReuse l h p j i)

theorem refines_of_indexedWords {v : View} {l : Launch P} {s : DistState}
    (words : ∀ sched f, Run l (l.initial s) sched f → IndexedWords v l f.history) :
    v.Refines l s := by
  intro sched f run
  have certified := words sched f run
  refine ⟨certified.written, ?_, ?_⟩
  · intro k j boundary
    have take := certified.taken k j boundary
    obtain ⟨i, put, perCell⟩ := certified.tails k j take
    refine ⟨i, put, take, ?_⟩
    intro p hp t comp rd
    obtain ⟨w, own, clean, ⟨route⟩⟩ := perCell p hp t comp rd
    exact ⟨w, own, route.sender.wrote, DeepEPChannel.hb_lt route.hb, clean, route.hb⟩
  · intro old later putStop lt overlap put
    obtain ⟨takeStop, take, perCell⟩ := certified.heads old later putStop lt overlap put
    refine ⟨takeStop, lt, take, put, ?_⟩
    intro p earlier laterCell j i cj read ci write
    obtain ⟨route⟩ := perCell p earlier laterCell j i cj read ci write
    exact ⟨DeepEPChannel.hb_lt route.hb, route.hb⟩

#print axioms refines_of_indexedWords

namespace Example
open DeepEPChannel (slot tail rel acq)

private def cta : Cta := ⟨0,[0]⟩
private def writer : Agent := .group cta 0
private def publisher : Agent := .group cta 1
private def reader : Agent := .group ⟨1,[0]⟩ 0
private def phase : Counter := .phase cta 0
private def give : Mode := .atomic .cta .release
private def get : Mode := .atomic .cta .acquire
private def arrival (a : Agent) : Emission := ⟨a, .bump ⟨phase, .add, 1, give⟩, .noValue⟩
private def barrierWait : Emission := ⟨publisher, .wait phase .ge 2 get, .noValue⟩
private def publication : Emission := ⟨publisher, .access .store tail rel, .store (.of .nat 1)⟩
private def observation : Emission := ⟨reader, .access .load tail acq, .noValue⟩
private def dataCell (n : Nat) : Addr := {slot with offset := n}
private def entry : Set Addr := {dataCell 0, dataCell 1}

/-- Each warp executes one segment and its own nonempty group. In particular
the publisher cannot wait successfully before both warp arrivals. -/
private def group (a : Agent) (pc : Nat) : Next Nat :=
  if pc ≠ 0 then .finish else if a = writer then .emitGroup (arrival a) [] (fun _ => 1)
  else if a = publisher then .emitGroup (arrival a) [barrierWait, publication] (fun _ => 1)
  else .emitGroup observation [] (fun _ => 1)

private def result (n : Nat) : Addr := ⟨.global 1, "received", n⟩
private def receipts : Set Addr := {result 0, result 1}

private def writeSegment (a : Agent) (w : CellWrites) (pc : Nat) : Segment :=
  if a = writer ∧ pc = 0 then
    ⟨a, fun s => some (w.put (w.put s (dataCell 0) (.of .nat 40)) (dataCell 1) (.of .nat 41)),
        fun _ => ∅, fun _ => entry⟩
  else if a = reader ∧ pc = 1 then
    ⟨a, fun s => some (w.put (w.put s (result 0) (s.cell (dataCell 0))) (result 1) (s.cell (dataCell 1))),
        fun _ => entry, fun _ => receipts⟩
  else DeepEPChannel.emptySegment a

private def launch (w : CellWrites) : Launch Nat where
  program a := ⟨writeSegment a w, fun pc _ => group a pc⟩
  start a := if a = writer ∨ a = publisher ∨ a = reader then some 0 else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster c := if c = phase then some [writer, publisher] else none
  cells := w

private def history : History := [
  .segment writer ∅ entry, .issued writer (arrival writer),
  .segment publisher ∅ ∅, .issued publisher (arrival publisher),
  .issued publisher barrierWait, .issued publisher publication,
  .segment reader ∅ ∅, .issued reader observation, .segment reader entry receipts]

private theorem round (w : CellWrites) (p : Addr) : RoundEdge (launch w) history p 1 4 := by
  refine ⟨phase, writer, publisher, give, get, [writer,publisher], 1,
      trivial, ?_, by decide, by simp, by simp, rfl, by decide, by decide, rfl, rfl, ?_, ?_, ?_⟩
  · simp [launch]
  · simp [history, Occurrence.event?, arrival, Event.bump?]
  · constructor
    · decide
    · simp [history, Occurrence.event?, arrival, writer, publisher, Event.bump?]
  · exact ⟨rfl,rfl,by decide,by decide⟩

theorem senderOrders (w : CellWrites) (p : Addr) (hp : p ∈ entry) :
    SenderPublication (launch w) history p 0 5 publisher tail rel := by
  refine ⟨⟨_, .store, .plain, rfl, hp, rfl⟩, rfl, ?_⟩
  exact .trans (.program (a := writer) ⟨by decide, rfl, rfl⟩)
    (.trans (.round (round w p)) (.program (a := publisher) ⟨by decide, rfl, rfl⟩))

theorem readerHandoff (w : CellWrites) (p : Addr) (hp : p ∈ entry) :
    HB (launch w) history p 0 8 := by
  apply handoff (senderOrders w p hp) (consumer := reader) (poll := 7) (acquire := acq) rfl
  · exact ⟨rfl,rfl,trivial,trivial⟩
  · refine ⟨by decide, ?_⟩
    intro k x lo hi hx
    interval_cases k; simp [history] at hx
    subst x
    intro kd m access
    cases kd <;> cases m <;> simp_all [Occurrence.access]
  · exact .program (a := reader) ⟨by decide, rfl, rfl⟩

private def advanceSegment (w : CellWrites) (s : Config Nat) (a : Agent) (pc : Nat)
    (m : DistState) : Config Nat :=
  let seg := writeSegment a w pc
  {s with mem := m, history := s.history ++ [.segment a (seg.reads s.mem) (seg.writes s.mem)],
          pc := Function.update s.pc a (group a pc).cursor}

private theorem segmentTurn (w : CellWrites) (s : Config Nat) (a : Agent) (pc : Nat) (m : DistState)
    (ready : s.pc a = some (.ready pc)) (owned : (writeSegment a w pc).agent = a)
    (access : ∀ p ∈ (writeSegment a w pc).reads s.mem ∪ (writeSegment a w pc).writes s.mem,
      AccessibleAt (launch w).symm a p ∧ ¬ InFlight s.trace p)
    (result : (writeSegment a w pc).run s.mem = some m) :
    step (launch w) s (.agent a) (advanceSegment w s a pc m) :=
  .segment ready rfl owned access result

private def issued (s : Config Nat) (a : Agent) (es : List Emission) (m : DistState) : Config Nat :=
  {s with mem := m, history := s.history ++ es.map (.issued a),
          pc := Function.update s.pc a (some (.ready 1))}

private def applyGroup (s : Machine) (a : Agent) (es : List Emission) (m : DistState) : Machine :=
  {s with mem := m, history := s.history ++ es.map (.issued a)}

private theorem issueTurn (w : CellWrites) (s : Config Nat) (a : Agent) (e : Emission)
    (es : List Emission) (m : DistState) (vs : List (Option VeriTile.Triton.MemCell))
    (ready : s.pc a = some (.waiting e es (fun _ => 1)))
    (owned : ∀ x ∈ e :: es, x.actor.within a)
    (steps : FireGroup (launch w) a s.toMachine (e :: es) (applyGroup s.toMachine a (e :: es) m) vs) :
    step (launch w) s (.agent a) (issued s a (e :: es) m) :=
  .fire ready owned steps

private def writeData (w : CellWrites) (s : DistState) :=
  w.put (w.put s (dataCell 0) (.of .nat 40)) (dataCell 1) (.of .nat 41)
private def copyData (w : CellWrites) (s : DistState) :=
  w.put (w.put s (result 0) (s.cell (dataCell 0))) (result 1) (s.cell (dataCell 1))

set_option maxHeartbeats 2000000 in
/-- The history used by the cross-warp proof is reachable, and the receiver's
last segment copies both actual cells to separate observed addresses. -/
theorem run (w : CellWrites) (s : DistState) :
    ∃ sched final, Run (launch w) ((launch w).initial s) sched final ∧
      final.history = history ∧ final.mem.cell (result 0) = .of .nat 40 ∧
      final.mem.cell (result 1) = .of .nat 41 := by
  let initial := (launch w).initial s
  let m := writeData w s
  let wseg := advanceSegment w initial writer 0 m
  let a := issued wseg writer [arrival writer] m
  let pseg := advanceSegment w a publisher 0 m
  let published := w.put m tail (.of .nat 1)
  let b := issued pseg publisher [arrival publisher, barrierWait, publication] published
  let rseg := advanceSegment w b reader 0 published
  let c := issued rseg reader [observation] published
  let final := advanceSegment w c reader 1 (copyData w published)
  refine ⟨_, final, .cons (segmentTurn w initial writer 0 m ?_ ?_ ?_ ?_)
    (.cons (issueTurn w wseg writer _ [] m [none] ?_ ?_ ?_)
    (.cons (segmentTurn w a publisher 0 m ?_ ?_ ?_ ?_)
    (.cons (issueTurn w pseg publisher _ [barrierWait, publication] published [none,none,none] ?_ ?_ ?_)
    (.cons (segmentTurn w b reader 0 published ?_ ?_ ?_ ?_)
    (.cons (issueTurn w rseg reader _ [] published [some (published.cell tail)] ?_ ?_ ?_)
    (.cons (segmentTurn w c reader 1 (copyData w published) ?_ ?_ ?_ ?_) (.nil _))))))),
    ?_, ?_, ?_⟩
  all_goals first | rfl | (solve | simp [initial, Launch.initial, launch, advanceSegment, issued, group,
      final, c, rseg, b, pseg, a, wseg, writer, publisher, reader, cta]) | skip
  case refine_7 =>
    exact .cons (by simp [arrival, Event.AccessibleBy, Event.accesses, Bump.accesses, phase])
      (by simp [arrival, Event.accesses, Bump.accesses, phase]) (by simp [PendingFence, wseg, initial, advanceSegment, Launch.initial])
      (.bump _ _ 0 (by intro _; rfl)) (.nil _)
  case refine_14 =>
    refine .cons ?_ ?_ ?_ (.bump _ _ 1 (by intro _; rfl))
      (.cons ?_ ?_ ?_ (.wait _ _ _ _ _ 2 rfl (Nat.le_refl 2))
      (.cons ?_ ?_ ?_ (.store _ _ _ _) (.nil _)))
    all_goals first
      | solve | simp [arrival, Event.AccessibleBy, Event.accesses, Bump.accesses, phase,
          barrierWait, publication, AccessibleAt, Accessible, launch, tail]
      | solve | simp [PendingFence, pseg, a, wseg, advanceSegment, issued, initial, Launch.initial]
      | exact DeepEPChannel.accessOK w publication (by simp [publication, Event.accesses, tail])
      | intro kd p mode member
        apply DeepEPChannel.notInFlight
        simp [Machine.trace, pseg, a, wseg, advanceSegment, issued, initial, Launch.initial,
          Occurrence.event?, arrival, barrierWait]
  case refine_21 =>
    refine .cons ?_ ?_ ?_ (.load _ _ _) (.nil _)
    · exact DeepEPChannel.accessOK w observation (by simp [observation, Event.accesses, tail])
    · intro kd p mode member
      apply DeepEPChannel.notInFlight
      simp [Machine.trace, rseg, b, pseg, a, wseg, advanceSegment, issued, initial, Launch.initial,
          Occurrence.event?, arrival, barrierWait, publication]
    · simp [PendingFence, rseg, b, pseg, a, wseg, advanceSegment, issued, initial, Launch.initial]
  all_goals first
    | solve | simp [arrival, barrierWait, publication, observation, DeepEPChannel.own]
    | solve | simp (disch := decide) [final, advanceSegment, copyData, published, m, writeData,
          CellWrites.read_other, CellWrites.read_same]
    | intro p mem
      constructor
      · apply DeepEPChannel.reachable
        simp [writeSegment, writer, publisher, reader, cta, DeepEPChannel.emptySegment, entry,
          receipts, dataCell, result, slot] at mem
        all_goals grind
      · apply DeepEPChannel.notInFlight
        simp [Machine.trace, c, rseg, b, pseg, a, wseg, advanceSegment, issued, initial,
            Launch.initial, Occurrence.event?, arrival, barrierWait, publication, observation]

/-- Two increments by the same warp can satisfy a numerical threshold without
giving the missing member's contribution to the collective round. -/
theorem repeatedArrivalFails (w : CellWrites) (p : Addr) :
    ¬ RoundEdge (launch w) (history.set 1 (.issued publisher (arrival publisher))) p 3 4 := by
  rintro ⟨counter, a, b, m, m', members, n, _, roster, _, _, _, _, positive,
      _, first, last, _, counts, _⟩
  change some (publisher, (arrival publisher).event) = _ at first
  cases first
  change (if phase = phase then some [writer,publisher] else none) = some members at roster
  simp at roster
  subst members
  have occurs := counts.2 writer (by simp)
  change n ≤ 0 at occurs
  omega

/-- An actual receiver observes both values after publication through a
different warp. The sender certificate itself has no receiver hypothesis. -/
theorem checkedHandoff (w : CellWrites) (s : DistState) :
    ∃ sched final, Run (launch w) ((launch w).initial s) sched final ∧
      (∀ p ∈ entry, HB (launch w) final.history p 0 8) ∧
      final.mem.cell (result 0) = .of .nat 40 ∧ final.mem.cell (result 1) = .of .nat 41 := by
  obtain ⟨sched, final, execution, hist, h0, h1⟩ := run w s
  exact ⟨sched, final, execution, fun p hp => hist ▸ readerHandoff w p hp, h0, h1⟩

#print axioms repeatedArrivalFails
#print axioms checkedHandoff
open VeriTile.Tests.IndexQueueCells

private noncomputable def view : View where
  writers _ _ a := a = writer
  readers _ _ a := a = reader
  cap := 1
  cap_pos := by decide
  slots _ := {dataCell 0, dataCell 1}
  slot_nonempty _ := ⟨_, Finset.mem_insert_self ..⟩
  putEnd o := match o with
    | .issued _ ⟨_, .access .store q _, _⟩ => q == tail
    | _ => false
  takeEnd o := by
    classical
    exact match o with
    | .segment a r _ => decide (a = reader ∧ dataCell 0 ∈ r)
    | _ => false

private theorem cells {p} : p ∈ view.slotOf k ↔ p ∈ entry := by
  simp [View.slotOf, view, entry]

private theorem bounds :
    Boundary view.putEnd history 0 5 ∧ Boundary view.takeEnd history 0 8 := by
  constructor
  · exact ⟨⟨_,rfl,rfl⟩,rfl⟩
  · constructor
    · refine ⟨_, rfl, ?_⟩
      simp [view, entry]
    · simp [history, view, entry]

private theorem noIntervening (hp : p ∈ entry) (lo : 0 < k) (hi : k < 8) :
    ¬ Writes history k p := by
  simp [entry] at hp
  rintro ⟨x,kd,mode,ev,access,writes⟩
  rcases hp with rfl | rfl <;> interval_cases k <;> simp [history] at ev <;> subst x <;>
    cases kd <;> cases mode <;>
    simp_all [Occurrence.access, Event.accesses, Bump.accesses, AccessKind.writes, arrival,
      barrierWait, phase, publication, observation, dataCell, tail, slot]

/-- The same real run satisfies the token-boundary interface, as well as the
cell-wise synchronization and final-state value checks. -/
theorem tokenHandoff (w : CellWrites) (s : DistState) :
    ∃ sched final, Run (launch w) ((launch w).initial s) sched final ∧
      view.Handoff (launch w) final.history 0 5 8 ∧
      final.mem.cell (result 0) = .of .nat 40 ∧ final.mem.cell (result 1) = .of .nat 41 := by
  obtain ⟨sched, final, execution, hist, h0, h1⟩ := run w s
  refine ⟨sched, final, execution, ?_, h0, h1⟩
  rw [hist]
  have wr : ∀ p ∈ view.slotOf 0,
      view.PutComponent history 0 5 p 0 ∧ Writes history 0 p := by
    intro p member
    exact ⟨⟨⟨by decide, by intro t old impossible; omega⟩, ⟨_, rfl, rfl⟩⟩,
      ⟨_, .store, .plain, rfl, cells.mp member, rfl⟩⟩
  have rd : ∀ p ∈ view.slotOf 0,
      view.TakeComponent history 0 8 p 8 ∧ Reads history 8 p := by
    intro p member
    exact ⟨⟨⟨le_rfl, by intro t old impossible; omega⟩, ⟨_, rfl, rfl⟩⟩,
      ⟨_, .plain, rfl, cells.mp member⟩⟩
  refine ⟨⟨bounds.1, fun p hp => ⟨0, wr p hp⟩⟩, ⟨bounds.2, fun p hp => ⟨8, rd p hp⟩⟩, ?_⟩
  intro p hp j comp read
  have last : j = 8 := by
    have stop := comp.1.1
    have member := cells.mp hp
    simp [entry] at member
    obtain ⟨x, mode, pos, access⟩ := read
    rcases member with rfl | rfl <;> interval_cases j <;> first
      | rfl
      | simp [history] at pos; subst x; cases mode <;>
          simp [Occurrence.access, Event.accesses, Bump.accesses, arrival, phase,
            barrierWait, publication, observation, dataCell, tail, slot] at access
  subst j
  exact ⟨0,(wr p hp).1,(wr p hp).2,by decide,
    fun _ lo hi => noIntervening (cells.mp hp) lo hi, readerHandoff w p (cells.mp hp)⟩

#print axioms tokenHandoff

/-- A later correct read cannot mask an extra, too-early read of the same
cell by the same participant. This control is at the history interface. -/
theorem earlyReadFails (w : CellWrites) :
    ¬ view.Handoff (launch w)
      (.issued reader ⟨reader, .access .load (dataCell 0) .plain, .noValue⟩ :: history) 0 6 9 := by
  let early := Occurrence.issued reader ⟨reader, .access .load (dataCell 0) .plain, .noValue⟩
  intro ok
  have member : dataCell 0 ∈ view.slotOf 0 := by simp [View.slotOf, view]
  have comp : view.TakeComponent (early :: history) 0 9 (dataCell 0) 0 :=
    ⟨⟨by decide, by intro t old impossible; omega⟩, ⟨_, rfl, rfl⟩⟩
  have rd : Reads (early :: history) 0 (dataCell 0) :=
    ⟨_, .plain, rfl, by simp [early, Occurrence.access, Event.accesses]⟩
  obtain ⟨_, _, _, impossible, _⟩ := ok.2.2 _ member 0 comp rd
  omega

#print axioms earlyReadFails

end Example
#print axioms Example.senderOrders
#print axioms Example.readerHandoff

end VeriTile.Tests.IndexQueueWarpOrder
