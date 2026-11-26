import tests.lean.dist.IndexQueueCells
import tests.lean.dist.DeepEPChannel
import tests.lean.dist.Tutorial01

namespace VeriTile.Tests.IndexQueueCells.Client
open VeriTile.Dist
open VeriTile.Triton (MemCell)
open VeriTile.Tests.DeepEPChannel (sender receiver slot tail head rel acq segOcc emptySegment own
  notInFlight appendRuns reachable)

def metadata : Addr := ⟨.global 1, "channel_src_idx_buffers", 0⟩
private def written (a : Agent) (p : Addr) (v : Nat) (m : Mode := .plain) : Emission :=
  ⟨a, .access .store p m, .store (.of .nat v)⟩
private def loadData (p : Addr) : Emission := ⟨receiver, .access .load p .plain, .noValue⟩
private def awaitTail : Emission := ⟨receiver, .wait (.word tail) .ge 1 acq, .noValue⟩
private def second (wrongCell : Bool) := if wrongCell then slot else metadata

/-- This client sends one token per round, so the tail publication and the head
acknowledgement identify the logical boundaries. The row and its source index
are separate physical operations with independent scheduler choices. -/
def view : View where
  cap := 1
  cap_pos := by decide
  writers _ _ a := a = sender
  readers _ _ a := a = receiver
  slots _ := {slot, metadata}
  slot_nonempty _ := ⟨slot, by simp⟩
  putEnd x := x.event? == some (sender, .access .store tail rel)
  takeEnd x := x.event? == some (receiver, .access .store head rel)

private def emissions (wrongCell : Bool) (a : Agent) : List Emission :=
  if a = sender then [written sender slot 11, written sender metadata 29, written sender tail 1 rel]
  else if a = receiver then [awaitTail, loadData slot, loadData (second wrongCell), written receiver head 1 rel]
  else []

/-- The continuation records the actual values returned by Fire, in read order. -/
abbrev PC := Nat × List MemCell

private def next (ops : List Emission) (pc : PC) : Next PC :=
  match ops[pc.1]? with
  | none => .finish
  | some e => .emitGroup e [] (fun returned => (pc.1 + 1, pc.2 ++ returned.reduceOption))

def launch (wrongCell : Bool) (w : CellWrites) : Launch PC where
  program a := ⟨fun _ => emptySegment a, fun pc _ => next (emissions wrongCell a) pc⟩
  start a := if a = sender ∨ a = receiver then some (0, []) else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

private def afterEvent (s : Config PC) (a : Agent) (pc : PC) (e : Emission)
    (mem : DistState) (v : Option MemCell) : Config PC :=
  { s with
    mem := mem
    history := s.history ++ [segOcc a, .issued a e]
    pc := Function.update s.pc a (some (.ready (pc.1+1, pc.2 ++ v.toList))) }

private def opened (s : Config PC) (a : Agent) (ops : List Emission) (pc : PC) : Config PC :=
  { s with history := s.history ++ [segOcc a], pc := Function.update s.pc a (next ops pc).cursor }

private theorem one {wrong w} (s : Config PC) (a : Agent) (pc : PC) (e : Emission)
    (mem : DistState) (v : Option MemCell)
    (atPC : s.pc a = some (.ready pc)) (code : (emissions wrong a)[pc.1]? = some e)
    (actor : e.actor = a) (clear : s.pending = [])
    (access : e.event.AccessibleBy (launch wrong w).symm e.actor)
    (free : ∀ p, ¬ InFlight s.trace p)
    (fire : Fire (launch wrong w) (opened s a (emissions wrong a) pc).toMachine e mem s.pending v) :
    Run (launch wrong w) s [.agent a, .agent a] (afterEvent s a pc e mem v) := by
  refine .cons (t := opened s a (emissions wrong a) pc)
    (.segment atPC rfl rfl (by simp [launch, emptySegment]) rfl) ?_
  have values : [v].reduceOption = v.toList := by cases v <;> rfl
  have move := @step.fire _ (launch wrong w) (opened s a (emissions wrong a) pc)
    a e [] (fun returned => (pc.1+1, pc.2 ++ returned.reduceOption))
    ⟨mem, (s.history ++ [segOcc a]) ++ [.issued a e], s.pending⟩ [v]
    (by simp [opened, next, code, Next.cursor]) (by simpa [actor] using own a)
    (.cons access (by simpa [opened, Machine.trace, segOcc, Occurrence.event?] using
      (fun _ p _ _ => free p : ∀ kd p m, (kd,p,m) ∈ e.event.accesses → ¬ InFlight s.trace p))
      (by simp [PendingFence, opened, clear]) fire (.nil _))
  simpa [afterEvent, opened, values, Function.update_idem] using Run.cons move (Run.nil _)

private def finish (s : Config PC) (a : Agent) : Config PC :=
  {s with history := s.history ++ [segOcc a], pc := Function.update s.pc a none}

private theorem done {wrong w} (s : Config PC) (a : Agent) (pc : PC)
    (atPC : s.pc a = some (.ready pc)) (code : (emissions wrong a)[pc.1]? = none) :
    Run (launch wrong w) s [.agent a] (finish s a) := by
  have move := @step.segment _ (launch wrong w) s a pc (emptySegment a) s.mem
    atPC rfl rfl (by simp [emptySegment]) rfl
  simpa [finish, next, code, launch, segOcc, emptySegment, Next.cursor] using Run.cons move (Run.nil _)

def history (wrong : Bool) : History :=
  (emissions wrong sender).flatMap (fun e => [segOcc sender, .issued sender e]) ++
  (emissions wrong receiver).flatMap (fun e => [segOcc receiver, .issued receiver e]) ++
  [segOcc sender, segOcc receiver]

def schedule : Schedule :=
  List.replicate 6 (.agent sender) ++ List.replicate 8 (.agent receiver) ++ [.agent sender, .agent receiver]

section
variable (wrong : Bool) (w : CellWrites) (initial : DistState)

private def start := (launch wrong w).initial initial

private def after1 : Config PC :=
  let prev := start wrong w initial
  afterEvent prev sender (0, []) (written sender slot 11) (w.put prev.mem slot (.of .nat 11)) (none)

private def after2 : Config PC :=
  let prev := after1 wrong w initial
  afterEvent prev sender (1, []) (written sender metadata 29) (w.put prev.mem metadata (.of .nat 29)) (none)

private def after3 : Config PC :=
  let prev := after2 wrong w initial
  afterEvent prev sender (2, []) (written sender tail 1 rel) (w.put prev.mem tail (.of .nat 1)) (none)

private def after4 : Config PC :=
  let prev := after3 wrong w initial
  afterEvent prev receiver (0, []) (awaitTail) (prev.mem) (some (.of .nat 1))

private def after5 : Config PC :=
  let prev := after4 wrong w initial
  afterEvent prev receiver (1, [.of .nat 1]) (loadData slot) (prev.mem) (some (prev.mem.cell slot))

private def after6 : Config PC :=
  let prev := after5 wrong w initial
  afterEvent prev receiver (2, [.of .nat 1, prev.mem.cell slot]) (loadData (second wrong)) (prev.mem) (some (prev.mem.cell (second wrong)))

private def after7 : Config PC :=
  let prev := after6 wrong w initial
  afterEvent prev receiver (3, [.of .nat 1, prev.mem.cell slot, prev.mem.cell (second wrong)])
    (written receiver head 1 rel) (w.put prev.mem head (.of .nat 1)) none

private def endState := finish (finish (after7 wrong w initial) sender) receiver

private theorem runsToReads : Run (launch wrong w) (start wrong w initial)
    (List.replicate 6 (.agent sender) ++ List.replicate 8 (.agent receiver)) (after7 wrong w initial) := by
  have move1 : Run (launch wrong w) (start wrong w initial) [.agent sender, .agent sender] (after1 wrong w initial) := by
    apply one (pc := (0, [])) (e := written sender slot 11)
    · simp [start, Launch.initial, launch, sender, receiver]
    · rfl
    · rfl
    · rfl
    · intro kd p m member
      apply reachable _ _
      simp [written, Event.accesses] at member
      obtain ⟨_, rfl, _⟩ := member
      rfl
    · intro p
      apply notInFlight
      simp [start, Machine.trace, Launch.initial, Occurrence.event?, ]
    · exact .store _ _ _ _
  have move2 : Run (launch wrong w) (after1 wrong w initial) [.agent sender, .agent sender] (after2 wrong w initial) := by
    apply one (pc := (1, [])) (e := written sender metadata 29)
    · simp [after1, start, afterEvent, Launch.initial, launch, Function.update, sender, receiver]
    · rfl
    · rfl
    · rfl
    · intro kd p m member
      apply reachable _ _
      simp [written, Event.accesses] at member
      obtain ⟨_, rfl, _⟩ := member
      rfl
    · intro p
      apply notInFlight
      simp [after1, start, afterEvent, Machine.trace, Launch.initial, segOcc, Occurrence.event?, written, ]
    · exact .store _ _ _ _
  have move3 : Run (launch wrong w) (after2 wrong w initial) [.agent sender, .agent sender] (after3 wrong w initial) := by
    apply one (pc := (2, [])) (e := written sender tail 1 rel)
    · simp [after2, after1, start, afterEvent, Launch.initial, launch, Function.update, sender, receiver]
    · rfl
    · rfl
    · rfl
    · intro kd p m member
      apply reachable _ _
      simp [written, Event.accesses] at member
      obtain ⟨_, rfl, _⟩ := member
      rfl
    · intro p
      apply notInFlight
      simp [after2, after1, start, afterEvent, Machine.trace, Launch.initial, segOcc, Occurrence.event?, written, ]
    · exact .store _ _ _ _
  have move4 : Run (launch wrong w) (after3 wrong w initial) [.agent receiver, .agent receiver] (after4 wrong w initial) := by
    apply one (pc := (0, [])) (e := awaitTail)
    · simp [after3, after2, after1, start, afterEvent, Launch.initial, launch, Function.update, sender, receiver]
    · rfl
    · rfl
    · rfl
    · intro kd p m member
      apply reachable _ _
      simp [awaitTail, Event.accesses] at member
      exact (member.2.1 ▸ rfl)
    · intro p
      apply notInFlight
      simp [after3, after2, after1, start, afterEvent, Machine.trace, Launch.initial, segOcc, Occurrence.event?, written, ]
    · exact .wait _ _ _ _ _ 1 (by simp [opened, Machine.count?, after3, afterEvent, CellWrites.read_same]) (Nat.le_refl 1)
  have move5 : Run (launch wrong w) (after4 wrong w initial) [.agent receiver, .agent receiver] (after5 wrong w initial) := by
    apply one (pc := (1, [.of .nat 1])) (e := loadData slot)
    · simp [after4, after3, after2, after1, start, afterEvent, Launch.initial, launch, Function.update, sender, receiver]
    · rfl
    · rfl
    · rfl
    · intro kd p m member
      apply reachable _ _
      simp [loadData, Event.accesses] at member
      obtain ⟨_, rfl, _⟩ := member
      rfl
    · intro p
      apply notInFlight
      simp [after4, after3, after2, after1, start, afterEvent, Machine.trace, Launch.initial, segOcc, Occurrence.event?, written, awaitTail]
    · exact .load _ _ _
  have move6 : Run (launch wrong w) (after5 wrong w initial) [.agent receiver, .agent receiver] (after6 wrong w initial) := by
    apply one (pc := (2, [.of .nat 1, (after5 wrong w initial).mem.cell slot])) (e := loadData (second wrong))
    · simp [after5, after4, after3, after2, after1, start, afterEvent, Launch.initial, launch, Function.update, sender, receiver]
    · rfl
    · rfl
    · rfl
    · intro kd p m member
      apply reachable _ _
      cases wrong <;> simp [loadData, second, Event.accesses] at member <;> obtain ⟨_, rfl, _⟩ := member <;> rfl
    · intro p
      apply notInFlight
      simp [after5, after4, after3, after2, after1, start, afterEvent, Machine.trace, Launch.initial, segOcc, Occurrence.event?, written, awaitTail, loadData]
    · exact .load _ _ _
  have move7 : Run (launch wrong w) (after6 wrong w initial) [.agent receiver, .agent receiver] (after7 wrong w initial) := by
    apply one (pc := (3, [.of .nat 1, (after6 wrong w initial).mem.cell slot, (after6 wrong w initial).mem.cell (second wrong)])) (e := written receiver head 1 rel)
    · simp [after6, after5, after4, after3, after2, after1, start, afterEvent, Launch.initial, launch, Function.update, sender, receiver, second]
    · rfl
    · rfl
    · rfl
    · intro kd p m member
      apply reachable _ _
      simp [written, Event.accesses] at member
      obtain ⟨_, rfl, _⟩ := member
      rfl
    · intro p
      apply notInFlight
      simp [after6, after5, after4, after3, after2, after1, start, afterEvent, Machine.trace, Launch.initial, segOcc, Occurrence.event?, written, awaitTail, loadData]
    · exact .store _ _ _ _
  have actual := appendRuns move1 (appendRuns move2 (appendRuns move3
    (appendRuns move4 (appendRuns move5 (appendRuns move6 move7)))))
  exact actual

private theorem realized : Run (launch wrong w) (start wrong w initial) schedule (endState wrong w initial) := by
  unfold schedule endState
  have endS : Run (launch wrong w) (after7 wrong w initial) [.agent sender] (finish (after7 wrong w initial) sender) := by
    apply done (pc := (3, []))
    · simp [after7, after6, after5, after4, after3, afterEvent, Function.update, sender, receiver]
    · rfl
  have endR : Run (launch wrong w) (finish (after7 wrong w initial) sender) [.agent receiver] (finish (finish (after7 wrong w initial) sender) receiver) := by
    apply done (pc := (4, [.of .nat 1, (after6 wrong w initial).mem.cell slot, (after6 wrong w initial).mem.cell (second wrong)]))
    · simp [finish, after7, afterEvent, Function.update, sender, receiver]
    · rfl
  have actual := appendRuns (runsToReads wrong w initial) (appendRuns endS endR)
  exact actual

end

private theorem row_ne_metadata : slot ≠ metadata := by decide
private theorem row_ne_tail : slot ≠ tail := by decide
private theorem metadata_ne_tail : metadata ≠ tail := by decide
private theorem row_ne_head : slot ≠ head := by decide
private theorem metadata_ne_head : metadata ≠ head := by decide

/-- The failed experiment changes only the source of the second load.
The continuation records its wrong value even though both physical stores and
both endpoint publications still execute. -/
theorem execution (wrong : Bool) (w : CellWrites) (initial : DistState) :
    ∃ mid final, Run (launch wrong w) ((launch wrong w).initial initial) schedule final ∧
      Complete final ∧ final.history = history wrong ∧
      Run (launch wrong w) ((launch wrong w).initial initial)
        (List.replicate 6 (.agent sender) ++ List.replicate 8 (.agent receiver)) mid ∧
      mid.pc receiver = some (.ready (4, [.of .nat 1, .of .nat 11,
        .of .nat (if wrong then 11 else 29)])) ∧
      final.mem.cell slot = .of .nat 11 ∧ final.mem.cell metadata = .of .nat 29 := by
  refine ⟨after7 wrong w initial, endState wrong w initial, realized .., ⟨?_,
    by simp [endState, finish, after7, afterEvent, after6, after5, after4, after3, after2,
      after1, start, Launch.initial]⟩, rfl, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases hs : a = sender
    · subst a; rfl
    by_cases hr : a = receiver
    · subst a; rfl
    simp [endState, finish, after7, after6, after5, after4, after3, after2, after1, afterEvent,
      start, Launch.initial, launch, Function.update, hs, hr]
  · exact (runsToReads wrong w initial)
  all_goals cases wrong <;>
    simp [endState, finish, after7, after6, after5, after4, after3, after2, after1, afterEvent, start,
      Launch.initial, second, CellWrites.read_same, CellWrites.read_other, row_ne_metadata,
      row_ne_tail, metadata_ne_tail, row_ne_head, metadata_ne_head,
      ]

private theorem inSlot {p} (hp : p ∈ view.slotOf 0) : p = slot ∨ p = metadata := by
  simpa [View.slotOf, view] using hp

private theorem firstComponent {ends h stop p i} (hi : i ≤ stop) :
    view.Component ends h 0 stop p i :=
  ⟨hi, by intro t _ ht; omega⟩

private theorem putBoundary (wrong) : Boundary view.putEnd (history wrong) 0 5 :=
  ⟨⟨_, rfl, rfl⟩, rfl⟩
private theorem takeBoundary (wrong) : Boundary view.takeEnd (history wrong) 0 13 :=
  ⟨⟨_, rfl, rfl⟩, by cases wrong <;> rfl⟩

private def cellPos (p : Addr) := if p = slot then 1 else 3

private theorem positions {p} (hp : p ∈ view.slotOf 0) :
    Writes (history false) (cellPos p) p ∧ Reads (history false) (cellPos p + 8) p := by
  rcases inSlot hp with rfl | rfl
  all_goals
    constructor
    · exact ⟨_, .store, .plain, rfl, by simp [Occurrence.access, written, Event.accesses], rfl⟩
    · exact ⟨_, .plain, rfl, by simp [Occurrence.access, loadData, second, Event.accesses]⟩

private theorem po {P} (l : Launch P) {p i j a x y} (hi : (history false)[i]? = some x)
    (hj : (history false)[j]? = some y) (xp : x.program? = some a) (yp : y.program? = some a)
    (order : i < j) : HB l (history false) p i j :=
  .single ⟨x, y, hi, hj, order, Or.inl ⟨a, xp, yp⟩⟩

private theorem publishedBeforeRead (w : CellWrites) (p : Addr) :
    HB (launch false w) (history false) p 5 7 := by
  apply SyncEdge.hb_of_readsFrom
    (rel := (sender, .access .store tail rel)) (acq := (receiver, .wait (.word tail) .ge 1 acq))
    (c := .word tail) (m := rel)
  · exact ⟨.word tail, rel, acq, rfl, rfl, by simp [Mode.Pairs, rel, acq, Scope.covers, MemOrder.acquires, MemOrder.releases]⟩
  · rfl
  · rfl
  · rfl
  · refine ⟨by decide, ?_⟩
    intro k x lo hi lookup
    have : k = 6 := by omega
    subst k
    cases lookup
    intro kd m seen
    cases kd <;> cases m <;> simp [Occurrence.access, segOcc] at seen

private theorem cleanBetween {p} (hp : p ∈ view.slotOf 0) (u : Nat)
    (lo : cellPos p < u) (hi : u < cellPos p + 8) : ¬ Writes (history false) u p := by
  rintro ⟨x, kd, m, hx, access, write⟩
  rcases inSlot hp with rfl | rfl
  · change 1 < u at lo
    change u < 9 at hi
    have : u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5 ∨ u = 6 ∨ u = 7 ∨ u = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases hx; cases kd <;> cases m <;>
      simp_all [Occurrence.access, segOcc, Event.accesses, written, awaitTail, slot, metadata, tail]
  · change 3 < u at lo
    change u < 11 at hi
    have : u = 4 ∨ u = 5 ∨ u = 6 ∨ u = 7 ∨ u = 8 ∨ u = 9 ∨ u = 10 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases hx; cases kd <;> cases m <;>
      simp_all [Occurrence.access, segOcc, Event.accesses, written, awaitTail, loadData, slot, metadata, tail]

private theorem readPosition {p j} (hp : p ∈ view.slotOf 0) (rd : Reads (history false) j p) :
    j = cellPos p + 8 := by
  obtain ⟨x, m, hx, access⟩ := rd
  have bound : j < 16 := (List.getElem_of_getElem? hx).choose
  rcases inSlot hp with rfl | rfl
  all_goals interval_cases j <;> cases hx <;> first | rfl |
    (cases m <;> simp [Occurrence.access, segOcc, written, loadData, awaitTail, Event.accesses,
      slot, metadata, tail, head, second] at access)

theorem handoff (w : CellWrites) : view.Handoff (launch false w) (history false) 0 5 13 := by
  have both (p : Addr) (hp : p ∈ view.slotOf 0) :
      view.PutComponent (history false) 0 5 p (cellPos p) ∧
      view.TakeComponent (history false) 0 13 p (cellPos p + 8) := by
    rcases inSlot hp with rfl | rfl
    all_goals
      constructor <;> exact ⟨firstComponent (by decide), ⟨_, rfl, rfl⟩⟩
  refine ⟨⟨putBoundary _, fun p hp => ⟨_, (both p hp).1, (positions hp).1⟩⟩,
    ⟨takeBoundary _, fun p hp => ⟨_, (both p hp).2, (positions hp).2⟩⟩, ?_⟩
  intro p hp j _ reads
  obtain rfl := readPosition hp reads
  refine ⟨cellPos p, (both p hp).1, (positions hp).1, by omega, cleanBetween hp, ?_⟩
  have sync := publishedBeforeRead w p
  rcases inSlot hp with rfl | rfl
  all_goals
    exact (po _ (a := sender) (j := 5) rfl rfl rfl rfl (by decide)).trans
      (sync.trans (po _ (a := receiver) (i := 7) rfl rfl rfl rfl (by decide)))

private def plainData (kind : AccessKind) (x : Occurrence) : Bool :=
  match x.event? with
  | some (_, .access kd p .plain) => kd == kind && (p == slot || p == metadata)
  | _ => false

/-- The old event count would report two entries. Only one token completed. -/
theorem countControl : (history false).countP (plainData .store) = 2 ∧
    (history false).countP view.putEnd = 1 ∧ ¬ ∃ stop, view.Put (history false) 1 stop := by
  refine ⟨rfl, rfl, ?_⟩
  rintro ⟨_, b, _⟩
  have wrong := b.lt_count
  exact (Nat.lt_irrefl 1) wrong

private theorem metadataNeverRead (i : Nat) : ¬ Reads (history true) i metadata := by
  rintro ⟨x, m, hx, access⟩
  have member := List.mem_of_getElem? hx
  simp only [history, emissions, if_pos, receiver, sender, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append] at member
  change x ∈ [segOcc sender, .issued sender (written sender slot 11),
    segOcc sender, .issued sender (written sender metadata 29), segOcc sender,
    .issued sender (written sender tail 1 rel), segOcc receiver, .issued receiver awaitTail,
    segOcc receiver, .issued receiver (loadData slot), segOcc receiver, .issued receiver (loadData slot),
    segOcc receiver, .issued receiver (written receiver head 1 rel), segOcc sender, segOcc receiver] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases m <;> simp [Occurrence.access, segOcc, written, loadData, awaitTail,
    Event.accesses, metadata, slot, tail, head] at access

/-- Both boundary markers still occur, yet the duplicate row read omits metadata. -/
theorem wrongCellRejected (w : CellWrites) :
    Boundary view.putEnd (history true) 0 5 ∧ Boundary view.takeEnd (history true) 0 13 ∧
    ¬ view.Handoff (launch true w) (history true) 0 5 13 := by
  refine ⟨putBoundary _, takeBoundary _, ?_⟩
  intro bad
  obtain ⟨i, _, rd⟩ := bad.2.1.2 metadata (by simp [View.slotOf, view])
  exact metadataNeverRead i rd

/-- The same physical execution also supplies two distinct single-cell tokens
for a capacity-two view. Its second put precedes the first take, legally,
because the physical addresses do not overlap. -/
private def separate : View where
  cap := 2
  cap_pos := by decide
  writers _ _ a := a = sender
  readers _ _ a := a = receiver
  slots j := {if j.val = 0 then slot else metadata}
  slot_nonempty _ := Finset.singleton_nonempty _
  putEnd := plainData .store
  takeEnd := plainData .load

theorem disjointReuse (w : CellWrites) : separate.Reuse (launch false w) (history false) 0 1 9 3 := by
  refine ⟨by decide, ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, ?_⟩, ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, ?_⟩, ?_⟩
  · intro p hp
    have : p = slot := by simpa [View.slotOf, separate] using hp
    subst p
    exact ⟨9, ⟨⟨by decide, by intro t _ lt; omega⟩, ⟨_, rfl, rfl⟩⟩, (positions (p := slot) (by simp [view, View.slotOf])).2⟩
  · intro p hp
    have : p = metadata := by simpa [View.slotOf, separate] using hp
    subst p
    refine ⟨3, ⟨⟨by decide, ?_⟩, ⟨_, rfl, rfl⟩⟩, (positions (p := metadata) (by simp [view, View.slotOf])).1⟩
    intro t old prev shared
    have : t = 0 := by omega
    subst t
    simp [View.slotOf, separate, Ne.symm row_ne_metadata] at shared
  · intro p earlier later
    have first : p = slot := by simpa [View.slotOf, separate] using earlier
    have snd : p = metadata := by simpa [View.slotOf, separate] using later
    exact (row_ne_metadata (first.symm.trans snd)).elim

/-- A later matching read cannot hide an additional, premature read by the
same receiver. This history-level control puts the extra read at position zero. -/
theorem prematureReadRejected (w : CellWrites) :
    let h := .issued receiver (loadData slot) :: history false
    ¬ view.Handoff (launch false w) h 0 6 14 := by
  dsimp only
  intro hand
  have covered := hand.2.2 slot (by simp [View.slotOf, view]) 0
    ⟨firstComponent (by decide), ⟨_, rfl, rfl⟩⟩
    ⟨_, .plain, rfl, by simp [Occurrence.access, loadData, Event.accesses]⟩
  obtain ⟨i, _, _, impossible, _⟩ := covered
  omega

/-- A data access by a nonparticipant is still a read of the physical cell.
It does not become part of this receiver's token just because it precedes the boundary. -/
theorem foreignRead :
    let x := Occurrence.issued sender ⟨sender, .access .load slot .plain, .noValue⟩
    Reads (x :: history false) 0 slot ∧ ¬ view.TakeComponent (x :: history false) 0 14 slot 0 := by
  refine ⟨⟨_, .plain, rfl, by simp [Occurrence.access, Event.accesses]⟩, ?_⟩
  rintro ⟨_, x, hx, role⟩
  cases hx
  exact (by decide : sender ≠ receiver) role

/-- Public importing client, with the native distributed-state write laws. -/
theorem concrete : ∃ final, Run (launch false Tutorial01.putCellWrites)
    ((launch false Tutorial01.putCellWrites).initial (DistState.single default)) schedule final ∧
    Complete final ∧ view.Handoff (launch false Tutorial01.putCellWrites) final.history 0 5 13 ∧
    separate.Reuse (launch false Tutorial01.putCellWrites) final.history 0 1 9 3 := by
  obtain ⟨_, final, run, done, historyEq, _⟩ := execution false Tutorial01.putCellWrites (DistState.single default)
  exact ⟨final, run, done, historyEq ▸ handoff _, historyEq ▸ disjointReuse _⟩

/-- The wrong-address program really completes. Its receiver records the row
value a second time, and the unchanged queue contract rejects that execution. -/
theorem concreteWrong : ∃ mid final, Run (launch true Tutorial01.putCellWrites)
    ((launch true Tutorial01.putCellWrites).initial (DistState.single default)) schedule final ∧
    Complete final ∧ Run (launch true Tutorial01.putCellWrites)
      ((launch true Tutorial01.putCellWrites).initial (DistState.single default))
      (List.replicate 6 (.agent sender) ++ List.replicate 8 (.agent receiver)) mid ∧
    mid.pc receiver = some (.ready (4, [.of .nat 1, .of .nat 11, .of .nat 11])) ∧
    ¬ view.Handoff (launch true Tutorial01.putCellWrites) final.history 0 5 13 := by
  obtain ⟨mid, final, run, done, hist, traceToReads, obs, _⟩ :=
    execution true Tutorial01.putCellWrites (DistState.single default)
  exact ⟨mid, final, run, done, traceToReads, obs, hist ▸ (wrongCellRejected _).2.2⟩

/-- A completed take boundary obliges the implementation to account for
every cell. Omitting metadata refutes the all-schedules contract. -/
theorem wrongDoesNotRefine (w : CellWrites) (initial : DistState) : ¬ view.Refines (launch true w) initial := by
  intro refines
  obtain ⟨_, final, ran, _, hist, _⟩ := execution true w initial
  obtain ⟨_, hand⟩ := (refines _ final ran).2.1 0 13 (hist ▸ takeBoundary true)
  rw [hist] at hand
  obtain ⟨i, _, rd⟩ := hand.2.1.2 metadata (by simp [View.slotOf, view])
  exact metadataNeverRead i rd

#print axioms wrongDoesNotRefine
#print axioms execution
#print axioms wrongCellRejected
#print axioms prematureReadRejected
#print axioms foreignRead
#print axioms concrete
#print axioms concreteWrong

end VeriTile.Tests.IndexQueueCells.Client
