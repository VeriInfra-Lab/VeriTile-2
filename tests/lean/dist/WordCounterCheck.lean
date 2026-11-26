/- Documentation test of the current scope of `DetRaceFree` (#47, #54).
Written by the advisor on 2026-11-25 against main 89d5996c1; it still holds
after the 2026-11-25 fix of `Fire` (a word counter keeps returning its count).

Companion of the C3 counterexample (`RendezvousObservation`). The same three
programs, with the counter moved from a rendezvous object to a memory word, are
rejected by `DetRaceFree`: when the observer's wait fires between the two adds,
the wait and the later add are an unordered atomic pair on the word. So the
word form of the pattern does not reach the C3 candidate's conclusion. This
checks one launch; it does not prove C3 for word counters in general. -/
import VeriTile.Staging.Dist.JudgmentSpec

namespace VeriTile.Tests.WordObservation
open VeriTile.Dist
open VeriTile.Triton (MemCell)

def adderA : Agent := .cta ⟨0, [0]⟩
def adderB : Agent := .cta ⟨0, [1]⟩
def observer : Agent := .cta ⟨0, [2]⟩
def flag : Addr := ⟨.global 0, "flag", 0⟩
def cell : Addr := ⟨.global 0, "observed", 0⟩
def meet : Counter := .word flag
def mode : Mode := .atomic .sys .acqRel

inductive PC where
  | addStart
  | obsStart
  | got (v : MemCell)
  | done

def addEvent (a : Agent) : Emission := ⟨a, .bump ⟨meet, .add, 1, mode⟩, .noValue⟩
def waitEvent (a : Agent) : Emission := ⟨a, .wait meet .ge 1 mode, .noValue⟩
def storeEvent (a : Agent) (v : MemCell) : Emission := ⟨a, .access .store cell .plain, .store v⟩

def afterWait : List (Option MemCell) → PC
  | some v :: _ => .got v
  | _ => .done

def emptySegment (a : Agent) : Segment := ⟨a, some, fun _ => ∅, fun _ => ∅⟩

def nextOf (a : Agent) : PC → Next PC
  | .addStart => .emitGroup (addEvent a) [] (fun _ => .done)
  | .obsStart => .emitGroup (waitEvent a) [] afterWait
  | .got v => .emitGroup (storeEvent a v) [] (fun _ => .done)
  | .done => .finish

def launch (w : CellWrites) : Launch PC where
  program a := ⟨fun _ => emptySegment a, fun pc _ => nextOf a pc⟩
  start a := if a = adderA ∨ a = adderB then some .addStart
    else if a = observer then some .obsStart else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

theorem own (c : Agent) : c.within c := by
  cases c <;> simp [Agent.within, Agent.rankOf, Agent.cta?]

def segOcc (a : Agent) := Occurrence.segment a ∅ ∅

/-! ## A schedule prefix: adder A, the observer's wait, adder B -/

def addOpened (s : Config PC) (a : Agent) : Config PC :=
  { s with history := s.history ++ [segOcc a],
           pc := Function.update s.pc a (some (.waiting (addEvent a) [] (fun _ => .done))) }

def added (w : CellWrites) (s : Config PC) (a : Agent) (old : Nat) : Config PC :=
  { s with mem := w.put s.mem flag (.of .nat (old + 1)),
           history := s.history ++ [.issued a (addEvent a)],
           pc := Function.update s.pc a (some (.ready .done)) }

def waitOpened (s : Config PC) : Config PC :=
  { s with history := s.history ++ [segOcc observer],
           pc := Function.update s.pc observer
             (some (.waiting (waitEvent observer) [] afterWait)) }

def waited (s : Config PC) (n : Nat) : Config PC :=
  { s with history := s.history ++ [.issued observer (waitEvent observer)],
           pc := Function.update s.pc observer (some (.ready (.got (.of .nat n)))) }

theorem addHalf (w : CellWrites) (s : Config PC) (a : Agent) (old : Nat)
    (ready : s.pc a = some (.ready .addStart)) (clear : s.pending = [])
    (seen : ((addOpened s a).mem.cell flag).readAs .nat = some old)
    (free : ¬ InFlight (addOpened s a).trace flag) :
    Run (launch w) s [.agent a, .agent a] (added w (addOpened s a) a old) := by
  refine .cons (t := addOpened s a) (.segment ready rfl rfl (by simp [launch, emptySegment]) rfl) ?_
  refine .cons (t := added w (addOpened s a) a old)
    (.fire (s := addOpened s a) (a := a) (h := addEvent a) (t := []) (k := fun _ => .done)
      (values := [some (.of .nat old)]) (by simp [addOpened]) ?_ ?_) (.nil _)
  · simpa [addEvent] using own a
  · refine .cons ?_ ?_ ?_ (.bump _ _ old (fun _ => seen)) (.nil _)
    · intro k p m access
      simp [addEvent, Event.accesses, Bump.accesses, meet, SignalOp.kind] at access
      rcases access with ⟨_, rfl, _⟩
      exact ⟨trivial, Or.inr rfl⟩
    · intro k p m access
      simp [addEvent, Event.accesses, Bump.accesses, meet, SignalOp.kind] at access
      rcases access with ⟨_, rfl, _⟩
      exact free
    · simp [PendingFence, addOpened, clear]

theorem waitHalf (w : CellWrites) (s : Config PC) (n : Nat)
    (ready : s.pc observer = some (.ready .obsStart)) (clear : s.pending = [])
    (seen : ((waitOpened s).mem.cell flag).readAs .nat = some n) (pos : 1 ≤ n)
    (free : ¬ InFlight (waitOpened s).trace flag) :
    Run (launch w) s [.agent observer, .agent observer] (waited (waitOpened s) n) := by
  refine .cons (t := waitOpened s)
    (.segment ready rfl rfl (by simp [launch, emptySegment]) rfl) ?_
  refine .cons (t := waited (waitOpened s) n)
    (.fire (s := waitOpened s) (a := observer) (h := waitEvent observer) (t := [])
      (k := afterWait) (values := [some (.of .nat n)]) (by simp [waitOpened]) ?_ ?_) (.nil _)
  · simpa [waitEvent] using own observer
  · refine .cons ?_ ?_ ?_ (.wait _ _ _ _ _ n seen pos) (.nil _)
    · intro k p m access
      simp [waitEvent, Event.accesses, meet] at access
      rcases access with ⟨_, rfl, _⟩
      exact ⟨trivial, Or.inr rfl⟩
    · intro k p m access
      simp [waitEvent, Event.accesses, meet] at access
      rcases access with ⟨_, rfl, _⟩
      exact free
    · simp [PendingFence, waitOpened, clear]

theorem appendRuns {P : Type} {l : Launch P} {s t u : Config P} {xs ys : Schedule}
    (left : Run l s xs t) (right : Run l t ys u) : Run l s (xs ++ ys) u := by
  induction left with
  | nil => exact right
  | cons step _ ih => exact .cons step (ih right)

abbrev afterA (w : CellWrites) (s : DistState) : Config PC :=
  added w (addOpened ((launch w).initial s) adderA) adderA 0

abbrev afterWaitFired (w : CellWrites) (s : DistState) : Config PC :=
  waited (waitOpened (afterA w s)) 1

abbrev afterB (w : CellWrites) (s : DistState) : Config PC :=
  added w (addOpened (afterWaitFired w s) adderB) adderB 1

def prefixSchedule : Schedule :=
  [.agent adderA, .agent adderA] ++ ([.agent observer, .agent observer] ++
    [.agent adderB, .agent adderB])

theorem prefixRun (w : CellWrites) (s : DistState)
    (zero : (s.cell flag).readAs .nat = some 0) :
    Run (launch w) ((launch w).initial s) prefixSchedule (afterB w s) := by
  refine appendRuns (addHalf w _ adderA 0 ?_ rfl zero ?_)
    (appendRuns (waitHalf w _ 1 ?_ rfl ?_ (Nat.le_refl 1) ?_) (addHalf w _ adderB 1 ?_ rfl ?_ ?_))
  · simp [Launch.initial, launch]
  · simp [InFlight, Transfer.pending, Machine.trace, addOpened, Launch.initial, segOcc,
      Occurrence.event?]
  · simp [added, addOpened, Launch.initial, launch, Function.update, adderA, adderB, observer]
  · simp [waitOpened, added, addOpened, Launch.initial, w.read_same]
  · simp [InFlight, Transfer.pending, Machine.trace, waitOpened, added, addOpened,
      Launch.initial, segOcc, Occurrence.event?, addEvent]
  · simp [waited, waitOpened, added, addOpened, Launch.initial, launch, Function.update,
      adderA, adderB, observer]
  · simp [waited, waitOpened, added, addOpened, Launch.initial, w.read_same]
  · simp [InFlight, Transfer.pending, Machine.trace, waited, waitOpened, added, addOpened,
      Launch.initial, segOcc, Occurrence.event?, addEvent, waitEvent]

/-! ## The unordered atomic pair -/

def H : History :=
  [segOcc adderA, .issued adderA (addEvent adderA), segOcc observer,
    .issued observer (waitEvent observer), segOcc adderB, .issued adderB (addEvent adderB)]

theorem historyEq (w : CellWrites) (s : DistState) : (afterB w s).history = H := by
  simp [added, addOpened, waited, waitOpened, Launch.initial, H]

/-- The wait is a load, not a release: no happens-before edge leaves it for
another program's later occurrence. -/
theorem noEdgeFromWait (w : CellWrites) (p : Addr) (k : Nat) :
    ¬ DirectHB (launch w) H p 3 k := by
  rintro ⟨x, y, hx, hy, lt, po | round | delivery | sync | count⟩
  all_goals
    have hk : k = 4 ∨ k = 5 := by
      have bound := (List.getElem?_eq_some_iff.mp hy).1
      simp [H] at bound
      omega
    simp [H] at hx
    subst hx
  · rcases hk with rfl | rfl <;> simp [H] at hy <;> subst hy <;>
      simp [Occurrence.program?, segOcc, adderB, observer] at po
  · obtain ⟨c, _, _, _, _, members, _, _, roster, _⟩ := round
    simp [launch] at roster
  · obtain ⟨_, _, bad, _⟩ := delivery
    simp [Occurrence.event?, waitEvent] at bad
  · obtain ⟨a, b, c, m, ha, _, rel, _, _⟩ := sync
    simp [Occurrence.event?] at ha
    subst ha
    simp [waitEvent, Event.releaseOf?] at rel
  · obtain ⟨_, e, _, _, _, _, _, _, _, src, bump, _⟩ := count
    simp [H, Occurrence.event?] at src
    obtain ⟨_, rfl⟩ := src
    simp [waitEvent, Event.bump?] at bump

theorem race (w : CellWrites) : UnorderedAtomicRace (launch w) H := by
  refine ⟨3, 5, .issued observer (waitEvent observer), .issued adderB (addEvent adderB), flag,
    .load, .update, mode, mode, by decide, by simp [H], by simp [H], ?_, ?_, Or.inr rfl, ?_, ?_, ?_⟩
  · simp [Occurrence.access, waitEvent, Event.accesses, meet]
  · simp [Occurrence.access, addEvent, Event.accesses, Bump.accesses, meet, SignalOp.kind]
  · simp [Mode.AtomicFor, mode, Scope.covers]
  · intro hb
    obtain ⟨k, edge, _⟩ := Relation.TransGen.head'_iff.mp hb
    exact noEdgeFromWait w flag k edge
  · rintro ⟨discarded, _⟩
    simp [Occurrence.discardedAddAt, waitEvent] at discarded

/-- The word form of the observation pattern is not deterministic-race-free. -/
theorem word_launch_not_detRaceFree (w : CellWrites) (s : DistState)
    (zero : (s.cell flag).readAs .nat = some 0) : ¬ DetRaceFree (launch w) s := by
  rintro ⟨_, noRace⟩
  exact noRace _ _ (prefixRun w s zero) (historyEq w s ▸ race w)

#print axioms word_launch_not_detRaceFree

end VeriTile.Tests.WordObservation

/-! ## The same judgment on a one-way signal with two rounds

This part is about histories only and holds for every launch. A producer adds
to a word twice and discards both results; a consumer waits for `ge 1`, then
for `ge 2`. The first wait and the second add are an unordered atomic pair, so
a launch that can produce this history is not `DetRaceFree`, although the
threshold stays enabled (C2) and the consumer may ignore the value it read. -/

namespace VeriTile.Tests.StreamingRounds
open VeriTile.Dist

def add (a : Agent) (p : Addr) : Occurrence :=
  .issued a ⟨a, .bump ⟨.word p, .add, 1, .atomic .sys .acqRel⟩, .discardAddResult⟩

def waitGe (a : Agent) (p : Addr) (n : Nat) : Occurrence :=
  .issued a ⟨a, .wait (.word p) .ge n (.atomic .sys .acqRel), .noValue⟩

theorem direct_lt {P : Type} {l : Launch P} {h p i j} (e : DirectHB l h p i j) : i < j :=
  e.choose_spec.choose_spec.2.2.1

theorem hb_lt {P : Type} {l : Launch P} {h p i j} (e : HB l h p i j) : i < j := by
  induction e with
  | single edge => exact direct_lt edge
  | tail _ edge ih => exact lt_trans ih (direct_lt edge)

theorem two_rounds_unordered {P : Type} (l : Launch P) (producer consumer : Agent)
    (apart : producer ≠ consumer) (flag : Addr) :
    UnorderedAtomicRace l
      [add producer flag, waitGe consumer flag 1, add producer flag, waitGe consumer flag 2] := by
  refine ⟨1, 2, waitGe consumer flag 1, add producer flag, flag, .load, .update,
    .atomic .sys .acqRel, .atomic .sys .acqRel, by decide, rfl, rfl, ?_, ?_, Or.inr rfl,
    ?_, ?_, ?_⟩
  · simp [waitGe, Occurrence.access, Event.accesses]
  · simp [add, Occurrence.access, Event.accesses, Bump.accesses, SignalOp.kind]
  · simp [Mode.AtomicFor, Scope.covers]
  · intro path
    cases path with
    | tail prev last => have := hb_lt prev; have := direct_lt last; omega
    | single edge =>
      obtain ⟨x, y, hx, hy, _, po | round | delivery | sync | count⟩ := edge
      all_goals simp at hx hy; subst x; subst y
      · simp [add, waitGe, Occurrence.program?] at po
        exact apart po
      · obtain ⟨c, _, _, _, _, _, _, kind, _, _, _, _, _, _, _, src, _⟩ := round
        simp [waitGe, Occurrence.event?] at src
      · obtain ⟨_, _, bad, _⟩ := delivery
        simp [waitGe, Occurrence.event?] at bad
      · obtain ⟨a, b, _, _, ha, _, rel, _, _⟩ := sync
        simp [waitGe, Occurrence.event?] at ha
        subst ha
        simp [Event.releaseOf?] at rel
      · obtain ⟨_, e, _, _, _, _, _, _, _, src, bump, _⟩ := count
        simp [waitGe, Occurrence.event?] at src
        obtain ⟨_, rfl⟩ := src
        simp [Event.bump?] at bump
  · rintro ⟨discarded, _⟩
    simp [waitGe, Occurrence.discardedAddAt] at discarded

#print axioms two_rounds_unordered

/-! The store form, as a ring-buffer tail is published: the producer stores the
tail with a release store, the consumer reads it with an acquire load, and the
producer stores a new tail. The load and the second store are an unordered
atomic pair. -/

def publish (a : Agent) (p : Addr) : Occurrence :=
  .issued a ⟨a, .access .store p (.atomic .sys .release), .noValue⟩

def readTail (a : Agent) (p : Addr) : Occurrence :=
  .issued a ⟨a, .access .load p (.atomic .sys .acquire), .noValue⟩

theorem tail_republished_unordered {P : Type} (l : Launch P) (producer consumer : Agent)
    (apart : producer ≠ consumer) (tail : Addr) :
    UnorderedAtomicRace l [publish producer tail, readTail consumer tail, publish producer tail] := by
  refine ⟨1, 2, readTail consumer tail, publish producer tail, tail, .load, .store,
    .atomic .sys .acquire, .atomic .sys .release, by decide, rfl, rfl, ?_, ?_, Or.inr rfl,
    ?_, ?_, ?_⟩
  · simp [readTail, Occurrence.access, Event.accesses]
  · simp [publish, Occurrence.access, Event.accesses]
  · simp [Mode.AtomicFor, Scope.covers]
  · intro path
    cases path with
    | tail prev last => have := hb_lt prev; have := direct_lt last; omega
    | single edge =>
      obtain ⟨x, y, hx, hy, _, po | round | delivery | sync | count⟩ := edge
      all_goals simp at hx hy; subst x; subst y
      · simp [publish, readTail, Occurrence.program?] at po
        exact apart po
      · obtain ⟨c, _, _, _, _, _, _, kind, _, _, _, _, _, _, _, src, _⟩ := round
        simp [readTail, Occurrence.event?] at src
      · obtain ⟨_, _, bad, _⟩ := delivery
        simp [readTail, Occurrence.event?] at bad
      · obtain ⟨a, b, _, _, ha, _, rel, _, _⟩ := sync
        simp [readTail, Occurrence.event?] at ha
        subst ha
        simp [Event.releaseOf?, AccessKind.writes] at rel
      · obtain ⟨_, e, _, _, _, _, _, _, _, src, bump, _⟩ := count
        simp [readTail, Occurrence.event?] at src
        obtain ⟨_, rfl⟩ := src
        simp [Event.bump?] at bump
  · rintro ⟨discarded, _⟩
    simp [readTail, Occurrence.discardedAddAt] at discarded

#print axioms tail_republished_unordered

end VeriTile.Tests.StreamingRounds
