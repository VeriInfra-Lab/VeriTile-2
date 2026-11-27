/- C3 after fix (a) (#47, #54, 2026-11-25): a gap on word counters.

Two CTAs each perform one `acqRel` fetch-add on the same memory word and use
its result: each stores the old value it got back into its own cell. Fix (a)
does not touch this, since a word counter still returns its count. Every
history orders the two adds: the earlier add is a release, the later one an
acquire that reads from it (no write of the word lies between them), so the
fourth disjunct of `DirectHB` gives happens-before. The launch is therefore
`SoundLaunch` and `DetRaceFree`, yet the two complete schedules leave (0, 1)
and (1, 0) in the two cells. So the staged C3 candidate
`detRaceFree_complete_eq_canonical` is still false after fix (a); the race
judgment orders the pair in whichever direction the schedule ran it.

The proofs follow the advisor's rendezvous counterexample of 2026-11-25.
`fetchAdd_c3_fails_concrete` instantiates it with the store's own `putCell`.
This file does not use the staged, unproved theorem. -/
import VeriTile.Staging.Dist.JudgmentSpec

namespace VeriTile.Tests.FetchAddObservation
open VeriTile.Dist
open VeriTile.Triton (MemCell)

def first : Agent := .cta ⟨0, [0]⟩
def second : Agent := .cta ⟨0, [1]⟩
def counter : Addr := ⟨.global 0, "counter", 0⟩
def slotOf (a : Agent) : Addr := ⟨.global 0, "old", if a = first then 0 else 1⟩
def mode : Mode := .atomic .sys .acqRel

inductive PC where
  | start
  | got (v : MemCell)
  | done

def addEvent (a : Agent) : Emission := ⟨a, .bump ⟨.word counter, .add, 1, mode⟩, .noValue⟩
def storeEvent (a : Agent) (v : MemCell) : Emission := ⟨a, .access .store (slotOf a) .plain, .store v⟩

/-- The continuation keeps the old value the fetch-add returned. -/
def afterAdd : List (Option MemCell) → PC
  | some v :: _ => .got v
  | _ => .done

def emptySegment (a : Agent) : Segment := ⟨a, some, fun _ => ∅, fun _ => ∅⟩

def nextOf (a : Agent) : PC → Next PC
  | .start => .emitGroup (addEvent a) [] afterAdd
  | .got v => .emitGroup (storeEvent a v) [] (fun _ => .done)
  | .done => .finish

def launch (w : CellWrites) : Launch PC where
  program a := ⟨fun _ => emptySegment a, fun pc _ => nextOf a pc⟩
  start a := if a = first ∨ a = second then some .start else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

theorem own (c : Agent) : c.within c := by
  cases c <;> simp [Agent.within, Agent.rankOf, Agent.cta?]

def segOcc (a : Agent) := Occurrence.segment a ∅ ∅

/-! ## The invariant of every reachable configuration -/

def Live (a : Agent) : Prop := a = first ∨ a = second

def Shape (x : Occurrence) : Prop :=
  (∃ a, x = segOcc a) ∨
    ∃ a, Live a ∧ (x = .issued a (addEvent a) ∨ ∃ v, x = .issued a (storeEvent a v))

structure Inv (s : Config PC) : Prop where
  pending : s.pending = []
  live : ∀ a, s.pc a ≠ none → Live a
  waiting : ∀ a h t k, s.pc a = some (.waiting h t k) → t = [] ∧
    (h = addEvent a ∨ ∃ v, h = storeEvent a v)
  history : ∀ x ∈ s.history, Shape x

theorem oneGroup {w : CellWrites} {a : Agent} {s f : Machine} {h : Emission} {values}
    (shape : h = addEvent a ∨ ∃ v, h = storeEvent a v)
    (group : FireGroup (launch w) a s [h] f values) :
    f.pending = s.pending ∧ f.history = s.history ++ [.issued a h] := by
  cases group with
  | cons _ _ _ fire rest =>
    cases rest
    rcases shape with rfl | ⟨v, rfl⟩ <;> cases fire <;> exact ⟨rfl, rfl⟩

theorem stepInv {w : CellWrites} {s f : Config PC} {c}
    (inv : Inv s) (move : step (launch w) s c f) : Inv f := by
  obtain ⟨pending, live, waiting, history⟩ := inv
  cases move with
  | @segment a pc seg mem atPC code owner access success =>
    subst seg
    refine ⟨pending, fun b hb => ?_, fun b h t k atB => ?_, fun x member => ?_⟩
    · by_cases eq : b = a
      · subst b; exact live _ (by simp [atPC])
      · exact live b (by simpa [Function.update, eq] using hb)
    · by_cases eq : b = a
      · subst b
        cases pc <;> simp [Function.update, launch, nextOf, Next.cursor] at atB
        · obtain ⟨rfl, rfl, rfl⟩ := atB; exact ⟨rfl, Or.inl rfl⟩
        · obtain ⟨rfl, rfl, rfl⟩ := atB; exact ⟨rfl, Or.inr ⟨_, rfl⟩⟩
      · exact waiting b h t k (by simpa [Function.update, eq] using atB)
    · rcases List.mem_append.mp member with old | new
      · exact history _ old
      · exact Or.inl ⟨a, List.mem_singleton.mp new⟩
  | @fire a h t k final values atPC owned events =>
    obtain ⟨rfl, shape⟩ := waiting _ _ _ _ atPC
    have alive := live a (by simp [atPC])
    obtain ⟨pend, hist⟩ := oneGroup shape events
    refine ⟨pend.trans pending, fun b hb => ?_, fun b h' t' k' atB => ?_, fun x member => ?_⟩
    · by_cases eq : b = a
      · subst b; exact alive
      · exact live b (by simpa [Function.update, eq] using hb)
    · by_cases eq : b = a
      · subst b; simp [Function.update] at atB
      · exact waiting b h' t' k' (by simpa [Function.update, eq] using atB)
    · change x ∈ final.history at member
      rw [hist] at member
      rcases List.mem_append.mp member with old | new
      · exact history _ old
      · have here := List.mem_singleton.mp new
        subst here
        rcases shape with rfl | ⟨v, rfl⟩
        · exact Or.inr ⟨a, alive, Or.inl rfl⟩
        · exact Or.inr ⟨a, alive, Or.inr ⟨v, rfl⟩⟩
  | deliver outstanding _ _ _ _ _ _ => simp [pending] at outstanding

theorem runInv {w : CellWrites} {start stop : Config PC} {schedule}
    (steps : Run (launch w) start schedule stop) (inv : Inv start) : Inv stop := by
  induction steps with
  | nil => exact inv
  | cons step _ ih => exact ih (stepInv inv step)

theorem initialInv (w : CellWrites) (s : DistState) : Inv ((launch w).initial s) := by
  refine ⟨rfl, fun a ha => ?_, fun a h t k atA => ?_, by simp [Launch.initial]⟩
  · by_cases h : a = first ∨ a = second
    · exact h
    · simp [Launch.initial, launch, h] at ha
  · cases hx : (launch w).start a <;> simp [Launch.initial, hx] at atA

/-! ## Race freedom: the two adds are ordered by reads-from -/

theorem slot_ne_counter (a : Agent) : slotOf a ≠ counter := by
  simp [slotOf, counter]

theorem counter_ne_slot (a : Agent) : counter ≠ slotOf a := fun h => slot_ne_counter a h.symm

theorem slot_inj {a b : Agent} (ha : Live a) (hb : Live b) (h : slotOf a = slotOf b) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | rfl | simp [slotOf, first, second] at h

theorem isAdd_dec (h : History) (i j : Nat) :
    (∃ k c, i < k ∧ k < j ∧ h[k]? = some (.issued c (addEvent c))) ∨
      ∀ k c, i < k → k < j → h[k]? ≠ some (.issued c (addEvent c)) := by
  by_cases e : ∃ k c, i < k ∧ k < j ∧ h[k]? = some (.issued c (addEvent c))
  · exact Or.inl e
  · push Not at e
    exact Or.inr e

/-- Any two adds of a history made of these shapes are ordered by happens-before. -/
theorem addsOrdered (w : CellWrites) (h : History) (shape : ∀ x ∈ h, Shape x) (q : Addr) :
    ∀ n i j a b, j - i = n → i < j → h[i]? = some (.issued a (addEvent a)) →
      h[j]? = some (.issued b (addEvent b)) → HB (launch w) h q i j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i j a b hn lt hi hj
    rcases isAdd_dec h i j with ⟨k, c, ik, kj, hk⟩ | none
    · exact (ih (k - i) (by omega) i k a c rfl ik hi hk).trans
        (ih (j - k) (by omega) k j c b rfl kj hk hj)
    · refine .single ⟨_, _, hi, hj, lt, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
      refine ⟨(a, (addEvent a).event), (b, (addEvent b).event), .word counter, mode, rfl, rfl, rfl,
        ⟨lt, fun k x ik kj hx kd m acc => ?_⟩, .word counter, mode, mode, rfl, rfl, ?_⟩
      · rcases shape x (List.mem_of_getElem? hx) with ⟨c, rfl⟩ | ⟨c, _, rfl | ⟨v, rfl⟩⟩
        · cases kd <;> cases m <;> simp [segOcc, Occurrence.access] at acc
        · exact absurd hx (none k c ik kj)
        · simp [Occurrence.access, storeEvent, Event.accesses] at acc
          exact absurd acc.2.1.symm (slot_ne_counter c)
      · simp [Mode.Pairs, mode, MemOrder.releases, MemOrder.acquires, Scope.covers]

theorem launchDetRaceFree (w : CellWrites) (s : DistState) : DetRaceFree (launch w) s := by
  have ordered : ∀ sched final, Run (launch w) ((launch w).initial s) sched final →
      ∀ i j x y p k k' m m', i < j → final.history[i]? = some x → final.history[j]? = some y →
        x.access p k m → y.access p k' m' → HB (launch w) final.history p i j := by
    intro sched final run i j x y p k k' m m' lt hx hy ax ay
    have inv := runInv run (initialInv w s)
    have po : ∀ a, x.program? = some a → y.program? = some a → HB (launch w) final.history p i j :=
      fun a px py => .single ⟨x, y, hx, hy, lt, Or.inl ⟨a, px, py⟩⟩
    rcases inv.history _ (List.mem_of_getElem? hx) with ⟨a, rfl⟩ | ⟨a, la, rfl | ⟨v, rfl⟩⟩
    · cases k <;> cases m <;> simp [segOcc, Occurrence.access] at ax
    · simp [Occurrence.access, addEvent, Event.accesses, Bump.accesses] at ax
      obtain ⟨-, rfl, -⟩ := ax
      rcases inv.history _ (List.mem_of_getElem? hy) with ⟨b, rfl⟩ | ⟨b, lb, rfl | ⟨v', rfl⟩⟩
      · cases k' <;> cases m' <;> simp [segOcc, Occurrence.access] at ay
      · exact addsOrdered w _ inv.history _ _ i j a b rfl lt hx hy
      · simp [Occurrence.access, storeEvent, Event.accesses] at ay
        exact absurd ay.2.1.symm (slot_ne_counter b)
    · simp [Occurrence.access, storeEvent, Event.accesses] at ax
      obtain ⟨-, rfl, -⟩ := ax
      rcases inv.history _ (List.mem_of_getElem? hy) with ⟨b, rfl⟩ | ⟨b, lb, rfl | ⟨v', rfl⟩⟩
      · cases k' <;> cases m' <;> simp [segOcc, Occurrence.access] at ay
      · simp [Occurrence.access, addEvent, Event.accesses, Bump.accesses] at ay
        exact absurd ay.2.1 (slot_ne_counter a)
      · simp [Occurrence.access, storeEvent, Event.accesses] at ay
        obtain rfl := slot_inj la lb ay.2.1
        exact po a rfl rfl
  constructor
  · intro sched final run
    rintro ⟨i, j, x, y, p, k, k', m, m', lt, hx, hy, ax, ay, _, _, nhb⟩
    exact nhb (ordered sched final run i j x y p k k' m m' lt hx hy ax ay)
  · intro sched final run
    rintro ⟨i, j, x, y, p, k, k', m, m', lt, hx, hy, ax, ay, _, _, nhb, _⟩
    exact nhb (ordered sched final run i j x y p k k' m m' lt hx hy ax ay)

theorem emptySound (a : Agent) : (emptySegment a).FootprintSound := by
  constructor
  · intro σ σ' h p _
    simp [emptySegment] at h
    subst h; rfl
  · intro σ σ' h
    simp [emptySegment] at h
    subst h
    exact ⟨⟨σ.view a, (DistState.setView_view _ _).symm⟩, fun _ _ _ => rfl⟩
  · intro s t _ hl
    refine ⟨rfl, rfl, ?_⟩
    intro s' hs
    simp [emptySegment] at hs
    subst hs
    exact ⟨t, rfl, fun _ h => False.elim h, hl⟩

theorem shapeOwner {x : Occurrence} (shape : Shape x) {b : Agent}
    (prog : x.program? = some b) : x.owner = b := by
  rcases shape with ⟨a, rfl⟩ | ⟨a, _, rfl | ⟨v, rfl⟩⟩ <;>
    (simp only [segOcc, Occurrence.program?, Option.some.injEq] at prog; subst prog; rfl)

theorem launchSound (w : CellWrites) : SoundLaunch (launch w) where
  localNext := fun _ _ _ _ _ _ => rfl
  footprints := fun a _ => emptySound a
  pidLength := by
    intro a c started isCta
    by_cases h : a = first ∨ a = second
    · rcases h with rfl | rfl <;> (cases isCta; rfl)
    · simp [launch, h] at started
  groups := by
    intro a pc s h t k emitted
    cases pc <;> simp [launch, nextOf] at emitted
    all_goals
      obtain ⟨rfl, rfl, _⟩ := emitted
      exact ⟨Or.inl rfl, by simpa [addEvent, storeEvent] using own a⟩
  nestedPath := by
    intro s sched f run x hx y hy a px py
    have inv := runInv run (initialInv w s)
    rw [shapeOwner (inv.history x hx) px, shapeOwner (inv.history y hy) py]
    exact Or.inl (own a)
  uniqueThreadPath := by
    intro s sched f run x hx y hy c g t ox oy a b px py
    have inv := runInv run (initialInv w s)
    exact (shapeOwner (inv.history x hx) px).symm.trans
      (ox.trans (oy.symm.trans (shapeOwner (inv.history y hy) py)))

/-! ## Two complete schedules -/

def opened (s : Config PC) (a : Agent) (pc : PC) : Config PC :=
  { s with history := s.history ++ [segOcc a], pc := Function.update s.pc a ((nextOf a pc).cursor) }

def fired (s : Config PC) (a : Agent) (e : Emission) (mem : DistState) (next : PC) : Config PC :=
  { s with mem := mem, history := s.history ++ [.issued a e],
           pc := Function.update s.pc a (some (.ready next)) }

def closed (s : Config PC) (a : Agent) : Config PC :=
  { s with history := s.history ++ [segOcc a], pc := Function.update s.pc a none }

def added (w : CellWrites) (s : Config PC) (a : Agent) (old : Nat) : Config PC :=
  fired (opened s a .start) a (addEvent a) (w.put s.mem counter (.of .nat (old + 1))) (.got (.of .nat old))

def stored (w : CellWrites) (s : Config PC) (a : Agent) (old : Nat) : Config PC :=
  fired (opened s a (.got (.of .nat old))) a (storeEvent a (.of .nat old))
    (w.put s.mem (slotOf a) (.of .nat old)) .done

abbrev afterTurn (w : CellWrites) (s : Config PC) (a : Agent) (old : Nat) : Config PC :=
  closed (stored w (added w s a old) a old) a

def turn (a : Agent) : Schedule := [.agent a, .agent a, .agent a, .agent a, .agent a]

theorem turnRun (w : CellWrites) (s : Config PC) (a : Agent) (old : Nat)
    (ready : s.pc a = some (.ready .start)) (clear : s.pending = [])
    (seen : (s.mem.cell counter).readAs .nat = some old)
    (free₁ : ¬ InFlight (opened s a .start).trace counter)
    (free₂ : ¬ InFlight (opened (added w s a old) a (.got (.of .nat old))).trace (slotOf a)) :
    Run (launch w) s (turn a) (afterTurn w s a old) := by
  refine .cons (t := opened s a .start) (.segment ready rfl rfl (by simp [launch, emptySegment]) rfl) ?_
  refine .cons (t := added w s a old)
    (.fire (s := opened s a .start) (a := a) (h := addEvent a) (t := []) (k := afterAdd)
      (values := [some (.of .nat old)]) (by simp [opened, nextOf, Next.cursor]) ?_ ?_) ?_
  · simpa [addEvent] using own a
  · refine .cons ?_ ?_ ?_ (.bump _ _ old (fun _ => seen)) (.nil _)
    · intro k p m access
      simp [addEvent, Event.accesses, Bump.accesses] at access
      rcases access with ⟨_, rfl, _⟩
      exact ⟨trivial, Or.inr rfl⟩
    · intro k p m access
      simp [addEvent, Event.accesses, Bump.accesses] at access
      rcases access with ⟨_, rfl, _⟩
      exact free₁
    · simp [PendingFence, opened, clear]
  refine .cons (t := opened (added w s a old) a (.got (.of .nat old)))
    (.segment (pc := PC.got (.of .nat old)) (by simp [added, fired, opened]) rfl rfl
      (by simp [launch, emptySegment]) rfl) ?_
  refine .cons (t := stored w (added w s a old) a old)
    (.fire (s := opened (added w s a old) a (.got (.of .nat old))) (a := a)
      (h := storeEvent a (.of .nat old)) (t := []) (k := fun _ => .done)
      (values := [none]) (by simp [opened, nextOf, Next.cursor]) ?_ ?_) ?_
  · simpa [storeEvent] using own a
  · refine .cons ?_ (fun _ p _ access => ?_) ?_ (.store _ _ _ _) (.nil _)
    · intro k p m access
      simp [storeEvent, Event.accesses] at access
      rcases access with ⟨_, rfl, _⟩
      exact ⟨trivial, Or.inr rfl⟩
    · simp [storeEvent, Event.accesses] at access
      rcases access with ⟨_, rfl, _⟩
      exact free₂
    · simp [PendingFence, opened, added, fired, clear]
  · exact .cons (.segment (pc := .done) (by simp [stored, fired]) rfl rfl
      (by simp [launch, emptySegment]) rfl) (.nil _)

theorem appendRuns {P : Type} {l : Launch P} {s t u : Config P} {xs ys : Schedule}
    (left : Run l s xs t) (right : Run l t ys u) : Run l s (xs ++ ys) u := by
  induction left with
  | nil => exact right
  | cons step _ ih => exact .cons step (ih right)

/-- No transfer is ever initiated, so no cell is in flight. -/
theorem notInFlight (tr : Trace) (p : Addr) (none : ∀ x ∈ tr, ∀ t, x.2 ≠ .initiate t) :
    ¬ InFlight tr p := by
  rintro ⟨t, pos, _⟩
  have zero : tr.countP (fun x => x.2 = .initiate t) = 0 := by
    rw [List.countP_eq_zero]
    intro x hx
    simpa using none x hx t
  simp [Transfer.pending, zero] at pos

/-- `first` adds first and stores 0; `second` then stores 1. -/
abbrev endFS (w : CellWrites) (s : DistState) : Config PC :=
  afterTurn w (afterTurn w ((launch w).initial s) first 0) second 1

/-- `second` adds first and stores 0; `first` then stores 1. -/
abbrev endSF (w : CellWrites) (s : DistState) : Config PC :=
  afterTurn w (afterTurn w ((launch w).initial s) second 0) first 1

set_option hygiene false in
local macro "noTransfer" : tactic => `(tactic| exact notInFlight _ _ (by
  simp [Machine.trace, opened, fired, added, stored, closed, Launch.initial, segOcc,
    Occurrence.event?, addEvent, storeEvent]))

set_option hygiene false in
local macro "atStart" : tactic => `(tactic| simp [closed, stored, added, fired, opened,
  Launch.initial, launch, Function.update, first, second])

set_option hygiene false in
local macro "counterValue" : tactic => `(tactic| simp [closed, stored, added, fired, opened,
  Launch.initial, w.read_same, w.read_other _ _ _ _ (counter_ne_slot _), zero])

theorem runFS (w : CellWrites) (s : DistState) (zero : (s.cell counter).readAs .nat = some 0) :
    Run (launch w) ((launch w).initial s) (turn first ++ turn second) (endFS w s) := by
  refine appendRuns (turnRun w _ first 0 ?_ rfl ?_ ?_ ?_) (turnRun w _ second 1 ?_ rfl ?_ ?_ ?_)
  · atStart
  · counterValue
  · noTransfer
  · noTransfer
  · atStart
  · counterValue
  · noTransfer
  · noTransfer

theorem runSF (w : CellWrites) (s : DistState) (zero : (s.cell counter).readAs .nat = some 0) :
    Run (launch w) ((launch w).initial s) (turn second ++ turn first) (endSF w s) := by
  refine appendRuns (turnRun w _ second 0 ?_ rfl ?_ ?_ ?_) (turnRun w _ first 1 ?_ rfl ?_ ?_ ?_)
  · atStart
  · counterValue
  · noTransfer
  · noTransfer
  · atStart
  · counterValue
  · noTransfer
  · noTransfer

set_option hygiene false in
local macro "all_finished" : tactic => `(tactic| (
  refine ⟨fun c => ?_, by simp [closed, stored, added, fired, opened, Launch.initial]⟩
  by_cases ca : c = first
  · subst ca; simp [closed, stored, added, fired, opened, Function.update, first, second]
  by_cases cb : c = second
  · subst cb; simp [closed, stored, added, fired, opened, Function.update, first, second]
  simp [closed, stored, added, fired, opened, Launch.initial, launch, Function.update, ca, cb]))

theorem completeFS (w : CellWrites) (s : DistState) : Complete (endFS w s) := by all_finished
theorem completeSF (w : CellWrites) (s : DistState) : Complete (endSF w s) := by all_finished

theorem slot_first_ne_second : slotOf first ≠ slotOf second := by simp [slotOf, first, second]

theorem cellFS (w : CellWrites) (s : DistState) :
    (endFS w s).mem.cell (slotOf first) = .of .nat 0 := by
  simp only [closed, stored, added, fired, opened, Launch.initial]
  rw [w.read_other _ _ _ _ slot_first_ne_second, w.read_other _ _ _ _ (slot_ne_counter first),
    w.read_same]

theorem cellSF (w : CellWrites) (s : DistState) :
    (endSF w s).mem.cell (slotOf first) = .of .nat 1 := by
  simp [closed, stored, added, fired, opened, Launch.initial, w.read_same]

/-- A sound, deterministic-race-free launch with two complete schedules whose
final memories differ, after fix (a). -/
theorem fetchAdd_c3_fails (w : CellWrites) (s : DistState)
    (zero : (s.cell counter).readAs .nat = some 0) :
    ∃ (canonical sched : Schedule) (reference final : Config PC),
      SoundLaunch (launch w) ∧ DetRaceFree (launch w) s ∧
      Run (launch w) ((launch w).initial s) canonical reference ∧ Complete reference ∧
      Run (launch w) ((launch w).initial s) sched final ∧ Complete final ∧
      final.mem ≠ reference.mem := by
  refine ⟨_, _, _, _, launchSound w, launchDetRaceFree w s, runFS w s zero, completeFS w s,
    runSF w s zero, completeSF w s, ?_⟩
  intro same
  have cells : (endSF w s).mem.cell (slotOf first) = (endFS w s).mem.cell (slotOf first) := by
    rw [same]
  rw [cellFS, cellSF] at cells
  have eq := congrArg (fun x : MemCell => x.readAs .nat) cells
  simp at eq

/-- The statement of `detRaceFree_complete_eq_canonical`, at this launch, does not hold. -/
theorem not_c3_candidate (w : CellWrites) (s : DistState)
    (zero : (s.cell counter).readAs .nat = some 0) :
    ¬ ∀ {canonical sched : Schedule} {reference final : Config PC},
        SoundLaunch (launch w) → DetRaceFree (launch w) s →
        Run (launch w) ((launch w).initial s) canonical reference → Complete reference →
        Run (launch w) ((launch w).initial s) sched final → Complete final →
        final.mem = reference.mem := by
  intro c3
  obtain ⟨_, _, _, _, sound, safe, refRun, refDone, run, done, ne⟩ := fetchAdd_c3_fails w s zero
  exact ne (c3 sound safe refRun refDone run done)

def putCellWrites : CellWrites where
  put := DistState.putCell
  read_same := DistState.cell_putCell
  read_other s _ _ v h := DistState.cell_putCell_ne s h v
  local_frame _ _ _ a := by
    unfold DistState.SameLocal DistState.view
    cases a <;> rfl
  commute s _ _ u v h := DistState.putCell_commute s h u v

def zeroState : DistState := (DistState.single default).putCell counter (.of .nat 0)

theorem fetchAdd_c3_fails_concrete :
    ∃ (l : Launch PC) (s : DistState) (canonical sched : Schedule) (reference final : Config PC),
      SoundLaunch l ∧ DetRaceFree l s ∧
      Run l (l.initial s) canonical reference ∧ Complete reference ∧
      Run l (l.initial s) sched final ∧ Complete final ∧ final.mem ≠ reference.mem :=
  ⟨launch putCellWrites, zeroState, fetchAdd_c3_fails putCellWrites _ (by simp [zeroState])⟩

#print axioms launchDetRaceFree
#print axioms fetchAdd_c3_fails
#print axioms not_c3_candidate
#print axioms fetchAdd_c3_fails_concrete

end VeriTile.Tests.FetchAddObservation
