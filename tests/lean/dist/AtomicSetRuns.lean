/- Two complete, race-free schedules of the same launch can leave different
physical values in one word (S4.8). Each CTA does one system-scope atomic set. -/
import VeriTile.Staging.Dist.JudgmentSpec

namespace VeriTile.Tests.AtomicSetRuns
open VeriTile.Dist
open VeriTile.Triton (MemCell)

def first : Agent := .cta ⟨0, [0]⟩
def second : Agent := .cta ⟨0, [1]⟩
def word : Addr := ⟨.global 0, "signal", 0⟩
private def mode := Mode.atomic .sys .relaxed
private def value (a : Agent) := if a = first then 1 else 2
private def writeEvent (a : Agent) : Emission :=
  ⟨a, .bump ⟨.word word, .set, value a, mode⟩, .noValue⟩
private def emptySegment (a : Agent) : Segment := ⟨a, some, fun _ => ∅, fun _ => ∅⟩

def launch (w : CellWrites) : Launch Bool where
  program a := ⟨fun _ => emptySegment a, fun finished _ =>
    if finished then .finish else .emitGroup (writeEvent a) [] (fun _ => true)⟩
  start a := if a = first ∨ a = second then some false else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

private def segOccurrence (a : Agent) := Occurrence.segment a ∅ ∅

private def opened (s : Config Bool) (a : Agent) : Config Bool :=
  { s with history := s.history ++ [segOccurrence a],
           pc := Function.update s.pc a (some (.waiting (writeEvent a) [] (fun _ => true))) }

private def stored (w : CellWrites) (s : Config Bool) (a : Agent) : Config Bool :=
  { s with mem := w.put s.mem word (.of .nat (value a)),
           history := s.history ++ [.issued a (writeEvent a)],
           pc := Function.update s.pc a (some (.ready true)) }

private def finished (s : Config Bool) (a : Agent) : Config Bool :=
  { s with history := s.history ++ [segOccurrence a], pc := Function.update s.pc a none }

private abbrev after (w : CellWrites) (s : Config Bool) (a : Agent) :=
  finished (stored w (opened s a) a) a

/-- Run the opening segment, issue the atomic set, then run the closing segment. -/
def choices (a : Agent) : Schedule := [.agent a, .agent a, .agent a]

private theorem one (w : CellWrites) (s : Config Bool) (a : Agent)
    (ready : s.pc a = some (.ready false)) (owns : a.within a)
    (clear : s.pending = []) (free : ∀ p, ¬ InFlight (opened s a).trace p) :
    Run (launch w) s (choices a) (after w s a) := by
  refine .cons (t := opened s a) (.segment ready rfl rfl (by simp [launch, emptySegment]) rfl) ?_
  refine .cons (t := stored w (opened s a) a)
    (.fire (s := opened s a) (a := a) (h := writeEvent a) (t := [])
      (k := fun _ => true) (values := [none]) (by simp [opened]) ?_ ?_) ?_
  · simpa [writeEvent] using owns
  · refine .cons ?_ (fun _ p _ _ => free p) ?_ ?_ (.nil _)
    · intro k p m access
      simp [writeEvent, Event.accesses, Bump.accesses, SignalOp.kind] at access
      rcases access with ⟨_, rfl, _⟩
      exact ⟨trivial, Or.inr rfl⟩
    · simp [PendingFence, opened, clear]
    · exact .bump _ _ 0 (by intro h; cases h)
  · refine .cons (.segment (pc := true) (by simp [stored]) rfl rfl
      (by simp [launch, emptySegment]) rfl) (.nil _)

private theorem appendRuns {l : Launch P} {s t u : Config P} {xs ys : Schedule}
    (left : Run l s xs t) (right : Run l t ys u) : Run l s (xs ++ ys) u := by
  induction left with
  | nil => exact right
  | cons step _ ih => exact .cons step (ih right)

private theorem atomicAccess (a : Agent) {x : Occurrence} (member : x = segOccurrence a ∨ x = .issued a (writeEvent a))
    {p k m} (access : x.access p k m) : m = mode := by
  rcases member with rfl | rfl
  · cases k <;> cases m <;> simp [segOccurrence, Occurrence.access] at access
  · simp [writeEvent, Occurrence.access, Event.accesses, Bump.accesses, SignalOp.kind] at access
    exact access.2.2

/-- Only a set can wait to fire. No transfers are pending and every recorded access
belongs to a set; empty segments contribute no accesses. -/
private def OnlySets (s : Config Bool) : Prop :=
  s.pending = [] ∧
  (∀ a h t k, s.pc a = some (.waiting h t k) → h = writeEvent a ∧ t = []) ∧
  ∀ x ∈ s.history, ∃ a, x = segOccurrence a ∨ x = .issued a (writeEvent a)

private theorem oneSetGroup {w : CellWrites} {a : Agent} {s f : Machine} {values}
    (group : FireGroup (launch w) a s [writeEvent a] f values) :
    f.pending = s.pending ∧ f.history = s.history ++ [.issued a (writeEvent a)] := by
  cases group with
  | cons _ _ _ fire rest =>
    cases rest
    cases fire
    exact ⟨rfl,rfl⟩

private theorem stepOnlySets {w : CellWrites} {s f : Config Bool} {c}
    (fact : OnlySets s) (move : step (launch w) s c f) : OnlySets f := by
  obtain ⟨pending,waiting,history⟩ := fact
  cases move with
  | @segment a pc seg mem atPC code owner access success =>
    subst seg
    refine ⟨pending, ?_, ?_⟩
    · intro b h t k atB
      by_cases eq : b = a
      · subst b
        cases pc <;> simp [Function.update, launch, Next.cursor] at atB
        exact ⟨atB.1.symm, atB.2.1⟩
      · exact waiting b h t k (by simpa [Function.update, eq] using atB)
    · intro x member
      rcases List.mem_append.mp member with old | new
      · exact history _ old
      · exact ⟨a, Or.inl (List.mem_singleton.mp new)⟩
  | @fire a h t k final values atPC owned events =>
    obtain ⟨rfl,rfl⟩ := waiting _ _ _ _ atPC
    obtain ⟨pend,hist⟩ := oneSetGroup events
    refine ⟨pend.trans pending, ?_, ?_⟩
    · intro b h t k atB
      by_cases eq : b = a
      · subst b; simp [Function.update] at atB
      · exact waiting b h t k (by simpa [Function.update, eq] using atB)
    · intro x member
      change x ∈ final.history at member
      rw [hist] at member
      rcases List.mem_append.mp member with old | new
      · exact history _ old
      · exact ⟨a, Or.inr (List.mem_singleton.mp new)⟩
  | deliver outstanding _ _ _ _ _ _ => simp [pending] at outstanding

/-- Every schedule prefix of the example is data-race free. -/
theorem launchDRF (w : CellWrites) (s : DistState) : DRF (launch w) s := by
  intro sched final run
  have allPrefixes {start stop : Config Bool} {schedule}
      (steps : Run (launch w) start schedule stop) (inv : OnlySets start) : OnlySets stop := by
    induction steps with
    | nil => exact inv
    | cons step _ ih => exact ih (stepOnlySets inv step)
  have initial : OnlySets ((launch w).initial s) := by
    refine ⟨rfl, ?_, by simp [Launch.initial]⟩
    intro a h t k
    simp [Launch.initial, launch]
  obtain ⟨_,_,history⟩ := allPrefixes run initial
  rintro ⟨i,j,x,y,p,k,k',m,m',_,hx,hy,ax,ay,_,apart,_⟩
  have atomic {x : Occurrence} (mem : x ∈ final.history) {k m} (access : x.access p k m) : m = mode := by
    obtain ⟨a,ha⟩ := history _ mem
    exact atomicAccess a ha access
  rw [atomic (List.mem_of_getElem? hx) ax, atomic (List.mem_of_getElem? hy) ay] at apart
  exact apart ⟨trivial, trivial⟩

private theorem inOrder (w : CellWrites) (s : DistState) (a b : Agent)
    (order : (a = first ∧ b = second) ∨ (a = second ∧ b = first)) :
    ∃ f, Run (launch w) ((launch w).initial s) (choices a ++ choices b) f ∧
      Complete f ∧ f.mem.cell word = .of .nat (value b) := by
  have ne : a ≠ b := by rcases order with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  have own (c : Agent) : c.within c := by cases c <;> simp [Agent.within, Agent.rankOf, Agent.cta?]
  let start := (launch w).initial s
  let middle := after w start a
  use after w middle b
  constructor
  · apply appendRuns
    · refine one w start a ?_ (own a) rfl ?_
      · rcases order with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [start, Launch.initial, launch]
      · simp [start, opened, Launch.initial, Machine.trace, segOccurrence,
          Occurrence.event?, InFlight, Transfer.pending]
    · refine one w middle b ?_ (own b) rfl ?_
      · rcases order with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
          simp [middle, finished, stored, opened, start, Launch.initial, launch,
            Function.update, first, second]
      · simp [middle, start, opened, finished, stored, Launch.initial, Machine.trace,
          segOccurrence, Occurrence.event?, writeEvent, InFlight, Transfer.pending]
  refine ⟨⟨?_, by simp [middle, start, Launch.initial, finished, stored, opened]⟩,
    w.read_same ..⟩
  intro c
  by_cases ca : c = a
  · subst c; simp [finished, stored, opened, middle, Function.update, ne]
  by_cases cb : c = b
  · subst c; simp [finished]
  rcases order with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    simp [finished, stored, opened, middle, start, Launch.initial, launch, Function.update, ca, cb]

/-- Both final states start from the very same distributed memory and launch.
The physical word records the value written by whichever CTA ran last. -/
theorem atomicSetSchedules (w : CellWrites) (s : DistState) :
    ∃ f g, Run (launch w) ((launch w).initial s) (choices first ++ choices second) f ∧
      Run (launch w) ((launch w).initial s) (choices second ++ choices first) g ∧
      Complete f ∧ Complete g ∧ ¬ DataRace (launch w) f.history ∧
      ¬ DataRace (launch w) g.history ∧ f.mem.cell word = .of .nat 2 ∧
      g.mem.cell word = .of .nat 1 ∧ f.mem.cell word ≠ g.mem.cell word := by
  obtain ⟨f, rf, cf, lastF⟩ := inOrder w s first second (.inl ⟨rfl,rfl⟩)
  obtain ⟨g, rg, cg, lastG⟩ := inOrder w s second first (.inr ⟨rfl,rfl⟩)
  refine ⟨f, g, rf, rg, cf, cg, launchDRF w s _ _ rf, launchDRF w s _ _ rg, lastF, lastG, ?_⟩
  rw [lastF, lastG]
  intro h
  have eq := congrArg (fun x : MemCell => x.readAs .nat) h
  contradiction

end VeriTile.Tests.AtomicSetRuns
