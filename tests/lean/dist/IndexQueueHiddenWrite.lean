import tests.lean.dist.IndexQueueSingleSlotModel
/-! Negative client for #651. An unreported physical write to the head admits
an overwrite before a take. The event-only shape holds, including on the
terminating zero-item variant. Footprint soundness rejects this launch. -/
set_option linter.unusedSimpArgs false
namespace HiddenShaped
open VeriTile.Dist VeriTile.Tests VeriTile.Tests.G1QueueRefinement
open VeriTile.Tests.DeepEPChannel (sender receiver head tail slot rel acq writeSlot waitRoom segOcc)
open VeriTile.Triton (MemCell)
def zero : DistState where
  numRanks := 2
  cell _ := .of .nat 0
  context _ := ⟨fun _ _ _ => none, fun _ _ => 0, fun _ => 1⟩
def q (n : Nat) : IndexQueue := {Dispatch.Q1 rel with items := n}
def w0 := writeSlot sender 0
def ge := waitRoom sender 1
def w1 := writeSlot sender 1
def startGroup : Next Bool := .emitGroup w0 [ge,w1] (fun _ => true)
def prog (w : CellWrites) (terminate : Bool) : Launch Bool where
  program a := ⟨fun pc => ⟨a,fun s => if !pc then some (s.putCell head (.of .nat 1)) else if terminate then some s else none, fun _ => ∅, fun _ => ∅⟩,
    fun pc _ => if pc then .finish else startGroup⟩
  start a := if a = sender then some false else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w
def h0 : History := []
def h1 : History := [segOcc sender]
def h2 : History := [segOcc sender, .issued sender w0, .issued sender ge, .issued sender w1]
def h3 : History := h2 ++ [segOcc sender]
inductive Phase (term : Bool) : History → Option (Cursor Bool) → Prop where
  | start : Phase term h0 (some (.ready false))
  | opened : Phase term h1 startGroup.cursor
  | fired : Phase term h2 (some (.ready true))
  | done : term = true → Phase term h3 none
structure Fit (term : Bool) (c : Config Bool) : Prop where
  phase : Phase term c.history (c.pc sender)
  idle : ∀ a, a ≠ sender → c.pc a = none
  clear : c.pending = []
theorem initialFit (w) (term) : Fit term ((prog w term).initial zero) := by
  refine ⟨?_, ?_, rfl⟩
  · simp [Launch.initial,prog]; exact .start
  · intro a ne; simp [Launch.initial,prog,ne]

theorem fitStep {s t : Config Bool} (fit : Fit term s) (st : step (prog w term) s c t) : Fit term t := by
  obtain ⟨phase,idle,clear⟩ := fit
  cases st with
  | @segment a pc seg mem atPC code owner access success =>
    have : a = sender := by by_contra hn; rw [idle a hn] at atPC; cases atPC
    clear owner; subst a; subst seg
    refine ⟨?_, fun a ne => by simpa [Function.update,ne] using idle a ne, clear⟩
    generalize hh : s.history = h at phase ⊢
    generalize hp : s.pc sender = current at phase atPC
    cases phase with
    | start => cases atPC; simpa [Function.update,prog,h0,h1,segOcc] using (Phase.opened (term := term))
    | opened => cases atPC
    | fired =>
      cases atPC
      cases term with
      | false => simp [prog] at success
      | true => simpa [Function.update,prog,h3,segOcc,Next.cursor] using (Phase.done (term := true) rfl)
    | done => cases atPC
  | @fire a x xs k final vs atPC owned events =>
    have : a = sender := by by_contra hn; rw [idle a hn] at atPC; cases atPC
    subst a
    generalize hh : s.history = h at phase
    generalize hp : s.pc sender = current at phase atPC
    cases phase with
    | start => cases atPC
    | done => cases atPC
    | fired => cases atPC
    | opened =>
      cases atPC
      cases events; rename_i a b c f rest
      cases f
      cases rest; rename_i a b c f rest
      cases f
      cases rest; rename_i a b c f rest
      cases f; cases rest
      refine ⟨?_, fun a ne => by simpa [Function.update,ne] using idle a ne, clear⟩
      simp only [Function.update_self]
      rw [hh]
      exact .fired
  | deliver outstanding _ _ _ _ _ _ => rw [clear] at outstanding; simp at outstanding

theorem fitRun (r : Run (prog w term) s sched t) : Fit term s → Fit term t := by
  induction r with
  | nil => exact id
  | cons step _ ih => exact fun f => ih (fitStep f step)

theorem bounds (ph : Phase term h cur) : h.length ≤ 5 := by cases ph <;> decide
theorem putFacts (ph : Phase term h cur) (put : (q n).view.Put h k i) :
    h[i]? = some (.issued sender ⟨sender,.access .store ((q n).slotOf k) .plain,.store ((q n).payload k)⟩) ∧
    (1 ≤ k → i = 3 ∧ k = 1 ∧ h[2]? = some (.issued sender ge)) := by
  obtain ⟨⟨x,hx,hit⟩,cnt⟩ := put
  have ib : i < 5 := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hx).1 (bounds ph)
  cases ph <;> interval_cases i <;> first | (simp [h0,h1,h2,h3] at hx; done) | (simp [h0,h1,h2,h3] at hx; subst x; simp_all (config := { decide := true }) [h0,h1,h2,h3,w0,w1,ge,segOcc,
      q,Dispatch.Q1,IndexQueue.view,IndexQueue.isPut,IndexQueue.isTake,IndexQueue.isSlot,
      IndexQueue.slotOf,writeSlot,waitRoom,sender,receiver])

  all_goals subst k; first | rfl | exact ⟨rfl,rfl⟩

theorem noTake (ph : Phase term h cur) (take : (q n).view.Take h k i) : False := by
  obtain ⟨⟨x,hx,hit⟩,_⟩ := take
  have ib : i < 5 := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hx).1 (bounds ph)
  cases ph <;> interval_cases i <;> first | (simp [h0,h1,h2,h3] at hx; done) | (simp [h0,h1,h2,h3] at hx; subst x; simp_all (config := { decide := true }) [h0,h1,h2,h3,w0,w1,ge,segOcc,
      q,Dispatch.Q1,IndexQueue.view,IndexQueue.isPut,IndexQueue.isTake,IndexQueue.isSlot,
      IndexQueue.slotOf,writeSlot,waitRoom,sender,receiver])

theorem ptrAbsent {i : Nat} {v : MemCell} (ph : Phase term h cur) :
    h[i]? ≠ some (.issued sender ⟨sender,.access .store tail rel,.store v⟩) ∧
    h[i]? ≠ some (.issued receiver ⟨receiver,.access .store head rel,.store v⟩) := by
  constructor <;> intro hx <;> have ib : i < 5 := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hx).1 (bounds ph)
  all_goals cases ph <;> interval_cases i <;> simp [h0,h1,h2,h3,w0,w1,ge,writeSlot,waitRoom,slot,tail,head,sender,receiver,segOcc] at hx

theorem cellsOK {i : Nat} {x : Occurrence} (ph : Phase term h cur) (hx : h[i]? = some x) (ac : x.access p kd m) :
    (q n).Allowed x := by
  have ib : i < 5 := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hx).1 (bounds ph)
  cases ph <;> interval_cases i <;> first | (simp [h0,h1,h2,h3] at hx; done) | (simp [h0,h1,h2,h3] at hx; subst x)
  all_goals first | (cases kd <;> cases m <;> simp [segOcc,Occurrence.access] at ac; done)
                  | simp (config := {decide := true}) [q,IndexQueue.Allowed,Dispatch.Q1,w0,w1,ge,writeSlot,waitRoom,IndexQueue.isSlot]

theorem shape (w) (term) (n : Nat) (valid : term = true → n = 0) : (q n).Shaped (prog w term) zero := by
  have ph := fun {sched fin} (r : Run (prog w term) ((prog w term).initial zero) sched fin) =>
    (fitRun r (initialFit w term)).phase
  constructor
  · exact fun _ _ r _ _ _ _ _ hx a _ => cellsOK (ph r) hx a
  · exact fun _ _ r _ _ put => (putFacts (ph r) put).1
  · exact fun _ _ r _ _ take => (noTake (ph r) take).elim
  · intro sched fin r k i put bound
    obtain ⟨rfl,rfl,atRoom⟩ := (putFacts (ph r) put).2 bound
    exact ⟨2,1,by decide,by change 2 ≤ 2; decide,atRoom⟩
  · exact fun _ _ r _ _ hx => ((ptrAbsent (ph r)).1 hx).elim
  · exact fun _ _ r _ _ take => (noTake (ph r) take).elim
  · exact fun _ _ r _ _ hx => ((ptrAbsent (ph r)).2 hx).elim
  · intro sched fin r comp
    have p := ph r
    rw [comp.1 sender] at p
    generalize hh : fin.history = h at p ⊢
    cases p with
    | done ok => rw [valid ok]; rfl

def opened (w : CellWrites) (term : Bool) : Config Bool :=
  let start := (prog w term).initial zero
  { start with
    mem := zero.putCell head (.of .nat 1)
    history := h1
    pc := Function.update start.pc sender startGroup.cursor }
def fired (w : CellWrites) (term : Bool) : Config Bool :=
  let x := opened w term
  {x with
    mem := w.put (w.put x.mem slot (.of .nat 40)) slot (.of .nat 41)
    history := h2
    pc := Function.update x.pc sender (some (.ready true))}
def finished (w : CellWrites) : Config Bool :=
  let x := fired w true
  {x with history := h3, pc := Function.update x.pc sender none}

theorem openStep (w) (term) :
    step (prog w term) ((prog w term).initial zero) (.agent sender) (opened w term) := by
  exact .segment (l := prog w term) (s := (prog w term).initial zero) (a := sender) (pc := false) (by simp [Launch.initial,prog]) rfl rfl (by simp [prog]) rfl

theorem fireStep (w) (term) :
    step (prog w term) (opened w term) (.agent sender) (fired w term) := by
  refine .fire (l := prog w term) (s := opened w term) (a := sender) (h := w0) (t := [ge,w1]) (k := fun _ => true)
    (final := ⟨(fired w term).mem,h2,[]⟩) (values := [none,some (.of .nat 1),none])
    (by simp [opened,startGroup,Next.cursor]) ?_ ?_
  · intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> exact DeepEPChannel.own sender
  · refine .cons ?_ ?_ (by simp [PendingFence,opened,Launch.initial]) (.store _ _ _ _) ?_
    · exact DeepEPChannel.accessOK w _ (by simp [w0,w1,ge,writeSlot,waitRoom,Event.accesses,slot,head])
    · exact fun _ _ _ _ => DeepEPChannel.notInFlight _ _ (by
        simp [Machine.trace,opened,Launch.initial,h1,segOcc,w0,w1,ge,writeSlot,waitRoom,Occurrence.event?])
    refine .cons ?_ ?_ (by simp [PendingFence,opened,Launch.initial])
      (.wait _ _ _ _ _ 1 ?_ (Nat.le_refl 1)) ?_
    · exact DeepEPChannel.accessOK w _ (by simp [w0,w1,ge,writeSlot,waitRoom,Event.accesses,slot,head])
    · exact fun _ _ _ _ => DeepEPChannel.notInFlight _ _ (by
        simp [Machine.trace,opened,Launch.initial,h1,segOcc,w0,w1,ge,writeSlot,waitRoom,Occurrence.event?])
    · simp [Machine.count?,prog,opened,CellWrites.read_other,slot,head]
    refine .cons ?_ ?_ (by simp [PendingFence,opened,Launch.initial]) (.store _ _ _ _) (.nil _)
    · exact DeepEPChannel.accessOK w _ (by simp [w0,w1,ge,writeSlot,waitRoom,Event.accesses,slot,head])
    · exact fun _ _ _ _ => DeepEPChannel.notInFlight _ _ (by
        simp [Machine.trace,opened,Launch.initial,h1,segOcc,w0,w1,ge,writeSlot,waitRoom,Occurrence.event?])
theorem badRun (w) (term) :
    Run (prog w term) ((prog w term).initial zero) [.agent sender,.agent sender] (fired w term) :=
  .cons (openStep w term) (.cons (fireStep w term) (.nil _))
theorem badReuse (w) (term) (n) : ¬ QueueRefines (prog w term) zero (q n).view := by
  intro good
  have put : (q n).view.Put h2 (0 + (q n).cap) 3 := ⟨⟨_,rfl,rfl⟩,rfl⟩
  obtain ⟨i,take,_,_⟩ := (good _ _ (badRun w term)).2 0 3 put
  exact noTake (Phase.fired (term := term)) take

theorem doneStep (w) : step (prog w true) (fired w true) (.agent sender) (finished w) := by
  exact .segment (l := prog w true) (s := fired w true) (a := sender) (pc := true) (by simp [fired]) rfl rfl (by simp [prog]) rfl
theorem doneComplete (w) : Complete (finished w) := by
  constructor
  · intro a; by_cases ha : a = sender
    · subst a; simp [finished]
    · simp [finished,fired,opened,Launch.initial,prog,Function.update,ha]
  · simp [finished,fired,opened,Launch.initial]
theorem completesZero (w) : Run (prog w true) ((prog w true).initial zero)
    [.agent sender,.agent sender,.agent sender] (finished w) ∧ Complete (finished w) :=
  ⟨.cons (openStep w true) (.cons (fireStep w true) (.cons (doneStep w) (.nil _))),doneComplete w⟩

theorem counterexample (w : CellWrites) (term : Bool) (n : Nat) (ad : term = true → n = 0) :
    (q n).Shaped (prog w term) zero ∧
    zero.cell (q n).tail = .of .nat 0 ∧ zero.cell (q n).head = .of .nat 0 ∧
    (∀ p, Mode.Pairs (prog w term).reach p (q n).sender (q n).receiver (q n).publish (q n).poll) ∧
    (∀ p, Mode.Pairs (prog w term).reach p (q n).receiver (q n).sender (q n).ack (q n).room) ∧
    ¬ QueueRefines (prog w term) zero (q n).view :=
  ⟨shape w term n ad,rfl,rfl,Dispatch.publish_pairs rel w,Dispatch.release_ack_pairs w,badReuse w term n⟩

theorem positiveItems (w : CellWrites) : (q 2).Shaped (prog w false) zero ∧
    ¬ QueueRefines (prog w false) zero (q 2).view := by
  exact ⟨shape _ _ _ (by decide),badReuse _ _ _⟩
theorem noPositiveComplete (w : CellWrites) (r : Run (prog w false) ((prog w false).initial zero) sched t) :
    ¬ Complete t := by
  intro done
  have ph := (fitRun r (initialFit w false)).phase
  rw [done.1 sender] at ph
  generalize h : t.history = h' at ph
  cases ph with | done hf => contradiction
theorem unsound (w) (term) : ¬ SoundLaunch (prog w term) := by
  intro sound
  have eqv := (sound.footprints sender false).frame zero (zero.putCell head (.of .nat 1)) rfl head (by simp [prog])
  have bad : (1 : Nat) = 0 := Option.some.inj (congrArg (fun v => v.readAs .nat) eqv)
  omega
#print axioms counterexample
#print axioms positiveItems
#print axioms noPositiveComplete
#print axioms completesZero
#print axioms unsound
end HiddenShaped
