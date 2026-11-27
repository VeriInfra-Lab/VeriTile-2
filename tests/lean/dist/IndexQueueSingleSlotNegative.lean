import tests.lean.dist.IndexQueueSingleSlotModel

/-! #651. Two negative clients of the single-slot contract. The first reuses
the reachable relaxed-head execution from DeepEPChannel. The second runs the
advisor's decreasing-tail program against the corrected publication premise. -/
namespace VeriTile.Tests.G1QueueRefinement.Dispatch
open VeriTile.Dist
open VeriTile.Tests.DeepEPChannel (sender receiver tail head slot rel acq rlx H2 segOcc writeSlot
  publishTail loadTail readSlot waitRoom emptySegment)

private theorem secondPut : (Q1 rlx).view.Put H2 (0 + (Q1 rlx).view.cap) 13 := by
  refine ⟨⟨_, rfl, rfl⟩, ?_⟩
  rfl

private theorem onlyTake {j : Nat} (h : (Q1 rlx).view.Take H2 0 j) : j = 7 := by
  obtain ⟨⟨x, hx, take⟩, _⟩ := h
  have bound : j < 14 := (List.getElem?_eq_some_iff.mp hx).1
  interval_cases j <;> simp [H2] at hx <;> subst hx <;>
    simp [IndexQueue.view, IndexQueue.isTake, IndexQueue.isSlot, Q1, segOcc, writeSlot,
      publishTail, loadTail, readSlot, DeepEPChannel.storeHead, waitRoom, sender, receiver, slot,
      tail, head] at take ⊢

/-- The relaxed head store gives no release edge from slot read 7 to overwrite 13. -/
theorem relaxed_not_refines (w : CellWrites) (s : DistState) :
    ¬ QueueRefines (launch rlx w) s (Q1 rlx).view := by
  rw [launch_relaxed_eq]
  intro good
  obtain ⟨f, run, hist⟩ := DeepEPChannel.wrapRun w s
  have reuse := (good _ _ run).2
  rw [hist] at reuse
  obtain ⟨j, take, _, hb⟩ := reuse 0 13 secondPut
  obtain rfl := onlyTake take
  apply DeepEPChannel.no_hb_while_mute (DeepEPChannel.launch w) H2 slot 7 13 receiver
      ⟨.issued receiver (readSlot receiver), rfl, rfl⟩ _ _ hb
  · intro k x lo hi hx mine a e ev
    interval_cases k <;> simp [H2] at hx <;> subst hx <;>
      simp [Occurrence.program?, Occurrence.event?, segOcc, sender, receiver, readSlot,
        DeepEPChannel.storeHead] at mine ev
    · obtain ⟨_, rfl⟩ := ev
      exact DeepEPChannel.mute_of_quiet (DeepEPChannel.quiet_load _ _)
    · obtain ⟨_, rfl⟩ := ev
      exact DeepEPChannel.mute_relaxed_store _ _
  · intro y hy
    simp [H2] at hy
    subst hy
    simp [Occurrence.program?, sender, receiver]

namespace DecreasingTail
open VeriTile.Triton (MemCell)

private def store (p : Addr) (m : Mode) (v : Nat) : Emission :=
  ⟨sender, .access .store p m, .store (.of .nat v)⟩

/-- The advisor’s original counterexample has no receiver or delivery obligation. -/
def queue : IndexQueue := { Q1 rel with items := 0 }

private def code : List Emission := [store slot .plain 40, store tail rel 1, store tail rel 0]

private def next : List Emission → Next (List Emission)
  | [] => .finish
  | e :: rest => .emitGroup e [] (fun _ => rest)

/-- One sender writes its slot, publishes tail 1, then publishes tail 0. -/
def program (w : CellWrites) : Launch (List Emission) where
  program a := ⟨fun _ => emptySegment a, fun pc _ => next pc⟩
  start a := if a = sender then some code else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

private def opened (c : Config (List Emission)) (pc : List Emission) : Config (List Emission) :=
  { c with history := c.history ++ [segOcc sender], pc := Function.update c.pc sender (next pc).cursor }

private def wrote (w : CellWrites) (c : Config (List Emission)) (p : Addr) (m : Mode)
    (v : Nat) (rest : List Emission) : Config (List Emission) :=
  { c with mem := w.put c.mem p (.of .nat v), history := c.history ++ [.issued sender (store p m v)],
           pc := Function.update c.pc sender (some (.ready rest)) }

private theorem oneStore (w : CellWrites) (c : Config (List Emission)) (p : Addr) (m : Mode)
    (v : Nat) (rest : List Emission) (ready : c.pc sender = some (.ready (store p m v :: rest)))
    (clear : c.pending = []) (space : p.space = .global 1)
    (free : ¬ InFlight (opened c (store p m v :: rest)).trace p) :
    Run (program w) c [.agent sender, .agent sender]
      (wrote w (opened c (store p m v :: rest)) p m v rest) := by
  let b := opened c (store p m v :: rest)
  refine .cons (t := b) (.segment ready rfl rfl (by simp [program, emptySegment]) rfl) ?_
  refine .cons (.fire (s := b) (a := sender) (h := store p m v) (t := [])
    (k := fun _ => rest) (values := [none]) ?_ ?_ ?_) (.nil _)
  · simp [b, opened, next, Next.cursor]
  · simpa [store] using DeepEPChannel.own sender
  · refine .cons (DeepEPChannel.accessOK w _ (by simp [store, Event.accesses, space])) ?_
        (by simp [PendingFence, b, opened, clear]) (.store _ _ _ _) (.nil _)
    intro kd q mode member
    simp [store, Event.accesses] at member
    obtain ⟨rfl, rfl, rfl⟩ := member
    exact free

private def history : History :=
  [segOcc sender, .issued sender (store slot .plain 40), segOcc sender,
   .issued sender (store tail rel 1), segOcc sender, .issued sender (store tail rel 0)]

private theorem run (w : CellWrites) (s : DistState) :
    ∃ f, Run (program w) ((program w).initial s) (List.replicate 6 (.agent sender)) f ∧
      f.history = history := by
  refine ⟨_, DeepEPChannel.appendRuns
    (oneStore w _ slot .plain 40 [store tail rel 1, store tail rel 0] ?_ rfl rfl ?_)
    (DeepEPChannel.appendRuns
      (oneStore w _ tail rel 1 [store tail rel 0] ?_ rfl rfl ?_)
      (oneStore w _ tail rel 0 [] ?_ rfl rfl ?_)), rfl⟩
  all_goals first
    | exact DeepEPChannel.notInFlight _ _ (by
        simp [Machine.trace, opened, wrote, Launch.initial, segOcc, Occurrence.event?, store])
    | simp [Launch.initial, program, code, wrote, Function.update]

/-- At the final publication the word stores zero, but one slot write precedes it.
This reachable program is rejected by the exact publication count. -/
theorem not_shaped (w : CellWrites) (s : DistState) :
    ¬ queue.Shaped (program w) s := by
  intro shape
  obtain ⟨f, executed, hist⟩ := run w s
  have published := shape.publishWritten _ f executed 5 (.of .nat 0)
  rw [hist] at published
  obtain ⟨n, readZero, count⟩ := published rfl
  have zero : 0 = n := Option.some.inj readZero
  have one : n = 1 := count
  exact Nat.zero_ne_one (zero.trans one)

end DecreasingTail

/-- Both counterexamples apply to actual mutable cells with initially zero words. -/
theorem negative_instances : ∃ (w : CellWrites) (s : DistState),
    s.cell tail = .of .nat 0 ∧ s.cell head = .of .nat 0 ∧
    ¬ QueueRefines (launch rlx w) s (Q1 rlx).view ∧ ¬ DecreasingTail.queue.Shaped (DecreasingTail.program w) s := by
  let w : CellWrites := {
    put := DistState.putCell
    read_same := DistState.cell_putCell
    read_other := fun s _ _ v h => s.cell_putCell_ne h v
    local_frame := by intro s p v a; cases a <;> rfl
    commute := fun s _ _ u v h => s.putCell_commute h u v }
  let s : DistState := {
    numRanks := 2
    cell := fun _ => .of .nat 0
    context := fun _ => ⟨fun _ _ _ => none, fun _ _ => 0, fun _ => 1⟩ }
  exact ⟨w, s, rfl, rfl, relaxed_not_refines w s, DecreasingTail.not_shaped w s⟩

#print axioms negative_instances
#print axioms relaxed_not_refines
#print axioms DecreasingTail.not_shaped

end VeriTile.Tests.G1QueueRefinement.Dispatch
