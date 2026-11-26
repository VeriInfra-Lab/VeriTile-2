import tests.lean.dist.IndexQueueSingleSlotModel

/-! A complete schedule of the two-token release-head dispatch; all eleven
milestones are issued by the actual launch, and both programs return. -/
namespace VeriTile.Tests.G1QueueRefinement.Dispatch
open VeriTile.Dist
open VeriTile.Triton (MemCell)
open VeriTile.Tests.DeepEPChannel (sender receiver tail head slot rel acq PC tokens
  writeSlot publishTail waitRoom loadTail readSlot afterPoll more emptySegment own segOcc
  appendRuns notInFlight)

namespace SingleSlotWitness

private def opened (ack : Mode) (s : Config PC) (a : Agent) (pc : PC) : Config PC :=
  { s with history := s.history ++ [segOcc a],
           pc := Function.update s.pc a ((nextOf ack a pc).cursor) }

private def fired (s : Config PC) (a : Agent) (e : Emission) (mem : DistState) (next : PC) : Config PC :=
  { s with mem := mem, history := s.history ++ [.issued a e],
           pc := Function.update s.pc a (some (.ready next)) }

private theorem oneEvent (ack : Mode) (w : CellWrites) (s : Config PC) (a : Agent) (pc : PC) (e : Emission)
    (k : List (Option MemCell) → PC) (mem : DistState) (v : Option MemCell)
    (ready : s.pc a = some (.ready pc)) (code : nextOf ack a pc = .emitGroup e [] k)
    (clear : s.pending = []) (actor : e.actor = a)
    (access : e.event.AccessibleBy (launch ack w).symm e.actor)
    (free : ∀ kd p m, (kd, p, m) ∈ e.event.accesses → ¬ InFlight (opened ack s a pc).trace p)
    (fire : Fire (launch ack w) (opened ack s a pc).toMachine e mem (opened ack s a pc).pending v) :
    Run (launch ack w) s [.agent a, .agent a] (fired (opened ack s a pc) a e mem (k [v])) := by
  refine .cons (t := opened ack s a pc)
    (.segment ready rfl rfl (by simp [launch, emptySegment]) rfl) ?_
  refine .cons (t := fired (opened ack s a pc) a e mem (k [v]))
    (.fire (s := opened ack s a pc) (a := a) (h := e) (t := []) (k := k) (values := [v])
      (by simp [opened, code, Next.cursor]) ?_ ?_) (.nil _)
  · intro x hx
    simp at hx
    subst hx
    rw [actor]
    exact own a
  · exact .cons access free (by simp [PendingFence, opened, clear]) fire (.nil _)

private theorem accessOK' (ack : Mode) (w : CellWrites) (e : Emission)
    (h : ∀ x ∈ e.event.accesses, x.2.1.space = .global 1) :
    e.event.AccessibleBy (launch ack w).symm e.actor :=
  fun kd p m hm => DeepEPChannel.reachable _ _ (h (kd, p, m) hm)

private theorem finishTurn (w : CellWrites) (s : Config PC) (a : Agent)
    (ready : s.pc a = some (.ready .done)) :
    Run (launch rel w) s [.agent a] (opened rel s a .done) :=
  .cons (.segment ready rfl rfl (by simp [launch, emptySegment]) rfl) (.nil _)

private def reached : Nat → History
  | 0 => []
  | n+1 => (reached n ++ [segOcc (milestone n).owner]) ++ [milestone n]

private theorem reachedPrefix {n} (le : n ≤ 11) : Prefix n (reached n) := by
  induction n with
  | zero => exact .start
  | succ m ih => exact .advance (.noise (ih (by omega)) (.segment _)) (by omega)

private def fullHistory : History := (reached 11 ++ [segOcc sender]) ++ [segOcc receiver]

private theorem allMilestones : Prefix 11 fullHistory :=
  .noise (.noise (reachedPrefix (by decide)) (.segment sender)) (.segment receiver)

set_option maxHeartbeats 1500000 in
/-- No constraint on the initial state or writes implementation is required for
this schedule: it publishes each tail before its poll and head 1 before reuse. -/
theorem completeScheduled (w : CellWrites) (s : DistState) :
    ∃ sched final, Run (launch rel w) ((launch rel w).initial s) sched final ∧
      Complete final ∧ Prefix 11 final.history := by
  refine ⟨_, _, appendRuns
    (oneEvent rel w _ sender (.write 0) (writeSlot sender 0) (fun _ => .publish 0) _ _ ?_ rfl rfl rfl
      (accessOK' rel w _ (by simp [writeSlot, Event.accesses, slot])) ?_ (.store _ _ _ _))
    (appendRuns
    (oneEvent rel w _ sender (.publish 0) (publishTail sender 0) (fun _ => more 0 (.room 1)) _ _ ?_ rfl rfl rfl
      (accessOK' rel w _ (by simp [publishTail, Event.accesses, tail])) ?_ (.store _ _ _ _))
    (appendRuns
    (oneEvent rel w _ receiver (.poll 0) (loadTail receiver) (afterPoll 0) _ _ ?_ rfl rfl rfl
      (accessOK' rel w _ (by simp [loadTail, Event.accesses, tail])) ?_ (.load _ _ _))
    (appendRuns
    (oneEvent rel w _ receiver (.read 0) (readSlot receiver) (fun _ => .ack 0) _ _ ?_ rfl rfl rfl
      (accessOK' rel w _ (by simp [readSlot, Event.accesses, slot])) ?_ (.load _ _ _))
    (appendRuns
    (oneEvent rel w _ receiver (.ack 0) (storeHead rel receiver 0) (fun _ => more 0 (.poll 1)) _ _ ?_ rfl rfl rfl
      (accessOK' rel w _ (by simp [storeHead, Event.accesses, head])) ?_ (.store _ _ _ _))
    (appendRuns
    (oneEvent rel w _ sender (.room 1) (waitRoom sender 1) (fun _ => .write 1) _ _ ?_ rfl rfl rfl
      (accessOK' rel w _ (by simp [waitRoom, Event.accesses, head])) ?_ (.wait _ _ _ _ _ 1 ?_ (Nat.le_refl 1)))
    (appendRuns
    (oneEvent rel w _ sender (.write 1) (writeSlot sender 1) (fun _ => .publish 1) _ _ ?_ rfl rfl rfl
      (accessOK' rel w _ (by simp [writeSlot, Event.accesses, slot])) ?_ (.store _ _ _ _))
    (appendRuns
    (oneEvent rel w _ sender (.publish 1) (publishTail sender 1) (fun _ => more 1 (.room 2)) _ _ ?_ rfl rfl rfl
      (accessOK' rel w _ (by simp [publishTail, Event.accesses, tail])) ?_ (.store _ _ _ _))
    (appendRuns
    (oneEvent rel w _ receiver (.poll 1) (loadTail receiver) (afterPoll 1) _ _ ?_ rfl rfl rfl
      (accessOK' rel w _ (by simp [loadTail, Event.accesses, tail])) ?_ (.load _ _ _))
    (appendRuns
    (oneEvent rel w _ receiver (.read 1) (readSlot receiver) (fun _ => .ack 1) _ _ ?_ rfl rfl rfl
      (accessOK' rel w _ (by simp [readSlot, Event.accesses, slot])) ?_ (.load _ _ _))
    (appendRuns
    (oneEvent rel w _ receiver (.ack 1) (storeHead rel receiver 1) (fun _ => more 1 (.poll 2)) _ _ ?_ rfl rfl rfl
      (accessOK' rel w _ (by simp [storeHead, Event.accesses, head])) ?_ (.store _ _ _ _))
    (appendRuns (finishTurn w _ sender ?_) (finishTurn w _ receiver ?_)))))))))))), ?_, ?_⟩
  all_goals first
    | exact allMilestones
    | exact fun _ _ _ _ => notInFlight _ _ (by
        simp [Machine.trace, opened, fired, Launch.initial, segOcc, Occurrence.event?, loadTail,
          writeSlot, publishTail, waitRoom, readSlot, storeHead])
    | solve | simp [fired, opened, Launch.initial, launch, Function.update, sender, receiver,
          more, tokens, afterPoll, CellWrites.read_same]
    | solve | simp [Machine.count?, fired, opened, Launch.initial, launch, CellWrites.read_same, storeHead]
    | skip
  · constructor
    · intro a
      by_cases hs : a = sender
      · subst a; simp [opened, Function.update, nextOf, Next.cursor, sender, receiver]
      by_cases hr : a = receiver
      · subst a; simp [opened, Function.update, nextOf, Next.cursor]
      simp [opened, fired, Function.update, Launch.initial, launch, hs, hr]
    · simp [fired, opened, Launch.initial]

#print axioms completeScheduled

end SingleSlotWitness
end VeriTile.Tests.G1QueueRefinement.Dispatch
