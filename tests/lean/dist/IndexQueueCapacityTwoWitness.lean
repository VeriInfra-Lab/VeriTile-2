import tests.lean.dist.IndexQueueCapacityTwoModel

/-! Actual capacity-two schedules: batch, acknowledge, and reuse the first physical slot. -/
namespace VeriTile.Tests.G1QueueRefinement.CapacityTwo
open VeriTile.Dist
open VeriTile.Triton (MemCell)
open VeriTile.Tests.DeepEPChannel (sender receiver head tail slot rel acq publishTail loadTail waitRoom
  emptySegment segOcc appendRuns own notInFlight)

private def opened (threshold : Nat) (s : Config PC) (a : Agent) (pc : PC) : Config PC :=
  { s with history := s.history ++ [segOcc a],
           pc := Function.update s.pc a ((next threshold a pc).cursor) }

private def fired (s : Config PC) (a : Agent) (e : Emission) (mem : DistState) (pc : PC) : Config PC :=
  { s with mem := mem, history := s.history ++ [.issued a e],
           pc := Function.update s.pc a (some (.ready pc)) }

private theorem oneEvent (threshold : Nat) (w : CellWrites) (s : Config PC) (a : Agent) (pc : PC) (e : Emission)
    (k : List (Option MemCell) → PC) (mem : DistState) (v : Option MemCell)
    (ready : s.pc a = some (.ready pc)) (code : next threshold a pc = .emitGroup e [] k)
    (clear : s.pending = []) (actor : e.actor = a)
    (access : e.event.AccessibleBy (launch threshold w).symm e.actor)
    (free : ∀ kd p m, (kd, p, m) ∈ e.event.accesses → ¬ InFlight (opened threshold s a pc).trace p)
    (fire : Fire (launch threshold w) (opened threshold s a pc).toMachine e mem (opened threshold s a pc).pending v) :
    Run (launch threshold w) s [.agent a, .agent a] (fired (opened threshold s a pc) a e mem (k [v])) := by
  refine .cons (t := opened threshold s a pc)
    (.segment ready rfl rfl (by simp [launch, emptySegment]) rfl) ?_
  refine .cons (t := fired (opened threshold s a pc) a e mem (k [v]))
    (.fire (s := opened threshold s a pc) (a := a) (h := e) (t := []) (k := k) (values := [v])
      (by simp [opened, code, Next.cursor]) ?_ ?_) (.nil _)
  · intro x hx
    simp at hx
    subst hx
    rw [actor]
    exact own a
  · exact .cons access free (by simp [PendingFence, opened, clear]) fire (.nil _)

private theorem queueAccess (threshold : Nat) (w : CellWrites) (e : Emission)
    (h : ∀ x ∈ e.event.accesses, x.2.1.space = .global 1) :
    e.event.AccessibleBy (launch threshold w).symm e.actor :=
  fun kd p m hm => DeepEPChannel.reachable _ _ (h (kd, p, m) hm)

private theorem finishTurn (w : CellWrites) (s : Config PC) (a : Agent)
    (ready : s.pc a = some (.ready .done)) :
    Run (launch 1 w) s [.agent a] (opened 1 s a .done) :=
  .cons (.segment ready rfl rfl (by simp [launch, emptySegment]) rfl) (.nil _)

private def positiveHistory : History :=
  ((List.range 13).flatMap fun i => [segOcc (milestone i).owner, milestone i]) ++
    [segOcc sender,segOcc receiver]

private def earlyHistory : History :=
  [put sender 0, put sender 1, publishTail sender 1, waitRoom sender 0, put sender 2].flatMap
    fun e => [segOcc sender, .issued sender e]

private theorem slot_ne_head (i : Nat) : queue.slotOf i ≠ head := queue.slot_ne_head _
private theorem head_ne_tail : head ≠ tail := by decide

private def machine (pcs : Agent → Option (Cursor PC)) (mem : DistState) (hist : History) : Config PC :=
  { pc := pcs, mem, history := hist }

private structure Reached (threshold : Nat) (w : CellWrites) (s : DistState)
    (pcs : Agent → Option (Cursor PC)) (mem : DistState) (hist : History) : Prop where
  run : ∃ cs, Run (launch threshold w) ((launch threshold w).initial s) cs (machine pcs mem hist)
  quiet : ∀ x ∈ hist.filterMap Occurrence.event?, ∀ t, x.2 ≠ .initiate t

private theorem start (th : Nat) (w : CellWrites) (s : DistState) :
    Reached th w s ((launch th w).initial s).pc s [] := ⟨⟨[],.nil _⟩, by simp⟩

private theorem turn (r : Reached th w s pcs mem hist) (a : Agent) (pc : PC)
    {e : Emission} {k : List (Option MemCell) → PC} {mem' v} (target : PC)
    (ready : pcs a = some (.ready pc)) (code : next th a pc = .emitGroup e [] k)
    (resume : k [v] = target) (actor : e.actor = a)
    (access : e.event.AccessibleBy (launch th w).symm e.actor) (regular : ∀ t, e.event ≠ .initiate t)
    (fire : Fire (launch th w) ⟨mem,hist ++ [segOcc a],[]⟩ e mem' [] v) :
    Reached th w s (Function.update pcs a (some (.ready target))) mem'
      (hist ++ [segOcc a, .issued a e]) := by
  obtain ⟨cs,prev⟩ := r.run
  let current := machine pcs mem hist
  have more := oneEvent th w current a pc e k mem' v ready code rfl actor access
    (fun _ p _ _ => notInFlight _ p (by simpa [opened,current,machine,Machine.trace,segOcc,Occurrence.event?] using r.quiet))
    fire
  constructor
  · refine ⟨_,appendRuns (ys := [.agent a,.agent a]) prev ?_⟩
    simpa [current,machine,fired,opened,resume,Function.update_idem,List.append_assoc] using more
  · intro x hx t
    simp [segOcc,Occurrence.event?] at hx
    rcases hx with old|rfl
    · exact r.quiet x (by simpa [Occurrence.event?] using old) t
    · exact regular t

private theorem finishBoth (r : Reached 1 w s pcs mem hist)
    (sr : pcs sender = some (.ready .done)) (rr : pcs receiver = some (.ready .done))
    (other : ∀ a, a ≠ sender → a ≠ receiver → pcs a = none) :
    ∃ cs f, Run (launch 1 w) ((launch 1 w).initial s) cs f ∧ Complete f ∧
      f.history = hist ++ [segOcc sender,segOcc receiver] := by
  obtain ⟨cs,prev⟩ := r.run
  have a := finishTurn w (machine pcs mem hist) sender sr
  have b := finishTurn w _ receiver (by simpa [opened,machine,Function.update,sender,receiver] using rr :
    (opened 1 (machine pcs mem hist) sender .done).pc receiver = some (.ready .done))
  refine ⟨_,_,appendRuns prev (appendRuns a b),⟨?_,by simp [opened,machine]⟩,by simp [opened,machine,List.append_assoc]⟩
  intro x
  by_cases h : x = sender
  · subst x; simp [opened,Function.update,next,Next.cursor,sender,receiver]
  by_cases k : x = receiver
  · subst x; simp [opened,Function.update,next,Next.cursor]
  simp [opened,machine,Function.update,h,k,other x h k]

private theorem scheduled (w : CellWrites) (s : DistState) :
    ∃ cs f, Run (launch 1 w) ((launch 1 w).initial s) cs f ∧ Complete f ∧ f.history = positiveHistory := by
  have h0 := start 1 w s
  have h1 := turn h0 sender .put0 (e := put sender 0) .put1 rfl rfl rfl rfl
    (queueAccess 1 w _ (by simp [put, Event.accesses, IndexQueue.slotOf, queue, physical, slot])) (by intro t bad; cases bad) (.store _ _ _ _)
  have h2 := turn h1 sender .put1 (e := put sender 1) .publish2 rfl rfl rfl rfl
    (queueAccess 1 w _ (by simp [put, Event.accesses, IndexQueue.slotOf, queue, physical, slot])) (by intro t bad; cases bad) (.store _ _ _ _)
  have h3 := turn h2 sender .publish2 (e := publishTail sender 1) .waitReuse rfl rfl rfl rfl
    (queueAccess 1 w _ (by simp [publishTail, Event.accesses, tail])) (by intro t bad; cases bad) (.store _ _ _ _)
  have h4 := turn h3 receiver .pollFirst (e := loadTail receiver) .take0 rfl rfl (by simp [after, launch, CellWrites.read_same]) rfl
    (queueAccess 1 w _ (by simp [loadTail, Event.accesses, tail])) (by intro t bad; cases bad) (.load _ _ _)
  have h5 := turn h4 receiver .take0 (e := take receiver 0) .take1 rfl rfl rfl rfl
    (queueAccess 1 w _ (by simp [take, Event.accesses, IndexQueue.slotOf, queue, physical, slot])) (by intro t bad; cases bad) (.load _ _ _)
  have h6 := turn h5 receiver .take1 (e := take receiver 1) .ack2 rfl rfl rfl rfl
    (queueAccess 1 w _ (by simp [take, Event.accesses, IndexQueue.slotOf, queue, physical, slot])) (by intro t bad; cases bad) (.load _ _ _)
  have h7 := turn h6 receiver .ack2 (e := ack receiver 2) .pollLast rfl rfl rfl rfl
    (queueAccess 1 w _ (by simp [ack, Event.accesses, head])) (by intro t bad; cases bad) (.store _ _ _ _)
  have h8 := turn h7 sender .waitReuse (e := waitRoom sender 1) .put2 rfl rfl rfl rfl
    (queueAccess 1 w _ (by simp [waitRoom, Event.accesses, head])) (by intro t bad; cases bad) (.wait _ _ _ _ _ 2
      (by simp [Machine.count?, launch, CellWrites.read_same]) (by decide : 1 ≤ 2))
  have h9 := turn h8 sender .put2 (e := put sender 2) .publish3 rfl rfl rfl rfl
    (queueAccess 1 w _ (by simp [put, Event.accesses, IndexQueue.slotOf, queue, physical, slot])) (by intro t bad; cases bad) (.store _ _ _ _)
  have h10 := turn h9 sender .publish3 (e := publishTail sender 2) .done rfl rfl rfl rfl
    (queueAccess 1 w _ (by simp [publishTail, Event.accesses, tail])) (by intro t bad; cases bad) (.store _ _ _ _)
  have h11 := turn h10 receiver .pollLast (e := loadTail receiver) .take2 rfl rfl (by simp [after, launch, CellWrites.read_same]) rfl
    (queueAccess 1 w _ (by simp [loadTail, Event.accesses, tail])) (by intro t bad; cases bad) (.load _ _ _)
  have h12 := turn h11 receiver .take2 (e := take receiver 2) .ack3 rfl rfl rfl rfl
    (queueAccess 1 w _ (by simp [take, Event.accesses, IndexQueue.slotOf, queue, physical, slot])) (by intro t bad; cases bad) (.load _ _ _)
  have h13 := turn h12 receiver .ack3 (e := ack receiver 3) .done rfl rfl rfl rfl
    (queueAccess 1 w _ (by simp [ack, Event.accesses, head])) (by intro t bad; cases bad) (.store _ _ _ _)
  exact finishBoth h13 rfl rfl (by intro a hs hr; simp [Function.update, Launch.initial, launch, hs, hr])

private theorem early (w : CellWrites) (s : DistState) (zero : (s.cell head).readAs .nat = some 0) :
    ∃ cs f, Run (launch 0 w) ((launch 0 w).initial s) cs f ∧ f.history = earlyHistory := by
  have h0 := start 0 w s
  have h1 := turn h0 sender .put0 (e := put sender 0) .put1 rfl rfl rfl rfl
    (queueAccess 0 w _ (by simp [put, Event.accesses, IndexQueue.slotOf, queue, physical, slot])) (by intro t bad; cases bad) (.store _ _ _ _)
  have h2 := turn h1 sender .put1 (e := put sender 1) .publish2 rfl rfl rfl rfl
    (queueAccess 0 w _ (by simp [put, Event.accesses, IndexQueue.slotOf, queue, physical, slot])) (by intro t bad; cases bad) (.store _ _ _ _)
  have h3 := turn h2 sender .publish2 (e := publishTail sender 1) .waitReuse rfl rfl rfl rfl
    (queueAccess 0 w _ (by simp [publishTail, Event.accesses, tail])) (by intro t bad; cases bad) (.store _ _ _ _)
  have h4 := turn h3 sender .waitReuse (e := waitRoom sender 0) .put2 rfl rfl rfl rfl
    (queueAccess 0 w _ (by simp [waitRoom, Event.accesses, head])) (by intro t bad; cases bad) (.wait _ _ _ _ _ 0
      (by simp [Machine.count?, launch, CellWrites.read_other, head_ne_tail, fun i => Ne.symm (slot_ne_head i), zero]) (Nat.le_refl 0))
  have h5 := turn h4 sender .put2 (e := put sender 2) .publish3 rfl rfl rfl rfl
    (queueAccess 0 w _ (by simp [put, Event.accesses, IndexQueue.slotOf, queue, physical, slot])) (by intro t bad; cases bad) (.store _ _ _ _)
  obtain ⟨cs,run⟩ := h5.run
  exact ⟨cs,_,run,rfl⟩
private theorem atToken {f : Occurrence → Bool} {h : History} {k i : Nat} {x : Occurrence}
    (pos : h[i]? = some x) (yes : f x = true) (n : (h.take i).countP f = k) : NthAt f h k i :=
  ⟨⟨x,pos,yes⟩,n⟩

/-- The receiver takes three values (40, 41, 42); put 2 reuses the cell of token 0.
The two tail polls and room wait are steps of this same completed execution. -/
theorem completeRun (w : CellWrites) (s : DistState) :
    ∃ cs f, Run (launch 1 w) ((launch 1 w).initial s) cs f ∧ Complete f ∧
      queue.view.Take f.history 0 9 ∧ queue.view.Take f.history 1 11 ∧ queue.view.Take f.history 2 23 ∧
      queue.view.Put f.history 2 17 ∧ queue.slotOf 0 = queue.slotOf 2 ∧ queue.slotOf 0 ≠ queue.slotOf 1 ∧
      IndexQueue.lastValue s f.history (queue.slotOf 0) 9 = queue.payload 0 ∧
      IndexQueue.lastValue s f.history (queue.slotOf 1) 11 = queue.payload 1 ∧
      IndexQueue.lastValue s f.history (queue.slotOf 2) 23 = queue.payload 2 := by
  obtain ⟨cs,f,run,done,trace⟩ := scheduled w s
  refine ⟨cs,f,run,done,?_⟩
  rw [trace]
  exact ⟨atToken rfl rfl rfl, atToken rfl rfl rfl, atToken rfl rfl rfl,
    atToken rfl rfl rfl, rfl, by decide, rfl,rfl,rfl⟩

private theorem noEarlyTake {k j : Nat} : ¬ queue.view.Take earlyHistory k j := by
  rintro ⟨⟨x,atX,isTake⟩,_⟩
  have mem := List.mem_of_getElem? atX
  simp [earlyHistory] at mem
  rcases mem with h|h|h|h|h|h|h|h|h|h <;> subst x <;> contradiction

/-- Threshold zero admits a sender-only ten-step prefix from a zero head. Put 2
reuses slot 0 before any take can witness the reuse clause of QueueRefines. -/
theorem thresholdZeroBreaksReuse (w : CellWrites) (s : DistState) (zero : (s.cell head).readAs .nat = some 0) :
    ¬ QueueRefines (launch 0 w) s queue.view := by
  obtain ⟨cs,f,run,trace⟩ := early w s zero
  intro refines
  have put2 : queue.view.Put f.history (0 + queue.view.cap) 9 := by rw [trace]; exact atToken rfl rfl rfl
  obtain ⟨j,take,_,_⟩ := (refines cs f run).2 0 9 put2
  exact noEarlyTake (trace ▸ take)

#print axioms completeRun
#print axioms thresholdZeroBreaksReuse

end VeriTile.Tests.G1QueueRefinement.CapacityTwo
