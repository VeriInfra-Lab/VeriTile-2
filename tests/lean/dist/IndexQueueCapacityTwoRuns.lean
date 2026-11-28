import tests.lean.dist.IndexQueueCapacityTwoModel

namespace VeriTile.Tests.G1QueueRefinement.CapacityTwo
open VeriTile.Dist
open DeepEPChannel (sender receiver tail head)

/-- Sender and receiver continuations after each successful program event. -/
private def sendAt : Nat → PC
  | 0 => .put0
  | 1 => .put1
  | 2 => .publish2
  | 3 | 4 | 5 | 6 | 7 => .waitReuse
  | 8 => .put2
  | 9 => .publish3
  | _ => .done

private def recvAt : Nat → PC
  | 0 | 1 | 2 | 3 => .pollFirst
  | 4 => .take0
  | 5 => .take1
  | 6 => .ack2
  | 7 | 8 | 9 | 10 => .pollLast
  | 11 => .take2
  | 12 => .ack3
  | _ => .done

private def tailAt (n : Nat) := if n < 3 then 0 else if n < 10 then 2 else 3
private def headAt (n : Nat) := if n < 7 then 0 else if n < 13 then 2 else 3

private def AtPC (a : Agent) (pc : PC) (actual : Option (Cursor PC)) : Prop :=
  actual = some (.ready pc) ∨ actual = (next 1 a pc).cursor

private structure Fits (n : Nat) (s : Config PC) : Prop where
  bound : n ≤ 13
  tailWord : (s.mem.cell tail).readAs .nat = some (tailAt n)
  headWord : (s.mem.cell head).readAs .nat = some (headAt n)
  clear : s.pending = []
  send : AtPC sender (sendAt n) (s.pc sender)
  recv : AtPC receiver (recvAt n) (s.pc receiver)
  idle : ∀ a, a ≠ sender → a ≠ receiver → s.pc a = none

private theorem atReady {a p q cur} (fit : AtPC a p cur) (ready : cur = some (.ready q)) :
    q = p := by
  rcases fit with eq | eq
  · rw [eq] at ready; cases ready; rfl
  · rw [eq] at ready; cases code : next 1 a p <;> rw [code] at ready <;> cases ready

private theorem atWaiting {a p h t k cur} (fit : AtPC a p cur)
    (wait : cur = some (.waiting h t k)) : next 1 a p = .emitGroup h t k := by
  rcases fit with eq | eq
  · rw [eq] at wait; cases wait
  · rw [eq] at wait
    cases code : next 1 a p <;> rw [code] at wait <;> cases wait
    rfl

private theorem sender_ne : sender ≠ receiver := by decide
private theorem receiver_ne : receiver ≠ sender := Ne.symm sender_ne

private theorem atInitial (w : CellWrites) (s : DistState)
    (ht : (s.cell tail).readAs .nat = some 0) (hh : (s.cell head).readAs .nat = some 0) :
    Fits 0 ((launch 1 w).initial s) := by
  refine ⟨by decide, ht, hh, rfl, Or.inl ?_, Or.inl ?_, ?_⟩
  · simp [Launch.initial, launch, sendAt]
  · simp [Launch.initial, launch, recvAt, receiver_ne]
  · intro a hs hr; simp [Launch.initial, launch, hs, hr]

private def opened (s : Config PC) (a : Agent) (p : PC) : Config PC :=
  {s with history := s.history ++ [.segment a ∅ ∅],
          pc := Function.update s.pc a (next 1 a p).cursor}

private theorem fitOpen (f : Fits n s) (ready : s.pc a = some (.ready p)) :
    Fits n (opened s a p) := by
  refine ⟨f.bound, f.tailWord, f.headWord, f.clear, ?_, ?_, ?_⟩
  · by_cases h : a = sender
    · subst a; rw [atReady f.send ready]; exact Or.inr (by simp [opened])
    · simpa [opened, Function.update_of_ne (Ne.symm h)] using f.send
  · by_cases h : a = receiver
    · subst a; rw [atReady f.recv ready]; exact Or.inr (by simp [opened])
    · simpa [opened, Function.update_of_ne (Ne.symm h)] using f.recv
  · intro b hs hr
    by_cases h : b = a
    · subst b; rw [f.idle a hs hr] at ready; contradiction
    · simpa [opened, Function.update_of_ne h] using f.idle b hs hr

private def fired (s : Config PC) (a : Agent) (e : Emission) (m : DistState)
    (p : PC) : Config PC :=
  { s with mem := m, history := s.history ++ [.issued a e],
           pc := Function.update s.pc a (some (.ready p)) }

private theorem fitSend (f : Fits n s) (hn : n' ≤ 13)
    (ht : (m.cell tail).readAs .nat = some (tailAt n'))
    (hh : (m.cell head).readAs .nat = some (headAt n'))
    (pc : p = sendAt n') (other : recvAt n = recvAt n') :
    Fits n' (fired s sender e m p) := by
  refine ⟨hn, ht, hh, f.clear, Or.inl ?_, ?_, ?_⟩
  · simp [fired, pc]
  · simpa [fired, receiver_ne, ← other] using f.recv
  · intro a hs hr; simpa [fired, hs] using f.idle a hs hr

private theorem fitRecv (f : Fits n s) (hn : n' ≤ 13)
    (ht : (m.cell tail).readAs .nat = some (tailAt n'))
    (hh : (m.cell head).readAs .nat = some (headAt n'))
    (pc : p = recvAt n') (other : sendAt n = sendAt n') :
    Fits n' (fired s receiver e m p) := by
  refine ⟨hn, ht, hh, f.clear, ?_, Or.inl ?_, ?_⟩
  · simpa [fired, sender_ne, ← other] using f.send
  · simp [fired, pc]
  · intro a hs hr; simpa [fired, hr] using f.idle a hs hr

private abbrev Reach (s : Config PC) := ∃ n, Prefix n s.history ∧ Fits n s

private theorem tail_ne_slot (n : Nat) : tail ≠ queue.slotOf n := Ne.symm (queue.slot_ne_tail _)
private theorem head_ne_slot (n : Nat) : head ≠ queue.slotOf n := Ne.symm (queue.slot_ne_head _)
private theorem tail_ne_head : tail ≠ head := by decide

-- Writing either data slot preserves both counter words.
private theorem sendStep {w : CellWrites} {s : Config PC} (traceOk : Prefix n s.history) (f : Fits n s)
    (code : next 1 sender (sendAt n) = .emitGroup e es k)
    (group : FireGroup (launch 1 w) sender s.toMachine (e :: es) final vs) :
    Reach { final with pc := Function.update s.pc sender (some (.ready (k vs))) } := by
  have bound := f.bound
  have ht := f.tailWord
  have hh := f.headWord
  interval_cases n <;> simp only [sendAt, next, reduceCtorEq] at code <;> try contradiction
  all_goals cases code
  all_goals (cases group; rename_i access available ordered fire rest; cases rest; cases fire)
  all_goals first
    | exact False.elim (by
        rename_i old read enabled
        simp [Machine.count?, hh, headAt, Cmp.holds] at read enabled
        omega)
    | refine ⟨_, MilestonePrefix.advance traceOk (by decide), fitSend f (by decide) ?_ ?_ ?_ rfl⟩
  all_goals first
    | rfl
    | solve | simp [launch, CellWrites.read_same, tailAt]
    | simpa [launch, CellWrites.read_same, CellWrites.read_other, tail_ne_slot, head_ne_slot,
        tail_ne_head, Ne.symm tail_ne_head, headAt, tailAt] using ht
    | simpa [launch, CellWrites.read_same, CellWrites.read_other, tail_ne_slot, head_ne_slot,
        tail_ne_head, Ne.symm tail_ne_head, headAt, tailAt] using hh

private theorem recvStep {w : CellWrites} {s : Config PC} (traceOk : Prefix n s.history) (f : Fits n s)
    (code : next 1 receiver (recvAt n) = .emitGroup e es k)
    (group : FireGroup (launch 1 w) receiver s.toMachine (e :: es) final vs) :
    Reach { final with pc := Function.update s.pc receiver (some (.ready (k vs))) } := by
  have bound := f.bound
  have ht := f.tailWord
  have hh := f.headWord
  interval_cases n <;> simp only [recvAt, next, reduceCtorEq] at code <;> try contradiction
  all_goals cases code
  all_goals (cases group; rename_i access available ordered fire rest; cases rest; cases fire)
  all_goals first
    | refine ⟨_, MilestonePrefix.advance traceOk (by decide), fitRecv f (by decide) ?_ ?_ ?_ rfl⟩
    | refine ⟨_, MilestonePrefix.noise traceOk Dispatch.Noise.poll, fitRecv f f.bound ?_ ?_ ?_ rfl⟩
  all_goals first
    | rfl
    | exact ht
    | exact hh
    | solve | simp [recvAt, after, ht, headAt, tailAt]
    | simpa [launch, CellWrites.read_other, tail_ne_head, headAt, tailAt] using ht
    | simp [launch, CellWrites.read_same, headAt]

private theorem stepReach {w : CellWrites} {s t : Config PC} {c} (r : Reach s)
    (st : step (launch 1 w) s c t) : Reach t := by
  obtain ⟨n, traceOk, f⟩ := r
  cases st with
  | segment ready code _ _ success =>
    rw [code] at success ⊢
    change some _ = some _ at success
    cases success
    exact ⟨n, .noise traceOk (.segment _), fitOpen f ready⟩
  | @fire a h t k final values waiting owned group =>
    by_cases hs : a = sender
    · subst a; exact sendStep traceOk f (atWaiting f.send waiting) group
    by_cases hr : a = receiver
    · subst a; exact recvStep traceOk f (atWaiting f.recv waiting) group
    rw [f.idle a hs hr] at waiting
    contradiction
  | deliver outstanding _ _ _ _ _ _ =>
    rw [f.clear] at outstanding
    simp at outstanding

private theorem runReach {w : CellWrites} {s t : Config PC} (run : Run (launch 1 w) s sched t) :
    Reach s → Reach t := by
  induction run with
  | nil => exact id
  | cons st _ ih => exact fun r => ih (stepReach r st)

/-- Every run has a prefix, including runs with arbitrarily many poll retries. -/
theorem runPrefix (w : CellWrites) (s : DistState)
    (ht : (s.cell tail).readAs .nat = some 0) (hh : (s.cell head).readAs .nat = some 0)
    (run : Run (launch 1 w) ((launch 1 w).initial s) sched final) :
    ∃ n, Prefix n final.history := by
  obtain ⟨n, tr, _⟩ := runReach run ⟨0, .start, atInitial w s ht hh⟩
  exact ⟨n, tr⟩

/-- A completed receiver has executed its third acknowledgement. -/
theorem completePrefix (w : CellWrites) (s : DistState)
    (ht : (s.cell tail).readAs .nat = some 0) (hh : (s.cell head).readAs .nat = some 0)
    (run : Run (launch 1 w) ((launch 1 w).initial s) sched final)
    (done : Complete final) : Prefix 13 final.history := by
  obtain ⟨n, tr, f⟩ := runReach run ⟨0, .start, atInitial w s ht hh⟩
  have bound := f.bound
  have recv := f.recv
  rw [done.1 receiver] at recv
  interval_cases n <;> first | exact tr | simp [AtPC, recvAt, next, Next.cursor] at recv

#print axioms runPrefix
#print axioms completePrefix
end VeriTile.Tests.G1QueueRefinement.CapacityTwo
