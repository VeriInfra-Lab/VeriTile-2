import tests.lean.dist.IndexQueueSingleSlotModel

namespace VeriTile.Tests.G1QueueRefinement.Dispatch
open VeriTile.Dist
open VeriTile.Triton (MemCell)
open DeepEPChannel (PC sender receiver tail head slot writeSlot publishTail waitRoom loadTail
  readSlot afterPoll more tokens rel emptySegment)

/-- Local continuations after the n-th successful protocol event. A segment can prepare
that continuation's group while the other program is running. -/
private def sendAt : Nat → PC
  | 0 => .write 0
  | 1 => .publish 0
  | 2 | 3 | 4 | 5 => .room 1
  | 6 => .write 1
  | 7 => .publish 1
  | _ => .done

private def recvAt : Nat → PC
  | 0 | 1 | 2 => .poll 0
  | 3 => .read 0
  | 4 => .ack 0
  | 5 | 6 | 7 | 8 => .poll 1
  | 9 => .read 1
  | 10 => .ack 1
  | _ => .done

private def tailAt (n : Nat) := if n < 2 then 0 else if n < 8 then 1 else 2
private def headAt (n : Nat) := if n < 5 then 0 else if n < 11 then 1 else 2

private def AtPC (a : Agent) (pc : PC) (actual : Option (Cursor PC)) : Prop :=
  actual = some (.ready pc) ∨ actual = (nextOf rel a pc).cursor

private structure Fits (n : Nat) (s : Config PC) : Prop where
  bound : n ≤ 11
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
  · rw [eq] at ready; cases code : nextOf rel a p <;> rw [code] at ready <;> cases ready

private theorem atWaiting {a p h t k cur} (fit : AtPC a p cur)
    (wait : cur = some (.waiting h t k)) : nextOf rel a p = .emitGroup h t k := by
  rcases fit with eq | eq
  · rw [eq] at wait; cases wait
  · rw [eq] at wait
    cases code : nextOf rel a p <;> rw [code] at wait <;> cases wait
    rfl

private theorem sender_ne : sender ≠ receiver := by decide
private theorem receiver_ne : receiver ≠ sender := Ne.symm sender_ne

private theorem atInitial (w : CellWrites) (s : DistState)
    (ht : (s.cell tail).readAs .nat = some 0) (hh : (s.cell head).readAs .nat = some 0) :
    Fits 0 ((launch rel w).initial s) := by
  refine ⟨by decide, ht, hh, rfl, Or.inl ?_, Or.inl ?_, ?_⟩
  · simp [Launch.initial, launch, sendAt]
  · simp [Launch.initial, launch, recvAt, receiver_ne]
  · intro a hs hr; simp [Launch.initial, launch, hs, hr]

private def opened (s : Config PC) (a : Agent) (p : PC) : Config PC :=
  {s with history := s.history ++ [.segment a ∅ ∅],
          pc := Function.update s.pc a (nextOf rel a p).cursor}

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

private theorem fitSend (f : Fits n s) (hn : n' ≤ 11)
    (ht : (m.cell tail).readAs .nat = some (tailAt n'))
    (hh : (m.cell head).readAs .nat = some (headAt n'))
    (pc : p = sendAt n') (other : recvAt n = recvAt n') :
    Fits n' (fired s sender e m p) := by
  refine ⟨hn, ht, hh, f.clear, Or.inl ?_, ?_, ?_⟩
  · simp [fired, pc]
  · simpa [fired, receiver_ne, ← other] using f.recv
  · intro a hs hr; simpa [fired, hs] using f.idle a hs hr

private theorem fitRecv (f : Fits n s) (hn : n' ≤ 11)
    (ht : (m.cell tail).readAs .nat = some (tailAt n'))
    (hh : (m.cell head).readAs .nat = some (headAt n'))
    (pc : p = recvAt n') (other : sendAt n = sendAt n') :
    Fits n' (fired s receiver e m p) := by
  refine ⟨hn, ht, hh, f.clear, ?_, Or.inl ?_, ?_⟩
  · simpa [fired, sender_ne, ← other] using f.send
  · simp [fired, pc]
  · intro a hs hr; simpa [fired, hr] using f.idle a hs hr

private abbrev Reach (s : Config PC) := ∃ n, Prefix n s.history ∧ Fits n s

private theorem tail_ne_slot : tail ≠ slot := by decide
private theorem head_ne_slot : head ≠ slot := by decide
private theorem tail_ne_head : tail ≠ head := by decide

-- A store at either counter or the data slot updates exactly one cell.
private theorem sendStep {w : CellWrites} {s : Config PC} (traceOk : Prefix n s.history) (f : Fits n s)
    (code : nextOf rel sender (sendAt n) = .emitGroup e es k)
    (group : FireGroup (launch rel w) sender s.toMachine (e :: es) final vs) :
    Reach { final with pc := Function.update s.pc sender (some (.ready (k vs))) } := by
  have bound := f.bound
  have ht := f.tailWord
  have hh := f.headWord
  interval_cases n <;> simp only [sendAt, nextOf, reduceCtorEq] at code <;> try contradiction
  all_goals cases code
  all_goals (cases group; rename_i access available ordered fire rest; cases rest; cases fire)
  all_goals first
    | exact False.elim (by
        rename_i old read enabled
        simp [Machine.count?, hh, headAt, Cmp.holds] at read enabled
        omega)
    | refine ⟨_, Prefix.advance traceOk (by decide), fitSend f (by decide) ?_ ?_ ?_ rfl⟩
  all_goals first
    | rfl
    | solve | simp [launch, CellWrites.read_same, tailAt]
    | simpa [launch, CellWrites.read_same, CellWrites.read_other, tail_ne_slot, head_ne_slot,
        tail_ne_head, Ne.symm tail_ne_head, headAt, tailAt] using ht
    | simpa [launch, CellWrites.read_same, CellWrites.read_other, tail_ne_slot, head_ne_slot,
        tail_ne_head, Ne.symm tail_ne_head, headAt, tailAt] using hh

private theorem recvStep {w : CellWrites} {s : Config PC} (traceOk : Prefix n s.history) (f : Fits n s)
    (code : nextOf rel receiver (recvAt n) = .emitGroup e es k)
    (group : FireGroup (launch rel w) receiver s.toMachine (e :: es) final vs) :
    Reach { final with pc := Function.update s.pc receiver (some (.ready (k vs))) } := by
  have bound := f.bound
  have ht := f.tailWord
  have hh := f.headWord
  interval_cases n <;> simp only [recvAt, nextOf, reduceCtorEq] at code <;> try contradiction
  all_goals cases code
  all_goals (cases group; rename_i access available ordered fire rest; cases rest; cases fire)
  all_goals first
    | refine ⟨_, Prefix.advance traceOk (by decide), fitRecv f (by decide) ?_ ?_ ?_ rfl⟩
    | refine ⟨_, Prefix.noise traceOk Noise.poll, fitRecv f f.bound ?_ ?_ ?_ rfl⟩
  all_goals first
    | rfl
    | exact ht
    | exact hh
    | solve | simp [recvAt, afterPoll, ht, headAt, tailAt]
    | simpa [launch, CellWrites.read_other, tail_ne_head, headAt, tailAt] using ht
    | simp [launch, CellWrites.read_same, headAt]

private theorem stepReach {w : CellWrites} {s t : Config PC} {c} (r : Reach s)
    (st : step (launch rel w) s c t) : Reach t := by
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

private theorem runReach {w : CellWrites} {s t : Config PC} (run : Run (launch rel w) s sched t) :
    Reach s → Reach t := by
  induction run with
  | nil => exact id
  | cons st _ ih => exact fun r => ih (stepReach r st)

theorem runPrefix (w : CellWrites) (s : DistState)
    (ht : (s.cell tail).readAs .nat = some 0) (hh : (s.cell head).readAs .nat = some 0)
    (run : Run (launch rel w) ((launch rel w).initial s) sched final) :
    ∃ n, Prefix n final.history := by
  obtain ⟨n, tr, _⟩ := runReach run ⟨0, .start, atInitial w s ht hh⟩
  exact ⟨n, tr⟩

theorem completePrefix (w : CellWrites) (s : DistState)
    (ht : (s.cell tail).readAs .nat = some 0) (hh : (s.cell head).readAs .nat = some 0)
    (run : Run (launch rel w) ((launch rel w).initial s) sched final)
    (done : Complete final) : Prefix 11 final.history := by
  obtain ⟨n, tr, f⟩ := runReach run ⟨0, .start, atInitial w s ht hh⟩
  have bound := f.bound
  have recv := f.recv
  rw [done.1 receiver] at recv
  interval_cases n <;> first | exact tr | simp [AtPC, recvAt, nextOf, Next.cursor] at recv


end VeriTile.Tests.G1QueueRefinement.Dispatch
