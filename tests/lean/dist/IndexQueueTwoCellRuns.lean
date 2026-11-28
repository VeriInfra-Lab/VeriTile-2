import tests.lean.dist.IndexQueueCellsClient

namespace VeriTile.Tests.IndexQueueCells.Client
open VeriTile.Dist
open VeriTile.Triton (MemCell)
open DeepEPChannel (sender receiver tail head slot rel acq segOcc emptySegment)

def tokenEvent : Nat → Occurrence
  | 0 => .issued sender (written sender slot 11)
  | 1 => .issued sender (written sender metadata 29)
  | 2 => .issued sender (written sender tail 1 rel)
  | 3 => .issued receiver awaitTail
  | 4 => .issued receiver (loadData slot)
  | 5 => .issued receiver (loadData metadata)
  | _ => .issued receiver (written receiver head 1 rel)

/-- The scheduler may open or finish either agent's empty segment between any two
physical events. Positions refer to the actual, unfiltered history. -/
structure TokenTrace (n : Nat) (h : History) where
  bound : n ≤ 7
  pos : Nat → Nat
  atEvent : ∀ i, i < n → h[pos i]? = some (tokenEvent i)
  ordered : ∀ i j, i < j → j < n → pos i < pos j
  covers : ∀ u x, h[u]? = some x → (∃ a, x = segOcc a) ∨ ∃ i < n, u = pos i

private def startTrace : TokenTrace 0 [] where
  bound := by decide
  pos _ := 0
  atEvent _ := by omega
  ordered _ _ := by omega
  covers _ _ h := by simp at h

private theorem inRange (t : TokenTrace n h) (i) (hi : i < n) : t.pos i < h.length :=
  List.getElem?_eq_some_iff.mp (t.atEvent i hi) |>.1

private def TokenTrace.segment (t : TokenTrace n h) (a) : TokenTrace n (h ++ [segOcc a]) where
  bound := t.bound
  pos := t.pos
  atEvent i hi := by rw [List.getElem?_append_left (inRange t i hi)]; exact t.atEvent i hi
  ordered := t.ordered
  covers u x entry := by
    by_cases earlier : u < h.length
    · exact t.covers u x (by rwa [List.getElem?_append_left earlier] at entry)
    · have hu := (List.getElem?_eq_some_iff.mp entry).1
      simp only [List.length_append,List.length_singleton] at hu
      have : u = h.length := by omega
      subst u
      simp at entry
      exact Or.inl ⟨a, entry.symm⟩

private def TokenTrace.advance (t : TokenTrace n h) (hn : n < 7) :
    TokenTrace (n + 1) (h ++ [tokenEvent n]) where
  bound := by omega
  pos i := if i = n then h.length else t.pos i
  atEvent i hi := by
    by_cases eq : i = n
    · subst i; simp
    · simp [eq, List.getElem?_append_left (inRange t i (by omega)),t.atEvent i (by omega)]
  ordered i j lt bound := by
    have ne : i ≠ n := by omega
    by_cases eq : j = n
    · simpa [eq,ne] using inRange t i (by omega)
    · simpa [eq,ne] using t.ordered i j lt (by omega)
  covers u x entry := by
    by_cases earlier : u < h.length
    · rcases t.covers u x (by rwa [List.getElem?_append_left earlier] at entry) with quiet | ⟨i,hi,atI⟩
      · exact Or.inl quiet
      · exact Or.inr ⟨i,by omega,by simpa [Nat.ne_of_lt hi] using atI⟩
    · have hu := (List.getElem?_eq_some_iff.mp entry).1
      simp only [List.length_append,List.length_singleton] at hu
      exact Or.inr ⟨n,by omega,by simp; omega⟩

private def sendAt (n : Nat) := min n 3
private def recvAt (n : Nat) := n - 3
private def tailAt (n : Nat) := if n < 3 then 0 else 1

private def AtPC (a : Agent) (i : Nat) (actual : Option (Cursor PC)) : Prop :=
  ∃ vals : List MemCell, actual = some (.ready (i,vals)) ∨
    actual = (next (emissions false a) (i,vals)).cursor

private structure Fits (n : Nat) (s : Config PC) : Prop where
  tailWord : (s.mem.cell tail).readAs .nat = some (tailAt n)
  clear : s.pending = []
  send : AtPC sender (sendAt n) (s.pc sender)
  recv : AtPC receiver (recvAt n) (s.pc receiver)
  idle : ∀ a, a ≠ sender → a ≠ receiver → s.pc a = none

private theorem atReady {a i actual} {p : PC} (ok : AtPC a i actual)
    (ready : actual = some (.ready p)) : p.1 = i := by
  obtain ⟨v,eq | eq⟩ := ok
  · rw [eq] at ready; cases ready; rfl
  · rw [eq] at ready; cases code : next (emissions false a) (i,v) <;> rw [code] at ready <;> cases ready

private theorem atWaiting {a i actual e es k} (ok : AtPC a i actual)
    (wait : actual = some (.waiting e es k)) :
    ∃ v, next (emissions false a) (i,v) = .emitGroup e es k := by
  obtain ⟨v,eq | eq⟩ := ok
  · rw [eq] at wait; cases wait
  · rw [eq] at wait; cases code : next (emissions false a) (i,v) <;> rw [code] at wait <;> cases wait
    exact ⟨v,code⟩

private theorem sender_ne : sender ≠ receiver := by decide
private theorem receiver_ne : receiver ≠ sender := Ne.symm sender_ne

private theorem initialFit (w : CellWrites) (s : DistState) (ht : (s.cell tail).readAs .nat = some 0) :
    Fits 0 ((launch false w).initial s) := by
  refine ⟨ht,rfl,⟨[],Or.inl ?_⟩,⟨[],Or.inl ?_⟩,?_⟩
  · simp [Launch.initial,launch,sendAt]
  · simp [Launch.initial,launch,recvAt]
  · intro a hs hr; simp [Launch.initial,launch,hs,hr]

private def openSegment (s : Config PC) (a : Agent) (p : PC) : Config PC :=
  {s with history := s.history ++ [segOcc a], pc := Function.update s.pc a (next (emissions false a) p).cursor}

private theorem fitOpen (f : Fits n s) (ready : s.pc a = some (.ready p)) : Fits n (openSegment s a p) := by
  refine ⟨f.tailWord,f.clear,?_,?_,?_⟩
  · by_cases ha : a = sender
    · subst a; exact ⟨p.2,Or.inr (by simp [openSegment,← atReady f.send ready])⟩
    · simpa [openSegment,Ne.symm ha] using f.send
  · by_cases ha : a = receiver
    · subst a; exact ⟨p.2,Or.inr (by simp [openSegment,← atReady f.recv ready])⟩
    · simpa [openSegment,Ne.symm ha] using f.recv
  · intro b hs hr; by_cases ha : b = a
    · subst b; rw [f.idle _ hs hr] at ready; contradiction
    · simpa [openSegment,ha] using f.idle b hs hr

private def fired (s : Config PC) (a : Agent) (e : Emission) (mem : DistState) (p : PC) : Config PC :=
  {s with mem := mem, history := s.history ++ [.issued a e], pc := Function.update s.pc a (some (.ready p))}

private theorem fitSend (f : Fits n s) (ht : (m.cell tail).readAs .nat = some (tailAt (n+1)))
    (pc : p.1 = sendAt (n+1)) (other : recvAt n = recvAt (n+1)) :
    Fits (n+1) (fired s sender e m p) := by
  refine ⟨ht,f.clear,⟨p.2,Or.inl (by simp [fired,← pc])⟩,?_,?_⟩
  · simpa [fired,receiver_ne,← other] using f.recv
  · intro a hs hr; simpa [fired,hs] using f.idle a hs hr

private theorem fitRecv (f : Fits n s) (ht : (m.cell tail).readAs .nat = some (tailAt (n+1)))
    (pc : p.1 = recvAt (n+1)) (other : sendAt n = sendAt (n+1)) :
    Fits (n+1) (fired s receiver e m p) := by
  refine ⟨ht,f.clear,?_,⟨p.2,Or.inl (by simp [fired,← pc])⟩,?_⟩
  · simpa [fired,sender_ne,← other] using f.send
  · intro a hs hr; simpa [fired,hr] using f.idle a hs hr

private abbrev Reach (s : Config PC) := ∃ n, Nonempty (TokenTrace n s.history) ∧ Fits n s

private theorem tail_ne_slot : tail ≠ slot := by decide
private theorem tail_ne_meta : tail ≠ metadata := by decide
private theorem tail_ne_head : tail ≠ head := by decide

private theorem sendStep {w : CellWrites} {s : Config PC} (trace : TokenTrace n s.history) (f : Fits n s)
    (code : next (emissions false sender) (sendAt n,v) = .emitGroup e es k)
    (group : FireGroup (launch false w) sender s.toMachine (e :: es) final vs) :
    Reach {final with pc := Function.update s.pc sender (some (.ready (k vs)))} := by
  have bound := trace.bound
  have ht := f.tailWord
  interval_cases n <;> simp [sendAt,next,emissions] at code <;> try contradiction
  all_goals obtain ⟨rfl,rfl,rfl⟩ := code
  all_goals (cases group; rename_i access available ordered fire rest; cases rest; cases fire)
  all_goals refine ⟨_,⟨trace.advance (by decide)⟩,fitSend f ?_ rfl rfl⟩
  all_goals first
    | solve | simp [launch,CellWrites.read_same,tailAt]
    | simpa [launch,CellWrites.read_other,tail_ne_slot,tail_ne_meta,tailAt] using ht

private theorem recvStep {w : CellWrites} {s : Config PC} (trace : TokenTrace n s.history) (f : Fits n s)
    (code : next (emissions false receiver) (recvAt n,v) = .emitGroup e es k)
    (group : FireGroup (launch false w) receiver s.toMachine (e :: es) final vs) :
    Reach {final with pc := Function.update s.pc receiver (some (.ready (k vs)))} := by
  have bound := trace.bound
  have ht := f.tailWord
  interval_cases n <;> simp [recvAt,next,emissions,receiver_ne] at code <;> try contradiction
  all_goals obtain ⟨rfl,rfl,rfl⟩ := code
  all_goals (cases group; rename_i access available ordered fire rest; cases rest; cases fire)
  all_goals first
    | exact False.elim (by
        rename_i old read enabled
        simp [Machine.count?, ht, tailAt, Cmp.holds] at read enabled
        omega)
    | refine ⟨_,⟨trace.advance (by decide)⟩,fitRecv f ?_ rfl rfl⟩
  all_goals first
    | exact ht
    | simpa [launch,CellWrites.read_other,tail_ne_head,tailAt] using ht

private theorem stepReach {w : CellWrites} {s t : Config PC} {c} (r : Reach s)
    (st : step (launch false w) s c t) : Reach t := by
  obtain ⟨n,⟨tr⟩,f⟩ := r
  cases st with
  | segment ready code _ _ success =>
    rw [code] at success ⊢
    change some _ = some _ at success
    cases success
    exact ⟨n,⟨tr.segment _⟩,fitOpen f ready⟩
  | @fire a h t k final vs waiting owned group =>
    by_cases hs : a = sender
    · subst a; obtain ⟨v,code⟩ := atWaiting f.send waiting; exact sendStep tr f code group
    by_cases hr : a = receiver
    · subst a; obtain ⟨v,code⟩ := atWaiting f.recv waiting; exact recvStep tr f code group
    rw [f.idle a hs hr] at waiting; contradiction
  | deliver outstanding _ _ _ _ _ _ => rw [f.clear] at outstanding; simp at outstanding

theorem tokenTrace (w : CellWrites) (s : DistState) (ht : (s.cell tail).readAs .nat = some 0)
    (run : Run (launch false w) ((launch false w).initial s) sched final) :
    ∃ n, Nonempty (TokenTrace n final.history) := by
  have moves {a b : Config PC} {cs} (r : Run (launch false w) a cs b) : Reach a → Reach b := by
    induction r with
    | nil => exact id
    | cons step _ ih => exact fun start => ih (stepReach start step)
  obtain ⟨n,tr,_⟩ := moves run ⟨0,⟨startTrace⟩,initialFit w s ht⟩
  exact ⟨n,tr⟩

end VeriTile.Tests.IndexQueueCells.Client
