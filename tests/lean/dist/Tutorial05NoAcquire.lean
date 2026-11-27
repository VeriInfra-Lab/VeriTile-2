import tests.lean.dist.Tutorial05Whole

/-! The signed scheduler runs a concrete instance of the same T05 program after removal
of the receiving CAS. The two-rank, two-lane instance keeps the CTA phase and stream
handoffs. The physical inputs are already present and the remote shard starts stale. -/
namespace VeriTile.Tests.T05Pilot.Whole.NoAcquire
open VeriTile.Dist
open VeriTile.Triton (MemCell)
open VeriTile.Tests.E2ReadsFromDetermined (Quiet quiet_free quiet_snoc emptySeg)
open VeriTile.Tests.FetchAddObservation (putCellWrites)
noncomputable section
private abbrev L := launch false 2 2 1 1 putCellWrites
private abbrev coord : Coordinate 1 1 := (0,0)
private abbrev H (r : Nat) := Stream.host r
private abbrev A (t : Nat) := Stream.lane 0 t
private abbrev T := Stream.tile 0 0
private def origin : DistState :=
  { numRanks := 2, context := (DistState.single default).context,
    cell := fun p => if p.region = "flag" ∨ p.region = "T05.stream.shadow" then .of .nat 0
                     else if p.region = "input" ∧ p.space = .global 1 then finiteCell 1 else finiteCell 0 }
private def data (r : Fin 2) (_ : Fin (2*1) × Fin 1) : ℝ := if r.val = 1 then 1 else 0
private theorem permitted : Initial data origin := by
  constructor
  · intro src peer u; fin_cases src <;> simp [data, origin, inputSlot, finiteCell]
  · intro r peer; simp [origin, VeriTile.Tests.E2ReadsFromDetermined.flag]
  · intro rank stage; simp [origin, Stream.mark]

private theorem hostZero : (hostCopySeg 1 1 (0 : Fin 2)).run origin = some origin := by
  obtain ⟨out,run⟩ := hostCopy_runs 1 1 (0 : Fin 2) origin
  have cells : out.cell = origin.cell := by
    funext p
    by_cases w : p ∈ copyWrites 1 1 (0 : Fin 2)
    · obtain ⟨peer,u,rfl⟩ := w
      rw [hostCopy_at _ _ _ run]
      simp [origin,inputSlot,scatterSlot]
    · exact hostCopy_frame _ run w
  rw [run]; congr 1
  have nr : out.numRanks = origin.numRanks := by cases run; rfl
  have ctx : out.context = origin.context := by cases run; rfl
  cases out
  congr

/-- Each entry gives the observation to the actual Fire rule. The machine verifies it
on every successful wait and add. CAS sets ignore the old value. -/
private inductive Op where
  | wait (c : Counter) (cmp : Cmp) (n : Nat) (mode : Mode) (old : Nat)
  | bump (b : Bump) (old : Nat)

private def Op.emit (a : Agent) : Op → Emission
  | .wait c cmp n md _ => ⟨a,.wait c cmp n md,.noValue⟩
  | .bump b _ => ⟨a,.bump b,.noValue⟩

private def Op.value : Op → Option MemCell
  | .wait (.word _) _ _ _ old => some (.of .nat old)
  | .bump ⟨.word _, .add, _, _⟩ old => some (.of .nat old)
  | _ => none

private def Op.mem (s : DistState) : Op → DistState
  | .bump ⟨.word p,op,n,_⟩ old => s.putCell p (.of .nat (op.apply old n))
  | _ => s

private def Op.Enabled (s : Machine) : Op → Prop
  | .wait c cmp n _ old => s.count? L.initialCount c = some old ∧ cmp.holds old n
  | .bump b old => b.op = .add → s.count? L.initialCount b.counter = some old

private theorem Op.fire (op : Op) (s : Machine) (a : Agent) (h : op.Enabled s) :
    Fire L s (op.emit a) (op.mem s.mem) s.pending op.value := by
  cases op with
  | wait c cmp n md old =>
    cases c <;> exact .wait _ _ _ _ _ _ h.1 h.2
  | bump b old =>
    obtain ⟨c,op,n,md⟩ := b
    cases c <;> cases op <;> exact .bump _ _ _ h

private def Op.after (o : Op) (a : Agent) (s : Machine) : Machine :=
  ⟨o.mem s.mem, s.history ++ [.issued a (o.emit a)],s.pending⟩

private def fireAll (a : Agent) : Machine → List Op → Machine
  | s, [] => s
  | s, o :: os => fireAll a (o.after a s) os

private def CanFire (a : Agent) : Machine → List Op → Prop
  | _, [] => True
  | s, o :: os => (o.emit a).event.AccessibleBy L.symm a ∧ o.Enabled s ∧ CanFire a (o.after a s) os

private theorem fireAll_sound (a : Agent) (ops : List Op) (s : Machine)
    (can : CanFire a s ops) (quiet : Quiet s.history) (pend : s.pending = []) :
    FireGroup L a s (ops.map (Op.emit a)) (fireAll a s ops) (ops.map Op.value) := by
  induction ops generalizing s with
  | nil => exact .nil _
  | cons o os ih =>
    have actor : (o.emit a).actor = a := by cases o <;> rfl
    apply FireGroup.cons (by rw [actor]; exact can.1) (fun _ p _ _ => quiet_free quiet p)
      (by simp [PendingFence,pend]) (o.fire s a can.2.1)
    apply ih _ can.2.2 _ pend
    apply quiet_snoc quiet
    intro entry member t
    cases o <;> simp [Op.emit, Occurrence.event?] at member <;> subst entry <;> simp

private theorem fireAll_quiet (a : Agent) (ops : List Op) (s : Machine) (q : Quiet s.history) :
    Quiet (fireAll a s ops).history := by
  induction ops generalizing s with
  | nil => exact q
  | cons o os ih =>
    apply ih (o.after a s) (quiet_snoc q ?_)
    intro e h t
    cases o <;> simp [Op.emit,Occurrence.event?] at h <;> subst e <;> simp

private theorem fireAll_pending (a : Agent) (ops : List Op) (s : Machine) :
    (fireAll a s ops).pending = s.pending := by
  induction ops generalizing s with
  | nil => rfl
  | cons o os ih => exact ih (o.after a s)

private def pre (s : Config Nat) (a : Agent) (pc : Nat) : Machine :=
  let seg := (L.program a).segment pc
  ⟨s.mem,s.history ++ [.segment a (seg.reads s.mem) (seg.writes s.mem)],s.pending⟩

private def turn (s : Config Nat) (a : Agent) (pc : Nat) (ops : List Op) : Config Nat :=
  {fireAll a (pre s a pc) ops with pc := Function.update s.pc a (some (.ready (pc+1)))}

private def At (q : Config Nat) : Prop :=
  (∃ cs, Run L (L.initial origin) cs q) ∧ Quiet q.history ∧ q.pending = []

private theorem turn_reached (reach : At s) (a : Agent) (pc : Nat) (hd : Op) (tail : List Op)
    (cur : s.pc a = some (.ready pc)) (owner : ((L.program a).segment pc).agent = a)
    (run : ((L.program a).segment pc).run s.mem = some s.mem)
    (acc : ∀ p ∈ ((L.program a).segment pc).reads s.mem ∪ ((L.program a).segment pc).writes s.mem,
      AccessibleAt L.symm a p)
    (next : (L.program a).next pc s.mem = .emitGroup (hd.emit a) (tail.map (Op.emit a)) (fun _ => pc+1))
    (self : a.within a) (can : CanFire a (pre s a pc) (hd::tail)) :
    At (turn s a pc (hd::tail)) := by
  have st := step.segment (l := L) cur rfl owner
    (fun p hp => ⟨acc p hp, quiet_free reach.2.1 p⟩) run
  have qpre : Quiet (pre s a pc).history := quiet_snoc reach.2.1 (by simp [Occurrence.event?])
  have fires := fireAll_sound a (hd::tail) _ can qpre reach.2.2
  obtain ⟨cs,r⟩ := reach.1
  refine ⟨⟨_, VeriTile.Tests.FetchAddObservation.appendRuns (ys := [.agent a, .agent a]) r (.cons st (.cons ?_ (.nil _)))⟩,
    fireAll_quiet _ _ _ qpre,(fireAll_pending _ _ _).trans reach.2.2⟩
  let middle : Config Nat := {pre s a pc with pc := Function.update s.pc a ((L.program a).next pc s.mem).cursor}
  have hpc : middle.pc a = some (.waiting (hd.emit a) (tail.map (Op.emit a)) (fun _ => pc+1)) := by
    simp [middle,next,Next.cursor]
  have owners : ∀ x ∈ (hd::tail).map (Op.emit a), x.actor.within a := by
    intro x hx; obtain ⟨o,_,rfl⟩ := List.mem_map.mp hx; cases o <;> exact self
  have go := step.fire (l := L) hpc owners fires
  simpa only [middle,turn,Function.update_idem] using go

private abbrev addWord (stage : Bool) (old : Nat) :=
  Op.bump ⟨Stream.streamCounter 0 stage,.add,1,.atomic .gpu .release⟩ old
private abbrev waitWord (stage : Bool) (n : Nat) :=
  Op.wait (Stream.streamCounter 0 stage) .ge n (.atomic .gpu .acquire) n
private abbrev arrive (old : Nat) := Op.bump ⟨phase 0,.add,1,.atomic .cta .release⟩ old
private abbrev join := Op.wait (phase 0) .ge 2 (.atomic .cta .acquire) 2
private abbrev casGet (t : Nat) := Op.wait (.word (VeriTile.Tests.E2ReadsFromDetermined.flag t 0))
  .eq 0 (.atomic .sys .relaxed) 0
private abbrev casSet (t : Nat) := Op.bump ⟨.word (VeriTile.Tests.E2ReadsFromDetermined.flag t 0),
  .set,1,.atomic .sys .release⟩ 0

private structure Move where
  actor : Agent
  pc : Nat
  head : Op
  tail : List Op := []

/-- Rank zero's copy, both K11 lanes and the local tile. Both participants arrive
before either is allowed to leave the CTA phase. Rank one has not run yet. -/
private def move : Nat → Move
  | 0 => ⟨H 0,0,addWord false 0,[]⟩
  | 1 => ⟨A 0,0,waitWord false 1,[]⟩
  | 2 => ⟨A 1,0,waitWord false 1,[]⟩
  | 3 => ⟨A 0,1,casGet 0,[casSet 0]⟩
  | 4 => ⟨A 1,1,casGet 1,[casSet 1]⟩
  | 5 => ⟨A 0,2,arrive 0,[]⟩
  | 6 => ⟨A 1,2,arrive 1,[]⟩
  | 7 => ⟨A 0,3,join,[]⟩
  | 8 => ⟨A 1,3,join,[]⟩
  | 9 => ⟨A 0,4,addWord true 0,[]⟩
  | 10 => ⟨A 1,4,addWord true 1,[]⟩
  | _ => ⟨T,0,waitWord true 2,[]⟩

private def before : Nat → Config Nat
  | 0 => L.initial origin
  | i+1 =>
    let v := move i
    turn (before i) v.actor v.pc (v.head::v.tail)

private theorem copyAccess (r : Fin 2) (s : DistState) :
    ∀ p ∈ (hostCopySeg 1 1 r).reads s ∪ (hostCopySeg 1 1 r).writes s,
      AccessibleAt L.symm (H r) p := by
  intro p hp
  rcases hp with ⟨q,u,rfl⟩ | ⟨q,u,rfl⟩
  · exact ⟨trivial,.inl rfl⟩
  · exact ⟨trivial,.inr rfl⟩

private theorem emptyAccess (a : Agent) (s : DistState) :
    ∀ p ∈ (emptySeg a).reads s ∪ (emptySeg a).writes s, AccessibleAt L.symm a p := by
  intro _ h; exact False.elim (by rcases h with h|h <;> exact h)

private theorem wordAccessible (a : Agent) (p : Addr) (m : Mode) (cmp : Cmp) (n : Nat)
    (ok : AccessibleAt L.symm a p) : (Event.wait (.word p) cmp n m).AccessibleBy L.symm a := by
  intro k q md h; simp [Event.accesses] at h; simpa [h.2.1] using ok

private theorem bumpAccessible (a : Agent) (p : Addr) (op : SignalOp) (m : Mode) (n : Nat)
    (ok : AccessibleAt L.symm a p) : (Event.bump ⟨.word p,op,n,m⟩).AccessibleBy L.symm a := by
  intro k q md h; simp [Event.accesses,Bump.accesses] at h; simpa [h.2.1] using ok

private theorem phaseWaitAccessible (a : Agent) (m : Mode) (cmp : Cmp) (n : Nat) :
    (Event.wait (phase 0) cmp n m).AccessibleBy L.symm a := by
  intro _ _ _ h; simp [Event.accesses,phase] at h

private theorem phaseAddAccessible (a : Agent) (m : Mode) (n : Nat) :
    (Event.bump ⟨phase 0,.add,n,m⟩).AccessibleBy L.symm a := by
  intro _ _ _ h; simp [Event.accesses,Bump.accesses,phase] at h

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
private theorem actual_turn (i : Nat) (lt : i < 12) (prev : At (before i)) : At (before (i+1)) := by
  apply turn_reached prev (move i).actor (move i).pc (move i).head (move i).tail
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> first | exact hostZero | rfl
  · interval_cases i <;> first | exact copyAccess (0 : Fin 2) origin | exact emptyAccess _ _
  · interval_cases i <;> rfl
  · interval_cases i <;> decide
  · interval_cases i <;> simp only [move, CanFire, Op.Enabled, Op.emit, and_true]
    all_goals repeat' first
      | apply And.intro
      | exact wordAccessible _ _ _ _ _ (by decide)
      | exact bumpAccessible _ _ _ _ _ (by decide)
      | exact phaseWaitAccessible _ _ _ _
      | exact phaseAddAccessible _ _ _
      | rfl
      | decide
      | intro h
    all_goals exact Nat.le_refl _

private theorem reached12 : At (before 12) := by
  have each (n : Nat) (hn : n ≤ 12) : At (before n) := by
    induction n with
    | zero => exact ⟨⟨[],.nil _⟩,by simp [before,Launch.initial, Quiet]⟩
    | succ n ih => exact actual_turn n hn (ih (by omega))
  exact each 12 le_rfl

private def noPeer (h : History) := ∀ x ∈ h, x.program? ≠ some (H 1)
private theorem noPeer_snoc {h : History} {x : Occurrence} (old : noPeer h)
    (one : x.program? ≠ some (H 1)) : noPeer (h ++ [x]) := by
  intro y mem; rcases List.mem_append.mp mem with past|last
  · exact old _ past
  · rwa [List.mem_singleton.mp last]

private theorem fireAll_noPeer (a : Agent) (ha : a ≠ H 1) (s : Machine) (ops : List Op)
    (old : noPeer s.history) : noPeer (fireAll a s ops).history := by
  induction ops generalizing s with
  | nil => exact old
  | cons o os ih =>
    exact ih (o.after a s) (noPeer_snoc old (by simpa [Occurrence.program?] using ha))

private theorem before_noPeer (i : Nat) : noPeer (before i).history := by
  induction i with
  | zero => simp [noPeer,before,Launch.initial]
  | succ i ih =>
    have away : (move i).actor ≠ H 1 := by unfold move; split <;> decide
    exact fireAll_noPeer _ away (pre _ _ _) _ (noPeer_snoc ih (by simpa [Occurrence.program?] using away))

private def segEnd (s : Config Nat) (a : Agent) (pc : Nat) (f : DistState) : Config Nat :=
  let sg := (L.program a).segment pc
  {s with
    mem := f
    history := s.history ++ [.segment a (sg.reads s.mem) (sg.writes s.mem)]
    pc := Function.update s.pc a ((L.program a).next pc s.mem).cursor}

private theorem seg_reached (before : At s) (a : Agent) (pc : Nat) (f : DistState)
    (cur : s.pc a = some (.ready pc)) (own : ((L.program a).segment pc).agent = a)
    (run : ((L.program a).segment pc).run s.mem = some f)
    (acc : ∀ p ∈ ((L.program a).segment pc).reads s.mem ∪ ((L.program a).segment pc).writes s.mem,
      AccessibleAt L.symm a p) : At (segEnd s a pc f) := by
  obtain ⟨⟨cs,r⟩,quiet,pend⟩ := before
  refine ⟨⟨_,FetchAddObservation.appendRuns r (.cons (step.segment cur rfl own
    (fun p hp => ⟨acc p hp,quiet_free quiet p⟩) run) (.nil _))⟩,?_,pend⟩
  apply quiet_snoc quiet
  simp [Occurrence.event?]

private theorem tileAccess (s : DistState) : ∀ p ∈ (encodedTileSeg 1 1 (0 : Fin 2) 0).reads s ∪
    (encodedTileSeg 1 1 (0 : Fin 2) 0).writes s, AccessibleAt L.symm T p := by
  intro p hp
  rcases hp with ⟨u,src,_,rfl⟩ | ⟨u,_,rfl⟩ <;> exact ⟨trivial,.inl rfl⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
/-- The two rank-zero K11 lanes can leave the CTA round after issuing their releases.
They never wait for rank one's release. Rank zero reads the unfilled peer slot,
then rank one's first segment writes it, with no happens-before edge. -/
theorem reachable_race : ∃ (x : RankTensor 2 (Fin (2*1) × Fin 1)) (s : DistState)
    (cs : Schedule) (f : Config Nat), Initial x s ∧
    Run (launch false 2 2 1 1 putCellWrites) ((launch false 2 2 1 1 putCellWrites).initial s) cs f ∧
    DataRace (launch false 2 2 1 1 putCellWrites) f.history := by
  have zeros : ∀ (u : Coordinate 1 1) (src : Fin 2), tileIndex u = 0 →
      ((before 12).mem.cell (scatterSlot (0 : Fin 2) src u.1 u.2)).readAs .real =
      some ((0 : ℝ) : WithBot ℝ) := by
    intro u src _
    obtain rfl : u = coord := Subsingleton.elim _ _
    fin_cases src <;> rfl
  obtain ⟨result,tile,_,_⟩ := encodedTile_run (fun (_ : Fin 2) (_ : Fin (2*1) × Fin 1) => (0 : ℝ))
    (0 : Fin 2) 0 (before 12).mem zeros
  let mid := segEnd (before 12) T 1 result
  have ready : At mid := seg_reached reached12 T 1 _ rfl rfl tile (tileAccess _)
  obtain ⟨copied,actual⟩ := hostCopy_runs 1 1 (1 : Fin 2) mid.mem
  let f := segEnd mid (H 1) 0 copied
  have reached : At f := seg_reached ready (H 1) 0 _ rfl rfl actual (copyAccess _ _)
  obtain ⟨cs,run⟩ := reached.1
  refine ⟨data,origin,cs,f,permitted,run,?_⟩
  let read : Occurrence := .segment T (@readsOf 2 1 1 0 0) (@writesOf 2 1 1 0 0)
  let write : Occurrence := .segment (H 1) (copyReads 1 1 (1 : Fin 2)) (copyWrites 1 1 (1 : Fin 2))
  have hist : f.history = (before 12).history ++ [read,write] := by
    change ((before 12).history ++ [read]) ++ [write] = _
    simp [List.append_assoc]
  let i := (before 12).history.length
  have atRead : f.history[i]? = some read := by rw [hist]; simp [i]
  have atWrite : f.history[i+1]? = some write := by rw [hist]; simp [i]
  let p := scatterSlot (0 : Fin 2) (1 : Fin 2) coord.1 coord.2
  refine ⟨i,i+1,read,write,p,.load,.store,.plain,.plain,by omega,atRead,atWrite,
    ⟨coord,1,rfl,rfl⟩,⟨0,coord,rfl⟩,Or.inr rfl,by simp [Mode.AtomicFor],?_⟩
  apply Stream.firstTileNoHB atWrite
  intro k bound occ hit
  by_cases old : k < i
  · rw [hist,List.getElem?_append_left old] at hit
    exact before_noPeer 12 _ (List.mem_iff_getElem?.mpr ⟨k,hit⟩)
  · have eq : k = i := by omega
    rw [eq,atRead] at hit
    cases hit
    decide

#print axioms reachable_race

end
end VeriTile.Tests.T05Pilot.Whole.NoAcquire
