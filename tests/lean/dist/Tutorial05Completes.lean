import tests.lean.dist.Tutorial05Whole
import tests.lean.dist.Tutorial05Registers

/-! A serial schedule for the complete tutorial launch. Segment and event-group
choices are kept separate, exactly as in the distributed machine. -/
namespace VeriTile.Tests.T05Pilot.Whole
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
open VeriTile.Triton (MemCell)
noncomputable section

namespace ScheduleProof

variable {n lanes rows cols : Nat} {w : CellWrites}

theorem role_inj : Function.Injective (@Role.owner n lanes rows cols) := by
  intro a b eq
  have h := congrArg (decode n lanes rows cols) eq
  simpa using h

private theorem segmentOwner (r : Role n lanes rows cols) (i : Nat) :
    (r.segment i).agent = r.owner := by
  cases r with
  | copy r => cases i <;> rfl
  | lane r t => rfl
  | tile r b => cases i with
    | zero => rfl
    | succ i => cases i <;> rfl

private theorem segmentAccessible (r : Role n lanes rows cols) (i : Nat) (s : DistState)
    {p} (mem : p ∈ (r.segment i).reads s ∪ (r.segment i).writes s) :
    AccessibleAt symmetric r.owner p := by
  cases r with
  | copy r =>
    cases i with
    | succ i => simp [Role.segment,emptySeg] at mem
    | zero =>
      change p ∈ copyReads rows cols r ∪ copyWrites rows cols r at mem
      rcases mem with ⟨peer,u,rfl⟩ | ⟨peer,u,rfl⟩
      · exact ⟨trivial,.inl rfl⟩
      · exact ⟨trivial,.inr rfl⟩
  | lane r t => simp [Role.segment,emptySeg] at mem
  | tile r b =>
    cases i with
    | zero => simp [Role.segment,emptySeg] at mem
    | succ i =>
      cases i with
      | succ i => simp [Role.segment,emptySeg] at mem
      | zero =>
        change p ∈ @readsOf n rows cols r b ∪ @writesOf n rows cols r b at mem
        rcases mem with ⟨u,src,_,rfl⟩ | ⟨u,_,rfl⟩ <;> exact ⟨trivial,.inl rfl⟩

def opened (s : Config Nat) (r : Role n lanes rows cols) (i : Nat) (mem : DistState) : Config Nat :=
  {s with mem := mem,
          history := s.history ++ [.segment r.owner ((r.segment i).reads s.mem) ((r.segment i).writes s.mem)],
          pc := Function.update s.pc r.owner (lineNext (r.groups true) i).cursor}

theorem openRole (s : Config Nat) (r : Role n lanes rows cols) (i : Nat) (mem : DistState)
    (ready : s.pc r.owner = some (.ready i)) (quiet : Quiet s.history)
    (execute : (r.segment i).run s.mem = some mem) :
    step (launch true n lanes rows cols w) s (.agent r.owner) (opened s r i mem) := by
  have code : (r.segment i) = ((launch true n lanes rows cols w).program r.owner).segment i := by
    simp [launch,agentProgram]
  have mv := @step.segment _ (launch true n lanes rows cols w) s r.owner i _ mem ready code
    (segmentOwner r i) (fun p hp => ⟨segmentAccessible r i _ hp,quiet_free quiet p⟩) execute
  simpa only [launch,agentProgram,decode_owner,opened] using mv

private theorem groupAccessible (a : Agent) (e : Emission)
    (access : e.event.AccessibleBy symmetric e.actor) (quiet : Quiet m.history)
    (pend : m.pending = []) (fire : Fire (launch true n lanes rows cols w) m e mem m.pending v) :
    FireGroup (launch true n lanes rows cols w) a m [e] ⟨mem,m.history ++ [.issued a e],m.pending⟩ [v] :=
  .cons access (fun _ p _ _ => quiet_free quiet p) (by simp [PendingFence,pend]) fire (.nil _)

def advanced (s : Config Nat) (r : Role n lanes rows cols) (i : Nat) (mid final : DistState)
    (g : Group) : Config Nat :=
  {(opened s r i mid) with
    mem := final
    history := (opened s r i mid).history ++ (g.1 :: g.2).map (.issued r.owner)
    pc := Function.update s.pc r.owner (some (.ready (i+1)))}

theorem tick (s : Config Nat) (r : Role n lanes rows cols) (i : Nat) (mid final : DistState)
    (g : Group) (ready : s.pc r.owner = some (.ready i)) (quiet : Quiet s.history)
    (execute : (r.segment i).run s.mem = some mid) (atGroup : (r.groups true)[i]? = some g)
    (owned : ∀ x ∈ g.1 :: g.2, x.actor.within r.owner)
    (fire : FireGroup (launch true n lanes rows cols w) r.owner (opened s r i mid).toMachine
      (g.1::g.2) ⟨final,(opened s r i mid).history ++ (g.1::g.2).map (Occurrence.issued r.owner),s.pending⟩ values) :
    Run (launch true n lanes rows cols w) s [.agent r.owner,.agent r.owner] (advanced s r i mid final g) := by
  apply Run.cons (openRole s r i mid ready quiet execute)
  have waiting : (opened s r i mid).pc r.owner = some (.waiting g.1 g.2 (fun _ => i+1)) := by
    simp [opened,lineNext,atGroup,Next.cursor]
  have st := @step.fire _ (launch true n lanes rows cols w) (opened s r i mid) r.owner _ _ _
    _ _ waiting owned fire
  apply Run.cons _ (Run.nil _)
  simpa [advanced,opened,Function.update_idem] using st

theorem finishRole (s : Config Nat) (r : Role n lanes rows cols) (i : Nat) (mem : DistState)
    (ready : s.pc r.owner = some (.ready i)) (quiet : Quiet s.history)
    (execute : (r.segment i).run s.mem = some mem) (done : (r.groups true)[i]? = none) :
    Run (launch true n lanes rows cols w) s [.agent r.owner]
      {(opened s r i mem) with pc := Function.update s.pc r.owner none} := by
  have mv := openRole (w := w) s r i mem ready quiet execute
  exact .cons (by simpa [opened,lineNext,done,Next.cursor] using mv) (.nil _)

/-- A series of choices of one program changes only its cursor. The event
projection exposes just the events that can change a collective count. -/
structure Moves (l : Launch Nat) (s d : Config Nat) (a : Agent) (pc : Option Nat)
    (mem : DistState) (events : Trace) : Prop where
  ran : ∃ cs, Run l s cs d
  pcs : d.pc = Function.update s.pc a (pc.map Cursor.ready)
  memory : d.mem = mem
  pending : d.pending = s.pending
  trace : d.trace = s.trace ++ events

theorem Moves.thenSame (h : Moves l s m a k mem events) (t : Moves l m d a k' mem' more) :
    Moves l s d a k' mem' (events ++ more) := by
  obtain ⟨c,rc⟩ := h.ran; obtain ⟨e,re⟩ := t.ran
  exact ⟨⟨_,appendRuns' rc re⟩,by rw [t.pcs,h.pcs,Function.update_idem],t.memory,
    t.pending.trans h.pending,by rw [t.trace,h.trace,List.append_assoc]⟩

theorem Moves.ready (h : Moves l s m a (some k) mem events) : m.pc a = some (.ready k) := by
  simp [h.pcs]

theorem Moves.quiet (h : Moves l s m a k mem events) (q : Quiet s.history)
    (noTransfer : ∀ e ∈ events, ∀ t, e.2 ≠ .initiate t) : Quiet m.history := by
  change ∀ e ∈ m.trace, ∀ t, _
  rw [h.trace]; rintro e he; rcases List.mem_append.mp he with old | new
  · exact q e old
  · exact noTransfer e new

private theorem eventProjection {a : Agent} (xs : List Emission) :
    (xs.map (.issued a)).filterMap Occurrence.event? = xs.map (fun e => (e.actor,e.event)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Occurrence.event?]

/-- Turn the actual segment and nonempty fire group into a composable move. -/
theorem runGroup (s : Config Nat) (r : Role n lanes rows cols) (i : Nat) (mid final : DistState)
    (g : Group) (ready : s.pc r.owner = some (.ready i)) (quiet : Quiet s.history)
    (execute : (r.segment i).run s.mem = some mid) (atGroup : (r.groups true)[i]? = some g)
    (owned : ∀ x ∈ g.1 :: g.2, x.actor.within r.owner)
    (fire : FireGroup (launch true n lanes rows cols w) r.owner (opened s r i mid).toMachine
      (g.1::g.2) ⟨final,(opened s r i mid).history ++ (g.1::g.2).map (Occurrence.issued r.owner),s.pending⟩ values) :
    ∃ d, Moves (launch true n lanes rows cols w) s d r.owner (some (i+1)) final
        ((g.1::g.2).map (fun e => (e.actor,e.event))) := by
  refine ⟨_,⟨_,tick s r i mid final g ready quiet execute atGroup owned fire⟩,rfl,rfl,rfl,?_⟩
  change (((s.history ++ [_]) ++ (g.1::g.2).map (Occurrence.issued r.owner)).filterMap Occurrence.event?) = _
  rw [List.filterMap_append,eventProjection,List.filterMap_append]
  simp [Machine.trace,Occurrence.event?]

theorem runFinish (s : Config Nat) (r : Role n lanes rows cols) (i : Nat) (mem : DistState)
    (ready : s.pc r.owner = some (.ready i)) (quiet : Quiet s.history)
    (execute : (r.segment i).run s.mem = some mem) (done : (r.groups true)[i]? = none) :
    ∃ d, Moves (launch true n lanes rows cols w) s d r.owner none mem [] := by
  refine ⟨_,⟨_,finishRole s r i mem ready quiet execute done⟩,rfl,rfl,rfl,?_⟩
  simp [opened,Machine.trace,Occurrence.event?]

private theorem own (r : Role n lanes rows cols) : r.owner.within r.owner := by
  cases r <;> simp [Role.owner,Stream.host,Stream.lane,Stream.tile,Agent.within,Agent.cta?]

private theorem openQuiet {s : Config Nat} {r : Role n lanes rows cols} (q : Quiet s.history) :
    Quiet (opened s r i mid).history := quiet_snoc q (by simp [Occurrence.event?])

/-- A single operational wait after the indicated segment. For phase waits the
observed value comes from the signed trace fold; word waits read physical RAM. -/
theorem waitTurn (s : Config Nat) (r : Role n lanes rows cols) (i : Nat) (mid : DistState)
    (counter : Counter) (scope : Scope) (threshold old : Nat)
    (ready : s.pc r.owner = some (.ready i)) (q : Quiet s.history) (clear : s.pending = [])
    (execute : (r.segment i).run s.mem = some mid)
    (atGroup : (r.groups true)[i]? = some (take r.owner counter scope threshold,[]))
    (access : (take r.owner counter scope threshold).event.AccessibleBy symmetric r.owner)
    (value : (opened s r i mid).count? (launch true n lanes rows cols w).initialCount counter = some old)
    (enabled : threshold ≤ old) :
    ∃ d, Moves (launch true n lanes rows cols w) s d r.owner (some (i+1)) mid
      [(r.owner,(take r.owner counter scope threshold).event)] := by
  apply runGroup s r i mid mid (take r.owner counter scope threshold,[]) ready q execute atGroup
  · intro e he; simp at he; subst e; exact own r
  · exact groupAccessible _ _ access (openQuiet q) clear (.wait _ _ _ _ _ old value enabled)

theorem giveWordTurn (s : Config Nat) (r : Role n lanes rows cols) (i : Nat) (mid : DistState)
    (p : Addr) (scope : Scope) (old : Nat)
    (ready : s.pc r.owner = some (.ready i)) (q : Quiet s.history) (clear : s.pending = [])
    (execute : (r.segment i).run s.mem = some mid)
    (atGroup : (r.groups true)[i]? = some (give r.owner (.word p) scope,[]))
    (access : (give r.owner (.word p) scope).event.AccessibleBy symmetric r.owner)
    (value : (mid.cell p).readAs .nat = some old) :
    ∃ d, Moves (launch true n lanes rows cols w) s d r.owner (some (i+1))
      (w.put mid p (.of .nat (old+1))) [(r.owner,(give r.owner (.word p) scope).event)] := by
  apply runGroup s r i mid _ (give r.owner (.word p) scope,[]) ready q execute atGroup
  · intro e he; simp at he; subst e; exact own r
  · exact groupAccessible _ _ access (openQuiet q) clear (.bump _ _ old (fun _ => value))

theorem phaseTurn (s : Config Nat) (r : Role n lanes rows cols) (i : Nat) (rank : Nat)
    (ready : s.pc r.owner = some (.ready i)) (q : Quiet s.history) (clear : s.pending = [])
    (execute : (r.segment i).run s.mem = some s.mem)
    (atGroup : (r.groups true)[i]? = some (give r.owner (phase rank) .cta,[])) :
    ∃ d, Moves (launch true n lanes rows cols w) s d r.owner (some (i+1)) s.mem
      [(r.owner,(give r.owner (phase rank) .cta).event)] := by
  apply runGroup s r i _ _ (give r.owner (phase rank) .cta,[]) ready q execute atGroup
  · intro e he; simp at he; subst e; exact own r
  · apply groupAccessible _ _ (by simp [give,phase,Event.AccessibleBy,Event.accesses,Bump.accesses])
      (openQuiet q) clear
    exact .bump _ _ _ (fun _ => rfl)

private def casGroup (a : Agent) (p : Addr) (old new : Nat) (reader writer : Mode) : Group :=
  (⟨a,.wait (.word p) .eq old reader,.noValue⟩,[⟨a,.bump ⟨.word p,.set,new,writer⟩,.noValue⟩])

theorem casTurn (s : Config Nat) (r : Role n lanes rows cols) (i : Nat)
    (p : Addr) (old new : Nat) (reader writer : Mode)
    (ready : s.pc r.owner = some (.ready i)) (q : Quiet s.history) (clear : s.pending = [])
    (execute : (r.segment i).run s.mem = some s.mem)
    (atGroup : (r.groups true)[i]? = some (casGroup r.owner p old new reader writer))
    (access : AccessibleAt symmetric r.owner p) (value : (s.mem.cell p).readAs .nat = some old) :
    ∃ d, Moves (launch true n lanes rows cols w) s d r.owner (some (i+1))
      (w.put s.mem p (.of .nat new)) [(r.owner,.wait (.word p) .eq old reader),
        (r.owner,.bump ⟨.word p,.set,new,writer⟩)] := by
  let g := casGroup r.owner p old new reader writer
  apply runGroup (values := [some (.of .nat old),none]) s r i _ _ g ready q execute atGroup
  · intro e he; simp [g,casGroup] at he; rcases he with rfl | rfl <;> exact own r
  · let m := opened s r i s.mem
    have pre : Quiet m.history := openQuiet q
    have afterWait : Quiet (m.history ++ [.issued r.owner g.1]) :=
      quiet_snoc pre (by simp [g,casGroup,Occurrence.event?])
    refine .cons ?_ (fun _ p _ _ => quiet_free pre p) (by simp [PendingFence,opened,clear])
      (.wait _ _ _ _ _ old value rfl) (.cons ?_ (fun _ p _ _ => quiet_free afterWait p)
      (by simp [PendingFence,opened,clear]) (.bump _ _ 0 (by intro h; cases h)) ?_)
    · intro kd a mode h; have := (show kd = .load ∧ a = p ∧ mode = reader by
        simpa [g,casGroup,Event.accesses] using h); exact this.2.1 ▸ access
    · intro kd a mode h; have := (show kd = .store ∧ a = p ∧ mode = writer by
        simpa [g,casGroup,Event.accesses,Bump.accesses] using h); exact this.2.1 ▸ access
    · simpa [List.append_assoc] using (FireGroup.nil
        (l := launch true n lanes rows cols w)
        (program := r.owner) (⟨w.put s.mem p (.of .nat new),m.history ++ [_,_],s.pending⟩ : Machine))

private def eventLog (r : Role n lanes rows cols) (i len : Nat) : Trace :=
  (((r.groups true).drop i).take len).flatMap fun g => (g.1 :: g.2).map (fun e => (e.actor,e.event))

private theorem localGive (a : Agent) (rank : Nat) (stage : Bool) (same : a.rankOf = rank) :
    (give a (Stream.streamCounter rank stage) .gpu).event.AccessibleBy symmetric a := by
  rintro kd p m h
  obtain ⟨rfl,rfl,rfl⟩ := (show kd = .update ∧ p = Stream.mark rank stage ∧ m = .atomic .gpu .release by
    simpa [give,Stream.streamCounter,Event.accesses,Bump.accesses] using h)
  exact ⟨trivial,.inl same.symm⟩

private theorem localWait (a : Agent) (rank : Nat) (stage : Bool) (k) (same : a.rankOf = rank) :
    (take a (Stream.streamCounter rank stage) .gpu k).event.AccessibleBy symmetric a := by
  rintro kd p m h
  obtain ⟨rfl,rfl,rfl⟩ := (show kd = .load ∧ p = Stream.mark rank stage ∧ m = .atomic .gpu .acquire by
    simpa [take,Stream.streamCounter,Event.accesses] using h)
  exact ⟨trivial,.inl same.symm⟩

private theorem flagAccess (a : Agent) (r t : Nat) : AccessibleAt symmetric a (flag r t) :=
  ⟨trivial,.inr rfl⟩

private def sendPC (n t : Nat) : Nat := if t < n then 2 else 1
private def joinPC (n t : Nat) : Nat := if t < n then 4 else 2

private theorem copyMoves (s : Config Nat) (r : Fin n)
    (ready : s.pc (Stream.host r) = some (.ready 0)) (q : Quiet s.history) (clear : s.pending = [])
    (zero : (s.mem.cell (Stream.mark r false)).readAs .nat = some 0) :
    ∃ mid d, (hostCopySeg rows cols r).run s.mem = some mid ∧
      Moves (launch true n lanes rows cols w) s d (Stream.host r) none
        (w.put mid (Stream.mark r false) (.of .nat 1)) (eventLog (.copy r : Role n lanes rows cols) 0 1) := by
  let worker : Role n lanes rows cols := .copy r
  obtain ⟨mid,exec⟩ := hostCopy_runs rows cols r s.mem
  have atMark : mid.cell (Stream.mark r false) = s.mem.cell (Stream.mark r false) :=
    hostCopy_frame r exec (by rintro ⟨peer,u,h⟩; exact (by decide : ("T05.stream.shadow" : VeriTile.Triton.RegionName) ≠ "scatter") (congrArg Addr.region h))
  obtain ⟨m,moved⟩ := giveWordTurn (w := w) s worker 0 mid (Stream.mark r false) .gpu 0 ready q clear exec
    rfl (localGive _ _ _ rfl) (by rw [atMark]; exact zero)
  obtain ⟨d,ended⟩ := runFinish (w := w) m worker 1 m.mem moved.ready
    (moved.quiet q (by simp [give])) rfl rfl
  exact ⟨mid,d,exec,by simpa [moved.memory] using moved.thenSame ended⟩

private theorem sendMoves (s : Config Nat) (r : Fin n) (t : Fin lanes)
    (ready : s.pc (Stream.lane r t) = some (.ready 0)) (q : Quiet s.history) (clear : s.pending = [])
    (host : (s.mem.cell (Stream.mark r false)).readAs .nat = some 1)
    (zero : t.val < n → (s.mem.cell (flag t r)).readAs .nat = some 0) :
    ∃ d, Moves (launch true n lanes rows cols w) s d (Stream.lane r t) (some (sendPC n t))
      (if t.val < n then w.put s.mem (flag t r) (.of .nat 1) else s.mem)
      (eventLog (.lane r t : Role n lanes rows cols) 0 (sendPC n t)) := by
  let worker : Role n lanes rows cols := .lane r t
  obtain ⟨m,moved⟩ := waitTurn (w := w) s worker 0 s.mem (Stream.streamCounter r false) .gpu 1 1
    ready q clear rfl (by simp [worker,Role.groups,Role.owner]) (localWait _ _ _ _ rfl) host (by decide)
  by_cases active : t.val < n
  · obtain ⟨d,cas⟩ := casTurn (w := w) m worker 1 (flag t r) 0 1 (sysM .relaxed) (sysM .release)
      moved.ready (moved.quiet q (by simp [take])) (moved.pending.trans clear) rfl
      (by simp [worker,Role.groups,active,casGroup,w0,s1,Role.owner,Stream.lane,thr])
      (flagAccess _ _ _) (by rw [moved.memory]; exact zero active)
    exact ⟨d,by simpa [sendPC,active,eventLog,worker,Role.groups,moved.memory] using moved.thenSame cas⟩
  · exact ⟨m,by simpa [sendPC,active,worker,eventLog,Role.groups] using moved⟩

private theorem arriveMoves (s : Config Nat) (r : Fin n) (t : Fin lanes)
    (ready : s.pc (Stream.lane r t) = some (.ready (sendPC n t))) (q : Quiet s.history) (clear : s.pending = [])
    (one : t.val < n → (s.mem.cell (flag r t)).readAs .nat = some 1) :
    ∃ d, Moves (launch true n lanes rows cols w) s d (Stream.lane r t) (some (joinPC n t))
      (if t.val < n then w.put s.mem (flag r t) (.of .nat 0) else s.mem)
      (eventLog (.lane r t : Role n lanes rows cols) (sendPC n t) (joinPC n t - sendPC n t)) := by
  let worker : Role n lanes rows cols := .lane r t
  by_cases active : t.val < n
  · obtain ⟨m,moved⟩ := casTurn (w := w) s worker 2 (flag r t) 1 0 (sysM .acquire) (sysM .relaxed)
      (by simpa [worker,sendPC,active] using ready) q clear rfl
      (by simp [worker,Role.groups,active,casGroup,w1,s0,Role.owner,Stream.lane,thr])
      (flagAccess _ _ _) (one active)
    obtain ⟨d,arrival⟩ := phaseTurn (w := w) m worker 3 r moved.ready
      (moved.quiet q (by simp)) (moved.pending.trans clear) rfl
      (by simp [worker,Role.groups,active,Role.owner])
    exact ⟨d,by simpa [eventLog,sendPC,joinPC,worker,Role.groups,active,moved.memory] using moved.thenSame arrival⟩
  · obtain ⟨d,arrival⟩ := phaseTurn (w := w) s worker 1 r
      (by simpa [worker,sendPC,active] using ready) q clear rfl (by simp [worker,Role.groups,active,Role.owner])
    exact ⟨d,by simpa [eventLog,sendPC,joinPC,worker,Role.groups,active] using arrival⟩

private theorem openedPhase (s : Config Nat) (r : Role n lanes rows cols) (i : Nat)
    (mem : DistState) (rank : Nat) (init : Counter → Nat) :
    (opened s r i mem).count? init (phase rank) = s.count? init (phase rank) := by
  simp [opened,Machine.count?,Machine.trace,phase,Occurrence.event?]

private theorem joinMoves (s : Config Nat) (r : Fin n) (t : Fin lanes) (old : Nat)
    (ready : s.pc (Stream.lane r t) = some (.ready (joinPC n t))) (q : Quiet s.history) (clear : s.pending = [])
    (phaseFull : s.count? (launch true n lanes rows cols w).initialCount (phase r) = some lanes)
    (ghost : (s.mem.cell (Stream.mark r true)).readAs .nat = some old) :
    ∃ d, Moves (launch true n lanes rows cols w) s d (Stream.lane r t) none
      (w.put s.mem (Stream.mark r true) (.of .nat (old+1)))
      (eventLog (.lane r t : Role n lanes rows cols) (joinPC n t) 2) := by
  let worker : Role n lanes rows cols := .lane r t
  let pc := joinPC n t
  have code : (worker.groups true)[pc]? = some (take worker.owner (phase r) .cta lanes,[]) := by
    by_cases h : t.val < n <;> simp [worker,pc,joinPC,h,Role.groups,Role.owner]
  obtain ⟨m,wait⟩ := waitTurn (w := w) s worker pc s.mem (phase r) .cta lanes lanes ready q clear rfl code
    (by simp [take,phase,Event.AccessibleBy,Event.accesses]) ((openedPhase ..).trans phaseFull) le_rfl
  have code' : (worker.groups true)[pc+1]? = some (give worker.owner (Stream.streamCounter r true) .gpu,[]) := by
    by_cases h : t.val < n <;> simp [worker,pc,joinPC,h,Role.groups,Role.owner]
  obtain ⟨u,posted⟩ := giveWordTurn (w := w) m worker (pc+1) m.mem (Stream.mark r true) .gpu old wait.ready
    (wait.quiet q (by simp [take])) (wait.pending.trans clear) rfl code' (localGive _ _ true rfl)
    (by rw [wait.memory]; exact ghost)
  have both := wait.thenSame posted
  obtain ⟨d,done⟩ := runFinish (w := w) u worker (pc+1+1) u.mem posted.ready
    (both.quiet q (by simp [give,take])) rfl (by
      by_cases h : t.val < n <;> simp [worker,pc,joinPC,h,Role.groups])
  refine ⟨d,?_⟩
  by_cases h : t.val < n <;> simpa [worker,pc,joinPC,h,eventLog,Role.groups,Role.owner,posted.memory,wait.memory]
    using both.thenSame done

private theorem tileMoves (x : RankTensor n (Fin (n*rows) × Fin cols)) (s : Config Nat)
    (r : Fin n) (b : Fin (tiles rows cols))
    (ready : s.pc (Stream.tile r b) = some (.ready 0)) (q : Quiet s.history) (clear : s.pending = [])
    (joined : (s.mem.cell (Stream.mark r true)).readAs .nat = some lanes) (placed : Placed x s.mem) :
    ∃ mem d, (encodedTileSeg rows cols r b).run s.mem = some mem ∧
      Moves (launch true n lanes rows cols w) s d (Stream.tile r b) none mem
        (eventLog (.tile r b : Role n lanes rows cols) 0 1) := by
  let worker : Role n lanes rows cols := .tile r b
  obtain ⟨m,wait⟩ := waitTurn (w := w) s worker 0 s.mem (Stream.streamCounter r true) .gpu lanes lanes
    ready q clear rfl rfl (localWait _ _ _ _ rfl) joined le_rfl
  obtain ⟨mem,compute,_⟩ := encodedTile_run x r b s.mem (fun u src _ => placed r u src)
  obtain ⟨d,done⟩ := runFinish (w := w) m worker 1 mem wait.ready (wait.quiet q (by simp [take]))
    (by change (encodedTileSeg rows cols r b).run m.mem = _; rwa [wait.memory]) rfl
  exact ⟨mem,d,compute,by simpa using wait.thenSame done⟩

def counterOf : Register n → Counter
  | .flag r t => .word (flag r t)
  | .pre r => Stream.streamCounter r false
  | .post r => Stream.streamCounter r true
  | .phase r => phase r

private theorem counter_inj : Function.Injective (@counterOf n) := by
  intro a b h
  cases a <;> cases b <;> simp [counterOf,flag,Stream.streamCounter,Stream.mark,phase,Fin.ext_iff] at h ⊢
  all_goals assumption

private theorem controlWord {reg : Register n} (eq : counterOf reg = .word p) : Control p := by
  cases reg <;> cases eq <;> simp [Control,flag,Stream.mark]

private def observe (w : CellWrites) (mem : DistState) (tr : Trace) (reg : Register n)
    (lanes rows cols : Nat) : Option Nat :=
  match counterOf reg with
  | .word p => (mem.cell p).readAs .nat
  | c => some (Counter.value (launch true n lanes rows cols w).initialCount tr c)

private abbrev Matches (w : CellWrites) (lanes rows cols : Nat) (mem : DistState) (tr : Trace)
    (values : Register n → Nat) :=
  ∀ reg, observe w mem tr reg lanes rows cols = some (values reg)

private theorem matchesFrame (h : Matches w lanes rows cols mem tr vals) (same : ∀ p, Control p → mem'.cell p = mem.cell p) :
    Matches w lanes rows cols mem' tr vals := by
  intro reg
  specialize h reg
  cases e : counterOf reg <;> simp only [observe,e] at h ⊢ <;> first
    | exact h
    | rwa [same _ (controlWord e)]

private theorem matchesPut (h : Matches w lanes rows cols mem tr vals)
    (key : Register n) (atWord : counterOf key = .word p) (v : Nat) :
    Matches w lanes rows cols (w.put mem p (.of .nat v)) tr (Function.update vals key v) := by
  intro reg
  by_cases eq : reg = key
  · subst reg; simp only [observe,atWord,w.read_same,Function.update_self]; rfl
  · rw [Function.update_of_ne eq]
    specialize h reg
    cases e : counterOf reg with
    | word addr =>
      have ne : addr ≠ p := fun h => eq (counter_inj (e.trans (h ▸ atWord.symm)))
      simpa only [observe,e,w.read_other _ _ _ _ ne] using h
    | phase | rendezvous | delivered => simpa only [observe,e] using h

private theorem matchesTrace {vals : Register n → Nat} (h : Matches w lanes rows cols mem tr vals)
    (same : ∀ r : Fin n, Counter.value (launch true n lanes rows cols w).initialCount (tr ++ ev) (phase r) =
      Counter.value (launch true n lanes rows cols w).initialCount tr (phase r)) :
    Matches w lanes rows cols mem (tr ++ ev) vals := by
  intro reg
  specialize h reg
  cases reg with
  | flag | pre | post => exact h
  | phase r => simpa only [observe,counterOf,phase] using (congrArg some (same r)).trans h

private theorem matchesArrival (h : Matches w lanes rows cols mem tr vals)
    (r : Fin n)
    (eq : ∀ v : Fin n, Counter.value (launch true n lanes rows cols w).initialCount (tr ++ ev) (phase v) =
      Counter.value (launch true n lanes rows cols w).initialCount tr (phase v) + (if v = r then 1 else 0)) :
    Matches w lanes rows cols mem (tr ++ ev) (Function.update vals (.phase r) (vals (.phase r) + 1)) := by
  intro reg
  specialize h reg
  cases reg with
  | flag | pre | post => simpa [Function.update_of_ne] using h
  | phase v =>
    change some (Counter.value _ (tr ++ ev) (phase v)) = _
    change some (Counter.value _ tr (phase v)) = _ at h
    rw [eq,Option.some.inj h]
    by_cases same : v = r
    · subst v; simp
    · simp [same,Function.update_of_ne]

private theorem copyTrace (r q : Fin n) (tr : Trace) (init : Counter → Nat) :
    Counter.value init (tr ++ eventLog (.copy r : Role n lanes rows cols) 0 1) (phase q) =
      Counter.value init tr (phase q) := by
  simp [eventLog,Role.groups,give,Stream.streamCounter,phase,Counter.value,Event.bump?,List.foldl_append]

private theorem tileTrace (r q : Fin n) (b : Fin (tiles rows cols)) (tr : Trace) (init : Counter → Nat) :
    Counter.value init (tr ++ eventLog (.tile r b : Role n lanes rows cols) 0 1) (phase q) =
      Counter.value init tr (phase q) := by
  simp [eventLog,Role.groups,take,Counter.value,Event.bump?,List.foldl_append]

private theorem sendTrace (r q : Fin n) (t : Fin lanes) (tr : Trace) (init : Counter → Nat) :
    Counter.value init (tr ++ eventLog (.lane r t : Role n lanes rows cols) 0 (sendPC n t)) (phase q) =
      Counter.value init tr (phase q) := by
  by_cases active : t.val < n <;>
    simp [eventLog,Role.groups,sendPC,active,take,w0,s1,phase,Counter.value,Event.bump?,List.foldl_append]

private theorem arriveTrace (r q : Fin n) (t : Fin lanes) (tr : Trace) (init : Counter → Nat) :
    Counter.value init (tr ++ eventLog (.lane r t : Role n lanes rows cols) (sendPC n t) (joinPC n t - sendPC n t))
      (phase q) = Counter.value init tr (phase q) + (if q = r then 1 else 0) := by
  have equiv : r.val = q.val ↔ q = r := ⟨fun h => Fin.ext h.symm,fun h => congrArg Fin.val h.symm⟩
  by_cases active : t.val < n <;> by_cases same : q = r <;>
    simp [eventLog,Role.groups,sendPC,joinPC,active,same,give,w1,s0,phase,Counter.value,Event.bump?,List.foldl_append,
      SignalOp.apply,equiv]

private theorem joinTrace (r q : Fin n) (t : Fin lanes) (tr : Trace) (init : Counter → Nat) :
    Counter.value init (tr ++ eventLog (.lane r t : Role n lanes rows cols) (joinPC n t) 2) (phase q) =
      Counter.value init tr (phase q) := by
  by_cases active : t.val < n <;>
    simp [eventLog,Role.groups,joinPC,active,take,give,Stream.streamCounter,phase,Counter.value,Event.bump?,List.foldl_append]

private def programPC : (r : Role n lanes rows cols) → Nat → Option Nat
  | .lane _ _,0 => some 0
  | .lane _ t,1 => some (sendPC n t)
  | .lane _ t,2 => some (joinPC n t)
  | .copy _,0 | .tile _ _,0 => some 0
  | _,_ => none

private def Pcs (stage : Stage n lanes rows cols) (c : Config Nat) :=
  ∀ a, c.pc a = (decode n lanes rows cols a).bind (fun r => (programPC r (stage r)).map Cursor.ready)

private theorem pcsAt (h : Pcs stage c) (r : Role n lanes rows cols) :
    c.pc r.owner = (programPC r (stage r)).map Cursor.ready := by rw [h r.owner,decode_owner]; rfl

private theorem pcsMove (h : Pcs stage s) (r : Role n lanes rows cols)
    (mv : Moves l s d r.owner k mem ev) (next : programPC r (stage r + 1) = k) : Pcs (bumpStage stage r) d := by
  intro a
  by_cases same : a = r.owner
  · subst a; simp [mv.pcs,bumpStage,next]
  · rw [mv.pcs,Function.update_of_ne same,h a]
    cases dec : decode n lanes rows cols a with
    | none => rfl
    | some other =>
      have apart : other ≠ r := fun eq => same ((owner_of_decode dec).symm.trans (congrArg Role.owner eq))
      simp [bumpStage,apart]

private structure DataFits (x : RankTensor n (Fin (n*rows) × Fin cols)) (stage : Stage n lanes rows cols)
    (mem : DistState) : Prop where
  inputs : Inputs x mem
  copied : ∀ (src : Fin n), stage (.copy src) = 1 → ∀ (peer : Fin n) (u : Coordinate rows cols),
    (mem.cell (scatterSlot peer src u.1 u.2)).readAs .real =
      some ((x src (finProdFinEquiv (peer,u.1),u.2)) : WithBot ℝ)

variable {stage stage' : Stage n lanes rows cols} {x : RankTensor n (Fin (n*rows) × Fin cols)} {fits : n ≤ lanes}

private theorem DataFits.retag (h : DataFits x stage mem) (same : ∀ r, stage' (.copy r) = stage (.copy r)) :
    DataFits x stage' mem := ⟨h.inputs,fun r done => h.copied r ((same r).symm.trans done)⟩

private theorem DataFits.frame (h : DataFits x stage mem)
    (same : ∀ p : Addr, p.region = "input" ∨ p.region = "scatter" → mem'.cell p = mem.cell p) :
    DataFits x stage mem' := by
  constructor
  · intro src peer u; rw [same _ (Or.inl rfl)]; exact h.inputs src peer u
  · intro src hit peer u; rw [same _ (Or.inr rfl)]; exact h.copied src hit peer u

private theorem DataFits.putControl (h : DataFits x stage mem) (wh : Control p) (val : MemCell) :
    DataFits x stage (w.put mem p val) := by
  apply h.frame
  intro a dataA
  apply w.read_other
  rintro rfl
  rcases wh with a | a <;> rcases dataA with b | b <;> simp_all

private theorem DataFits.copiedOnce {stage : Stage n lanes rows cols} (h : DataFits x stage m)
    (r : Fin n) (go : (hostCopySeg rows cols r).run m = some mem) :
    DataFits x (bumpStage stage (.copy r)) mem := by
  refine ⟨hostCopy_inputs x r h.inputs go,?_⟩
  intro src done peer u
  by_cases eq : src = r
  · subst src; exact hostCopy_placed x r h.inputs go peer u
  · rw [hostCopy_other u eq go]
    exact h.copied src (by simpa [bumpStage,eq] using done) peer u

private theorem hostFrameControl {r : Fin n} (go : (hostCopySeg rows cols r).run m = some mem) :
    ∀ p, Control p → mem.cell p = m.cell p := by
  intro p ctrl; apply hostCopy_frame r go
  rintro ⟨peer,u,rfl⟩; simp [Control,scatterSlot] at ctrl

private theorem tileFrameOther {p : Addr} {r : Fin n} {pid : Nat} (go : (encodedTileSeg rows cols r pid).run m = some mem)
    (other : p.region ≠ "output") : mem.cell p = m.cell p := by
  apply Segment.frame (encodedTileSeg_sound rows cols r pid) go
  rintro ⟨u,_,rfl⟩; exact other rfl

private structure Tracks (fits : n ≤ lanes) (x : RankTensor n (Fin (n*rows) × Fin cols))
    (w : CellWrites) (stage : Stage n lanes rows cols) (s : Config Nat) : Prop where
  pcs : Pcs stage s
  words : Matches w lanes rows cols s.mem s.trace (registerValue fits stage)
  data : DataFits x stage s.mem

private theorem initialTracks {x : RankTensor n (Fin (n*rows) × Fin cols)} (fits : n ≤ lanes) (w : CellWrites)
    (initial : Initial x s) : Tracks fits x w (fun _ => 0) ((launch true n lanes rows cols w).initial s) := by
  constructor
  · intro a
    cases eq : decode n lanes rows cols a with
    | none => simp [Launch.initial,launch,eq]
    | some role => cases role <;> simp [Launch.initial,launch,eq,programPC]
  · intro reg
    rw [registers_zero]
    cases reg with
    | flag a b => exact initial.flags a b
    | pre r => exact initial.milestones r false
    | post r => exact initial.milestones r true
    | phase r => rfl
  · exact ⟨initial.inputs,by simp⟩

private theorem copyTracks {x : RankTensor n (Fin (n*rows) × Fin cols)} (f : Tracks fits x w stage s)
    (r : Fin n) (new : stage (.copy r) = 0) (quiet : Quiet s.history) (clear : s.pending = []) :
    ∃ cs d, Run (launch true n lanes rows cols w) s cs d ∧ Tracks fits x w (bumpStage stage (.copy r)) d := by
  obtain ⟨mid,d,go,mv⟩ := copyMoves (w := w) (lanes := lanes) (rows := rows) (cols := cols) s r
    (by simpa [new,programPC] using pcsAt f.pcs (.copy r)) quiet clear (by
      simpa [observe,counterOf,registerValue,new,Stream.streamCounter] using f.words (.pre r))
  obtain ⟨cs,run⟩ := mv.ran
  refine ⟨cs,d,run,pcsMove f.pcs (.copy r) mv (by simp [new,programPC]),?_,?_⟩
  · rw [mv.memory,mv.trace,registers_copy r new]
    exact matchesTrace (matchesPut (matchesFrame f.words (hostFrameControl go)) (.pre r) rfl 1)
      (fun q => copyTrace r q _ _)
  · rw [mv.memory]; exact (f.data.copiedOnce r go).putControl (Or.inr rfl) _

private theorem sendTracks {x : RankTensor n (Fin (n*rows) × Fin cols)} (f : Tracks fits x w stage s)
    (r : Fin n) (t : Fin lanes) (new : stage (.lane r t) = 0) (copied : stage (.copy r) = 1)
    (peer : ∀ ht : t.val < n, stage (.lane ⟨t,ht⟩ (Fin.castLE fits r)) < 2)
    (quiet : Quiet s.history) (clear : s.pending = []) :
    ∃ cs d, Run (launch true n lanes rows cols w) s cs d ∧ Tracks fits x w (bumpStage stage (.lane r t)) d := by
  obtain ⟨d,mv⟩ := sendMoves (w := w) (lanes := lanes) (rows := rows) (cols := cols) s r t
    (by simpa [new,programPC] using pcsAt f.pcs (.lane r t)) quiet clear (by
      simpa [observe,counterOf,registerValue,copied,Stream.streamCounter] using f.words (.pre r)) (by
      intro ht
      simpa only [send_clear fits r t ht new] using f.words (.flag ⟨t,ht⟩ r))
  obtain ⟨cs,run⟩ := mv.ran
  refine ⟨cs,d,run,pcsMove f.pcs (.lane r t) mv (by simp [new,programPC]),?_,?_⟩
  · rw [mv.memory,mv.trace,registers_send fits r t new peer]
    apply matchesTrace _ (fun q => sendTrace r q t _ _)
    by_cases ht : t.val < n
    · simpa [sendReg,ht,writeFlag] using matchesPut f.words (.flag ⟨t,ht⟩ r) rfl 1
    · simpa [sendReg,ht,writeFlag] using f.words
  · rw [mv.memory]
    have data := f.data.retag (stage' := bumpStage stage (.lane r t)) (by simp [bumpStage])
    split_ifs <;> first | exact data | exact data.putControl (Or.inl rfl) _

private theorem arriveTracks {x : RankTensor n (Fin (n*rows) × Fin cols)} (f : Tracks fits x w stage s)
    (r : Fin n) (t : Fin lanes) (sent : stage (.lane r t) = 1)
    (peer : ∀ ht : t.val < n, 1 ≤ stage (.lane ⟨t,ht⟩ (Fin.castLE fits r)))
    (quiet : Quiet s.history) (clear : s.pending = []) :
    ∃ cs d, Run (launch true n lanes rows cols w) s cs d ∧ Tracks fits x w (bumpStage stage (.lane r t)) d := by
  obtain ⟨d,mv⟩ := arriveMoves (w := w) (lanes := lanes) (rows := rows) (cols := cols) s r t
    (by simpa [sent,programPC] using pcsAt f.pcs (.lane r t)) quiet clear (by
      intro ht
      simpa only [receive_set fits r t ht sent (peer ht)] using f.words (.flag r ⟨t,ht⟩))
  obtain ⟨cs,run⟩ := mv.ran
  refine ⟨cs,d,run,pcsMove f.pcs (.lane r t) mv (by simp [sent,programPC]),?_,?_⟩
  · rw [mv.memory,mv.trace,registers_arrive fits r t sent]
    by_cases ht : t.val < n
    · simpa [writeFlag,receiveReg,ht,Function.update_of_ne] using
        matchesArrival (matchesPut f.words (.flag r ⟨t,ht⟩) rfl 0) r (fun q => arriveTrace r q t _ _)
    · simpa [writeFlag,receiveReg,ht] using matchesArrival f.words r (fun q => arriveTrace r q t _ _)
  · rw [mv.memory]
    have data := f.data.retag (stage' := bumpStage stage (.lane r t)) (by simp [bumpStage])
    split_ifs <;> first | exact data | exact data.putControl (Or.inl rfl) _

private theorem joinTracks {x : RankTensor n (Fin (n*rows) × Fin cols)} (f : Tracks fits x w stage s)
    (r : Fin n) (t : Fin lanes) (arrived : stage (.lane r t) = 2) (allHere : laneCount stage r 2 = lanes)
    (quiet : Quiet s.history) (clear : s.pending = []) :
    ∃ cs d, Run (launch true n lanes rows cols w) s cs d ∧ Tracks fits x w (bumpStage stage (.lane r t)) d := by
  let old := registerValue fits stage (.post r)
  obtain ⟨d,mv⟩ := joinMoves (w := w) (lanes := lanes) (rows := rows) (cols := cols) s r t old
    (by simpa [arrived,programPC] using pcsAt f.pcs (.lane r t)) quiet clear
    (by simpa only [registerValue,allHere] using f.words (.phase r)) (f.words (.post r))
  obtain ⟨cs,run⟩ := mv.ran
  refine ⟨cs,d,run,pcsMove f.pcs (.lane r t) mv (by simp [arrived,programPC]),?_,?_⟩
  · rw [mv.memory,mv.trace,registers_join fits r t arrived]
    exact matchesTrace (matchesPut f.words (.post r) rfl (old+1)) (fun q => joinTrace r q t _ _)
  · rw [mv.memory]
    exact (f.data.retag (stage' := bumpStage stage (.lane r t)) (by simp [bumpStage])).putControl (Or.inr rfl) _

private theorem tileTracks {x : RankTensor n (Fin (n*rows) × Fin cols)} (f : Tracks fits x w stage s)
    (r : Fin n) (b : Fin (tiles rows cols)) (new : stage (.tile r b) = 0)
    (joined : laneCount stage r 3 = lanes) (copied : ∀ src, stage (.copy src) = 1)
    (quiet : Quiet s.history) (clear : s.pending = []) :
    ∃ cs d, Run (launch true n lanes rows cols w) s cs d ∧ Tracks fits x w (bumpStage stage (.tile r b)) d := by
  obtain ⟨mem,d,go,mv⟩ := tileMoves (w := w) x s r b
    (by simpa [new,programPC] using pcsAt f.pcs (.tile r b)) quiet clear
    (by simpa only [registerValue,joined] using f.words (.post r)) (fun peer u src => f.data.copied src (copied src) peer u)
  obtain ⟨cs,run⟩ := mv.ran
  refine ⟨cs,d,run,pcsMove f.pcs (.tile r b) mv (by simp [new,programPC]),?_,?_⟩
  · rw [mv.memory,mv.trace,registers_tile r b]
    apply matchesTrace _ (fun q => tileTrace r q b _ _)
    apply matchesFrame f.words
    intro p ctrl; apply tileFrameOther go; rcases ctrl with hf | hs
    · rw [hf]; decide
    · rw [hs]; decide
  · rw [mv.memory]
    apply (f.data.retag (stage' := bumpStage stage (.tile r b)) (by simp [bumpStage])).frame
    intro p dat; apply tileFrameOther go; rcases dat with hi | hs
    · rw [hi]; decide
    · rw [hs]; decide

theorem completeRun {x : RankTensor n (Fin (n*rows) × Fin cols)} (fits : n ≤ lanes) (w : CellWrites)
    (initial : Initial x s) :
    ∃ cs d, Run (launch true n lanes rows cols w) ((launch true n lanes rows cols w).initial s) cs d ∧ Complete d := by
  let l := launch true n lanes rows cols w
  obtain ⟨stage,steps,finished⟩ := completionPlan (rows := rows) (cols := cols) fits
  have lift {goal : Stage n lanes rows cols} (walk : PlanSteps fits (fun _ => 0) goal) :
      ∃ cs d, Run l (l.initial s) cs d ∧ Tracks fits x w goal d := by
    induction walk with
    | refl => exact ⟨[],_,.nil _,initialTracks fits w initial⟩
    | @snoc prev role prior action ih =>
      obtain ⟨cs,c,ran,state⟩ := ih
      have quiet := reachableQuiet ran
      have clear := (reachableShape ran).pending
      have go : ∃ cs' d, Run l c cs' d ∧ Tracks fits x w (bumpStage prev role) d := by
        cases action with
        | copy r new => exact copyTracks state r new quiet clear
        | send r t new copied peer => exact sendTracks state r t new copied peer quiet clear
        | arrive r t sent peer => exact arriveTracks state r t sent peer quiet clear
        | joinLanes r t arrived joined => exact joinTracks state r t arrived joined quiet clear
        | tile r b new joined copied => exact tileTracks state r b new joined copied quiet clear
      obtain ⟨cs',d,go,final⟩ := go
      exact ⟨_,d,appendRuns' ran go,final⟩
  obtain ⟨cs,d,run,state⟩ := lift steps
  refine ⟨cs,d,run,?_,by simp [(reachableShape run).pending]⟩
  intro a
  rw [state.pcs a]
  cases eq : decode n lanes rows cols a with
  | none => rfl
  | some role => have h := finished role; cases role <;> simp [h,programPC]

theorem completes {x : RankTensor n (Fin (n*rows) × Fin cols)} (fits : n ≤ lanes) (w : CellWrites)
    (initial : Initial x s) (safe : DRF (launch true n lanes rows cols w) s) :
    Completes (launch true n lanes rows cols w) s := by
  obtain ⟨cs,d,run,done⟩ := completeRun fits w initial
  exact ⟨cs,d,run,done,safe cs d run⟩

private def paddedInputs : RankTensor 2 (Fin (2*1) × Fin 65) :=
  fun r _ => (r.val + 1 : Nat)

private def paddedState : DistState where
  numRanks := 2
  cell p := if p.region = "input" then
    match p.space with
    | .global rank => finiteCell (rank + 1 : Nat)
    | _ => .of .nat 0
    else .of .nat 0
  context a := (DistState.single default).context a

/-- Two ranks, three physical lanes per CAS CTA, and two K10 tiles per rank.
The unpaired physical lane must still arrive and join the stream. Both ranks'
data start only in their own input cells. -/
theorem paddedCompleteRun :
    let l := launch true 2 3 1 65 FetchAddObservation.putCellWrites
    ∃ cs final, Run l (l.initial paddedState) cs final ∧ Complete final := by
  apply completeRun (x := paddedInputs) (by decide)
  refine ⟨?_,?_,?_⟩
  · intro src peer u; simp [inputSlot,paddedInputs,paddedState,finiteCell]
  · intro r t; rfl
  · intro r stage; rfl

#print axioms paddedCompleteRun
#print axioms completeRun
#print axioms completes
end ScheduleProof
end
end VeriTile.Tests.T05Pilot.Whole
