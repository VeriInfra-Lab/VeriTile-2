import tests.lean.dist.Tutorial05HostCopy
import tests.lean.dist.Tutorial05Stream

/-! One scheduled T05 launch. Every role has its own signed-machine cursor.
Only the receive CAS group depends on the acquire switch. Both stream
milestones are private to one rank; all physical lanes reach CO:168. -/
namespace VeriTile.Tests.T05Pilot.Whole
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
open VeriTile.Tests.T05Pilot
noncomputable section

def tiles (rows cols : Nat) := ((rows + 255) / 256) * ((cols + 63) / 64)

inductive Role (n lanes rows cols : Nat) where
  | copy (rank : Fin n)
  | lane (rank : Fin n) (id : Fin lanes)
  | tile (rank : Fin n) (block : Fin (tiles rows cols))
  deriving DecidableEq

def Role.owner : Role n lanes rows cols → Agent
  | .copy r => Stream.host r
  | .lane r t => Stream.lane r t
  | .tile r b => Stream.tile r b

def decode (n lanes rows cols : Nat) : Agent → Option (Role n lanes rows cols)
  | .cta ⟨r,[1]⟩ => if hr : r < n then some (.copy ⟨r,hr⟩) else none
  | .cta ⟨r,[b+2]⟩ => if hr : r < n then
      if hb : b < tiles rows cols then some (.tile ⟨r,hr⟩ ⟨b,hb⟩) else none else none
  | .thread ⟨r,[0]⟩ 0 t => if hr : r < n then
      if ht : t < lanes then some (.lane ⟨r,hr⟩ ⟨t,ht⟩) else none else none
  | _ => none

@[simp] theorem decode_owner (role : Role n lanes rows cols) :
    decode n lanes rows cols role.owner = some role := by
  cases role <;> simp [decode,Role.owner,Stream.host,Stream.lane,Stream.tile]

theorem owner_of_decode {role : Role n lanes rows cols} (h : decode n lanes rows cols a = some role) :
    role.owner = a := by
  unfold decode at h
  split at h <;> (repeat' split at h) <;> cases h <;> rfl

def phase (r : Nat) : Counter := .phase ⟨r,[0]⟩ 0
def roster (r lanes : Nat) := (List.finRange lanes).map (fun t => Stream.lane r t)
def give (a : Agent) (c : Counter) (scope : Scope) : Emission :=
  ⟨a,.bump ⟨c,.add,1,.atomic scope .release⟩,.noValue⟩
def take (a : Agent) (c : Counter) (scope : Scope) (count : Nat) : Emission :=
  ⟨a,.wait c .ge count (.atomic scope .acquire),.noValue⟩

def Role.groups (withAcquire : Bool) : Role n lanes rows cols → List Group
  | .copy r => [(give (Stream.host r) (Stream.streamCounter r false) .gpu,[])]
  | .tile r b => [(take (Stream.tile r b) (Stream.streamCounter r true) .gpu lanes,[])]
  | .lane r t =>
    let a := Stream.lane r t
    [(take a (Stream.streamCounter r false) .gpu 1,[])] ++
      (if t.val < n then [(w0 r t,[s1 r t])] ++ (if withAcquire then [(w1 r t,[s0 r t])] else []) else []) ++
      [(give a (phase r) .cta,[]),(take a (phase r) .cta lanes,[]),
       (give a (Stream.streamCounter r true) .gpu,[])]

def Role.segment (role : Role n lanes rows cols) (pc : Nat) : Segment :=
  match role,pc with
  | .copy r,0 => hostCopySeg rows cols r
  | .tile r b,1 => encodedTileSeg rows cols r b
  | _,_ => emptySeg role.owner

def agentProgram (withAcquire : Bool) (n lanes rows cols : Nat) (a : Agent) : AgentProgram Nat :=
  match decode n lanes rows cols a with
  | none => ⟨fun _ => emptySeg a,fun _ _ => .finish⟩
  | some role => ⟨role.segment,fun pc _ => lineNext (role.groups withAcquire) pc⟩

/-- CAS words are peer-accessible; auxiliary stream words and local inputs/outputs
are only accessed by their owning rank. -/
def symmetric (region : VeriTile.Triton.RegionName) : Bool :=
  region = "scatter" ∨ region = "flag"

def launch (withAcquire : Bool) (n lanes rows cols : Nat) (w : CellWrites) : Launch Nat where
  program := agentProgram withAcquire n lanes rows cols
  start a := (decode n lanes rows cols a).map (fun _ => 0)
  cells := w
  symm := symmetric
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster
    | .phase ⟨r,[0]⟩ 0 => if r < n then some (roster r lanes) else none
    | _ => none

/-- Actual initial source and synchronization data. Scatter memory may be stale. -/
structure Initial (x : RankTensor n (Fin (n*rows) × Fin cols)) (s : DistState) : Prop where
  inputs : Inputs x s
  flags : ∀ (rank peer : Fin n), (s.cell (flag rank peer)).readAs .nat = some 0
  milestones : ∀ (rank : Fin n) (stage : Bool), (s.cell (Stream.mark rank stage)).readAs .nat = some 0

/-- Only source-classified synchronization cells can change in an event group. -/
def Control (p : Addr) : Prop :=
  p.region = "flag" ∨ p.region = "T05.stream.shadow"

def ControlCounter : Counter → Prop
  | .word p => Control p
  | .phase .. => True
  | _ => False

def SyncEmission (a : Agent) (e : Emission) : Prop :=
  e.actor = a ∧ e.data = .noValue ∧
    ((∃ c cmp n mode, e.event = .wait c cmp n mode ∧ ControlCounter c) ∨
     (∃ b, e.event = .bump b ∧ ControlCounter b.counter))

@[simp] theorem sync_give (h : ControlCounter c) : SyncEmission a (give a c scope) :=
  ⟨rfl,rfl,.inr ⟨_,rfl,h⟩⟩
@[simp] theorem sync_take (h : ControlCounter c) : SyncEmission a (take a c scope n) :=
  ⟨rfl,rfl,.inl ⟨_,_,_,_,rfl,h⟩⟩
@[simp] theorem marker_control (r stage) : ControlCounter (Stream.streamCounter r stage) := Or.inr rfl
@[simp] theorem phase_control (r) : ControlCounter (phase r) := trivial

private theorem sendGroup (r t : Nat) : CASGroup (w0 r t) [s1 r t] ∧
    ∀ e ∈ [w0 r t,s1 r t], SyncEmission (Stream.lane r t) e := by
  refine ⟨.inr ⟨_,_,0,1,.sys,.relaxed,.release,rfl,rfl,rfl,rfl⟩,?_⟩
  intro e he; simp at he
  rcases he with rfl|rfl
  · exact ⟨rfl,rfl,.inl ⟨_,_,_,_,rfl,.inl rfl⟩⟩
  · exact ⟨rfl,rfl,.inr ⟨_,rfl,.inl rfl⟩⟩

private theorem receiveGroup (r t : Nat) : CASGroup (w1 r t) [s0 r t] ∧
    ∀ e ∈ [w1 r t,s0 r t], SyncEmission (Stream.lane r t) e := by
  refine ⟨.inr ⟨_,_,1,0,.sys,.acquire,.relaxed,rfl,rfl,rfl,rfl⟩,?_⟩
  intro e he; simp at he
  rcases he with rfl|rfl
  · exact ⟨rfl,rfl,.inl ⟨_,_,_,_,rfl,.inl rfl⟩⟩
  · exact ⟨rfl,rfl,.inr ⟨_,rfl,.inl rfl⟩⟩

theorem Role.good (role : Role n lanes rows cols) (on : Bool) (g : Group)
    (hg : g ∈ role.groups on) : CASGroup g.1 g.2 ∧ ∀ e ∈ g.1 :: g.2, SyncEmission role.owner e := by
  cases role with
  | copy r =>
    simp [Role.groups] at hg; subst g
    exact ⟨.inl rfl,by simp [Role.owner]⟩
  | tile r b =>
    simp [Role.groups] at hg; subst g
    exact ⟨.inl rfl,by simp [Role.owner]⟩
  | lane r t =>
    cases on <;> by_cases active : t.val < n <;> simp [Role.groups,active] at hg
    all_goals (repeat' rcases hg with hg | hg)
    all_goals first | exact sendGroup r t | exact receiveGroup r t |
      exact ⟨.inl rfl,by simp [Role.owner]⟩

theorem Role.segSound (role : Role n lanes rows cols) (pc : Nat) : (role.segment pc).FootprintSound := by
  cases role with
  | copy r => cases pc with
    | zero => exact hostCopy_sound _ _ _
    | succ pc => exact VeriTile.Tests.FetchAddObservation.emptySound _
  | lane r t => cases pc <;> exact VeriTile.Tests.FetchAddObservation.emptySound _
  | tile r b => cases pc with
    | zero => exact VeriTile.Tests.FetchAddObservation.emptySound _
    | succ pc => cases pc with
      | zero => exact encodedTileSeg_sound _ _ _ _
      | succ _ => exact VeriTile.Tests.FetchAddObservation.emptySound _

def erase : Occurrence → Occurrence
  | .segment a _ _ => segOf a
  | x => x

@[simp] theorem erase_program (x : Occurrence) : (erase x).program? = x.program? := by cases x <;> rfl
@[simp] theorem erase_event (x : Occurrence) : (erase x).event? = x.event? := by cases x <;> rfl

def script (on : Bool) (n lanes rows cols : Nat) (a : Agent) :=
  (decode n lanes rows cols a).map (Role.groups on)

theorem allowed {d : Role n lanes rows cols} (hs : decode n lanes rows cols a = some d)
    (hg : g ∈ d.groups on) (he : x ∈ g.1 :: g.2) : SyncEmission a x :=
  owner_of_decode hs ▸ (d.good on _ hg).2 x he

theorem event_noInit (good : SyncEmission a x) (t : Transfer) : x.event ≠ .initiate t := by
  rcases good.2.2 with ⟨_,_,_,_,h,_⟩|⟨_,h,_⟩ <;> rw [h] <;> intro bad <;> cases bad

theorem script_noInit : NoInit (script on n lanes rows cols) := by
  intro a gs hs g hg e he t
  obtain ⟨role,hd,rfl⟩ := Option.map_eq_some_iff.mp hs
  exact event_noInit (allowed hd hg he) t

structure Shape (on : Bool) (n lanes rows cols : Nat) (s : Config Nat) : Prop where
  pending : s.pending = []
  log : ∀ a, AgentLog (script on n lanes rows cols a) a (s.pc a) (filterA a (s.history.map erase))
  programs : ∀ x ∈ s.history, x.program? = some x.owner

theorem shape_initial (on n lanes rows cols w s) :
    Shape on n lanes rows cols ((launch on n lanes rows cols w).initial s) := by
  refine ⟨rfl,?_,by simp [Launch.initial]⟩
  intro a
  cases hd : decode n lanes rows cols a <;> simp [Launch.initial,launch,hd,AgentLog,script,filterA,logUpTo]

/-- Real firing appends precisely its source events and cannot create deliveries. -/
theorem groupTrace {l : Launch P} {s f : Machine}
    (g : FireGroup l a s es f vs) (good : ∀ x ∈ es, SyncEmission a x) :
    f.history = s.history ++ es.map (.issued a) ∧ f.pending = s.pending := by
  induction g with
  | nil => simp
  | @cons s x mem pending v xs final vs access available ordered fire rest ih =>
    have hx := good x (by simp)
    have hp : pending = s.pending := by
      cases fire <;> first | rfl | exact False.elim (event_noInit hx _ rfl)
    obtain ⟨hist,pend⟩ := ih (fun y hy => good _ (by simp [hy]))
    exact ⟨by simpa using hist,pend.trans hp⟩

theorem step_shape {s f : Config Nat} (h : Shape on n lanes rows cols s)
    (st : step (launch on n lanes rows cols w) s ch f) : Shape on n lanes rows cols f := by
  obtain ⟨pend,log,progs⟩ := h
  cases st with
  | @segment a pc seg mem atPC code owner access success =>
    have alog := log a
    rw [atPC] at alog
    obtain ⟨gs,scriptA,le,hl⟩ := alog
    obtain ⟨role,hd,rfl⟩ := Option.map_eq_some_iff.mp scriptA
    refine ⟨pend,fun b => ?_,?_⟩
    · change AgentLog _ b (Function.update s.pc a _ b) (filterA b ((s.history ++ [_]).map erase))
      simp only [List.map_append,List.map_cons,List.map_nil,erase,filterA_append,filterA_seg]
      by_cases same : b = a
      · subst b
        rw [Function.update_self,if_pos rfl]
        simp only [launch,agentProgram,hd,lineNext]
        cases hn : (role.groups on)[pc]? with
        | some g => exact ⟨_,pc,scriptA,by simp [hn],rfl,by rw [hl]⟩
        | none =>
          have : pc = (role.groups on).length := le_antisymm le (by simpa using hn)
          subst pc
          simp [Next.cursor,AgentLog,scriptA,fullLog,hl]
      · rw [Function.update_of_ne same, if_neg (Ne.symm same),List.append_nil]; exact log b
    · intro x hx
      rcases List.mem_append.mp hx with hx|hx
      · exact progs x hx
      · simp at hx; subst x; rfl
  | @fire a x xs cont final values atPC own events =>
    have alog := log a
    rw [atPC] at alog
    obtain ⟨gs,pc,scriptA,atG,rfl,hl⟩ := alog
    obtain ⟨role,hd,rfl⟩ := Option.map_eq_some_iff.mp scriptA
    have good := fun e he => allowed hd (List.mem_of_getElem? atG) (x := e) he
    obtain ⟨hist,pending⟩ := groupTrace events good
    refine ⟨pending.trans pend,fun b => ?_,?_⟩
    · change AgentLog _ b (Function.update s.pc a _ b) (filterA b (final.history.map erase))
      rw [hist,List.map_append,List.map_map]
      change AgentLog _ b _ (filterA b (s.history.map erase ++ (x :: xs).map (.issued a)))
      rw [filterA_append,filterA_issued]
      by_cases same : b = a
      · subst b
        rw [Function.update_self,if_pos rfl]
        refine ⟨_,scriptA,?_,?_⟩
        · exact (List.getElem?_eq_some_iff.mp atG).1
        · rw [hl,logUpTo_succ a atG]; simp [groupLog]
      · rw [Function.update_of_ne same, if_neg (Ne.symm same),List.append_nil]; exact log b
    · intro occ hx
      rw [hist] at hx
      rcases List.mem_append.mp hx with hx|hx
      · exact progs _ hx
      · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
        exact congrArg some (good e he).1.symm
  | @deliver pre post o b old outstanding bound counter ordered disjoint access free =>
    rw [pend] at outstanding
    simp at outstanding

theorem reachableShape {s : DistState} {sched f} (run : Run (launch on n lanes rows cols w)
    ((launch on n lanes rows cols w).initial s) sched f) : Shape on n lanes rows cols f := by
  have go {u d : Config Nat} {cs} (run : Run (launch on n lanes rows cols w) u cs d)
      (hu : Shape on n lanes rows cols u) : Shape on n lanes rows cols d := by
    induction run with
    | nil => exact hu
    | cons st _ ih => exact ih (step_shape hu st)
  exact go run (shape_initial _ _ _ _ _ _ _)

theorem reachableQuiet {s : DistState} {sched f} (run : Run (launch on n lanes rows cols w)
    ((launch on n lanes rows cols w).initial s) sched f) : Quiet f.history := by
  intro pair mem t
  obtain ⟨x,hx,evt⟩ := List.mem_filterMap.mp mem
  have shape := reachableShape run
  have hx' : erase x ∈ filterA x.owner (f.history.map erase) := by
    simp [filterA,List.mem_map.mpr ⟨_,hx,rfl⟩,shape.programs x hx]
  obtain hseg | ⟨gs,scriptA,g,hg,e,he,id⟩ := agentLog_mem (shape.log x.owner) hx'
  · have en := congrArg Occurrence.event? hseg
    rw [erase_event,evt] at en; cases en
  · have en := congrArg Occurrence.event? id
    rw [erase_event,evt] at en
    cases en
    exact script_noInit _ _ scriptA g hg e he t

theorem sound (on n lanes rows cols w) : SoundLaunch (launch on n lanes rows cols w) where
  localNext := by
    intro a pc s t equal
    cases h : decode n lanes rows cols a <;> simp [launch,agentProgram,h]
  footprints := by
    intro a pc
    cases h : decode n lanes rows cols a with
    | none => exact (show ((agentProgram on n lanes rows cols a).segment pc).FootprintSound by
        simpa [agentProgram,h] using VeriTile.Tests.FetchAddObservation.emptySound a)
    | some r => simpa [launch,agentProgram,h] using r.segSound pc
  pidLength := by
    intro a c started ca
    obtain ⟨r,hr⟩ : ∃ r, decode n lanes rows cols a = some r := by
      cases hd : decode n lanes rows cols a <;> simp_all [launch]
    rw [← owner_of_decode hr] at ca
    cases r <;> cases ca <;> rfl
  groups := by
    intro a pc s h t k emitted
    cases hd : decode n lanes rows cols a with
    | none => simp [launch,agentProgram,hd] at emitted
    | some r =>
      simp only [launch,agentProgram,hd,lineNext] at emitted
      cases atG : (r.groups on)[pc]? with
      | none => simp [atG] at emitted
      | some g =>
        simp only [atG,Next.emitGroup.injEq] at emitted
        obtain ⟨rfl,rfl,_⟩ := emitted
        obtain ⟨cas,actors⟩ := r.good on g (List.mem_of_getElem? atG)
        exact ⟨cas,fun e he => (actors e he).1 ▸ owner_of_decode hd ▸ VeriTile.Tests.FetchAddObservation.own a⟩
  nestedPath := by
    intro s sched f run x hx y hy a px py
    have H := reachableShape run
    rw [H.programs x hx] at px; rw [H.programs y hy] at py
    rw [Option.some.inj px,Option.some.inj py]
    exact .inl (VeriTile.Tests.FetchAddObservation.own a)
  uniqueThreadPath := by
    intro s sched f run x hx y hy c g t ox oy a b px py
    have H := reachableShape run
    rw [H.programs x hx] at px; rw [H.programs y hy] at py
    exact (Option.some.inj px).symm.trans (ox.trans (oy.symm.trans (Option.some.inj py)))

/-- Independent zero-based interpretation of the relevant counter in an
actual signed history. Ordinary segments never write these locations. -/
def recorded (c : Counter) (h : History) : Nat :=
  Counter.value (fun _ => 0) (h.filterMap Occurrence.event?) c

def tracked (l : Launch P) (m : Machine) (c : Counter) := m.count? l.initialCount c = some (recorded c m.history)

def ReadyAt (c : Counter) (h : History) : Prop :=
  ∀ (j : Nat) (prog : Agent) (e : Emission) (cmp : Cmp) (target : Nat) (mode : Mode), h[j]? = some (.issued prog e) → e.event = .wait c cmp target mode →
    cmp.holds (recorded c (h.take j)) target

theorem recorded_seg (c a reads writes h) :
    recorded c (h ++ [.segment a reads writes]) = recorded c h := by
  simp [recorded,Occurrence.event?]

theorem recorded_wait (c d cmp target mode a e h) (ev : e.event = .wait d cmp target mode) :
    recorded c (h ++ [.issued a e]) = recorded c h := by
  simp [recorded,Occurrence.event?,Counter.value,ev,Event.bump?]

theorem recorded_bump (c bump a e h) (ev : e.event = .bump bump) :
    recorded c (h ++ [.issued a e]) =
      if bump.counter = c then bump.op.apply (recorded c h) bump.amount else recorded c h := by
  by_cases b : bump.counter = c <;> simp [recorded,Occurrence.event?,Counter.value,ev,Event.bump?,b]

theorem controlFrame (role : Role n lanes rows cols) (pc : Nat) (p : Addr) (hp : Control p)
    (run : (role.segment pc).run s = some f) : f.cell p = s.cell p := by
  apply Segment.frame (role.segSound pc) run
  cases role with
  | lane r t => cases pc <;> exact Set.notMem_empty _
  | copy r =>
    cases pc with
    | zero =>
      rintro ⟨_,_,eq⟩; rw [eq] at hp; rcases hp with h|h
      all_goals first | exact (by decide : ("scatter" : VeriTile.Triton.RegionName) ≠ "flag") h | exact (by decide : ("scatter" : VeriTile.Triton.RegionName) ≠ "T05.stream.shadow") h
    | succ => exact Set.notMem_empty _
  | tile r b =>
    cases pc with
    | zero => exact Set.notMem_empty _
    | succ pc =>
      cases pc with
      | zero =>
        rintro ⟨_,_,eq⟩; rw [eq] at hp; rcases hp with h|h
        all_goals first | exact (by decide : ("output" : VeriTile.Triton.RegionName) ≠ "flag") h | exact (by decide : ("output" : VeriTile.Triton.RegionName) ≠ "T05.stream.shadow") h
      | succ => exact Set.notMem_empty _

theorem zeroInit (c : Counter) : (launch on n lanes rows cols w).initialCount c = 0 := by
  cases c <;> rfl

theorem nonwordTracked {M : Machine} (h : ∀ p, c ≠ .word p) :
    tracked (launch on n lanes rows cols w) M c := by
  have hz : (launch on n lanes rows cols w).initialCount = fun _ => 0 := funext zeroInit
  cases c with
  | word p => exact False.elim (h p rfl)
  | phase | rendezvous | delivered => simp [tracked,Machine.count?,Machine.trace,recorded,hz]

theorem fireTracked {M : Machine} (fr : Fire (launch on n lanes rows cols w) M e mem pending value)
    (good : SyncEmission a e) (ready : tracked (launch on n lanes rows cols w) M c) :
    tracked (launch on n lanes rows cols w) ⟨mem,M.history ++ [.issued a e],pending⟩ c := by
  cases c with
  | phase | rendezvous | delivered => exact nonwordTracked (by intro p h; cases h)
  | word p =>
    change (mem.cell p).readAs .nat = some (recorded (.word p) (M.history ++ [.issued a e]))
    change (M.mem.cell p).readAs .nat = some (recorded (.word p) M.history) at ready
    obtain ⟨actor,event,data⟩ := e
    obtain ⟨rfl,rfl,⟨d,cmp,n,mode,he,_⟩|⟨b,he,_⟩⟩ := good
    · cases he; cases fr; rw [recorded_wait _ _ _ _ _ _ _ _ rfl]; exact ready
    · cases he; cases fr with
      | bump _ _ old read =>
        rw [recorded_bump _ _ _ _ _ rfl]
        cases b with
        | mk d op amount mode =>
          cases d with
          | phase | rendezvous | delivered => simpa using ready
          | word q =>
            by_cases eq : q = p
            · subst q; simp only [↓reduceIte]
              change ((w.put M.mem p (.of .nat (op.apply old amount))).cell p).readAs .nat = _
              rw [w.read_same,VeriTile.Triton.MemCell.readAs_of_same]
              cases op with
              | set => rfl
              | add =>
                have hh : old = recorded (.word p) M.history :=
                  Option.some.inj ((read rfl).symm.trans ready)
                rw [hh]
            · simp [eq]
              change ((w.put M.mem q _).cell p).readAs .nat = _
              rw [w.read_other _ _ _ _ (Ne.symm eq)]; exact ready

theorem groupTracked {M f : Machine} (g : FireGroup (launch on n lanes rows cols w) a M es f vals)
    (allowed : ∀ x ∈ es, SyncEmission a x) (track : tracked (launch on n lanes rows cols w) M c) :
    tracked (launch on n lanes rows cols w) f c ∧
    ∀ (i : Nat) (e : Emission), es[i]? = some e → ∀ (cmp : Cmp) (target : Nat) (mode : Mode), e.event = .wait c cmp target mode →
        cmp.holds (recorded c (M.history ++ (es.take i).map (.issued a))) target := by
  induction g with
  | nil => exact ⟨track,by simp⟩
  | @cons M e mem pending v xs final vs accessible available ordered fire rest ih =>
    have h := fireTracked fire (allowed e (by simp)) track
    obtain ⟨ht,next⟩ := ih (fun x hx => allowed _ (by simp [hx])) h
    refine ⟨ht,?_⟩
    intro i x atX cmp target mode ev
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at atX
      subst x
      simp only [List.take_zero,List.map_nil,List.append_nil]
      cases fire <;> cases ev
      rename_i old read enabled
      have eq := Option.some.inj (read.symm.trans track)
      exact eq ▸ enabled
    | succ i => simpa using next i x (by simpa using atX) cmp target mode ev

theorem ready_append {xs : History} (old : ReadyAt c h)
    (next : ∀ (j : Nat) (a : Agent) (e : Emission) (cmp : Cmp) (target : Nat) (mode : Mode), xs[j]? = some (.issued a e) → e.event = .wait c cmp target mode →
        cmp.holds (recorded c (h ++ xs.take j)) target) : ReadyAt c (h ++ xs) := by
  intro j a e cmp target mode atE ev
  by_cases left : j < h.length
  · rw [List.getElem?_append_left left] at atE
    rw [take_snoc_of_lt xs left.le]; exact old _ _ _ _ _ _ atE ev
  · rw [List.getElem?_append_right (by omega)] at atE
    rw [List.take_append,List.take_of_length_le (by omega)]
    exact next _ _ _ _ _ _ atE ev

structure Clock (on : Bool) (n lanes rows cols : Nat) (w : CellWrites) (c : Counter)
    (s : Config Nat) : Prop where
  now : tracked (launch on n lanes rows cols w) s.toMachine c
  waits : ReadyAt c s.history

theorem clock_step {s f : Config Nat} (shape : Shape on n lanes rows cols s) (hc : ControlCounter c)
    (H : Clock on n lanes rows cols w c s) (st : step (launch on n lanes rows cols w) s ch f) :
    Clock on n lanes rows cols w c f := by
  cases st with
  | @segment a pc seg mem atPC code owner access success =>
    have atRole := shape.log a
    rw [atPC] at atRole
    obtain ⟨_,hs,_,_⟩ := atRole
    obtain ⟨r,hd,rfl⟩ := Option.map_eq_some_iff.mp hs
    subst code
    have run : (r.segment pc).run s.mem = some mem := by simpa [launch,agentProgram,hd] using success
    refine ⟨?_,ready_append H.waits ?_⟩
    · cases c with
      | phase | rendezvous | delivered => exact nonwordTracked (by intro p h; cases h)
      | word p =>
        change (mem.cell p).readAs .nat = some (recorded (.word p) (s.history ++ [.segment a _ _]))
        rw [recorded_seg,controlFrame r pc p hc run]
        exact H.now
    · intro j a' e cmp target mode atE
      cases j <;> simp at atE
  | @fire a h tl k final values atPC own events =>
    have atRole := shape.log a
    rw [atPC] at atRole
    obtain ⟨_,_,hs,atG,_,_⟩ := atRole
    obtain ⟨r,hd,rfl⟩ := Option.map_eq_some_iff.mp hs
    have good := fun x hx => allowed hd (List.mem_of_getElem? atG) (x := x) hx
    obtain ⟨hist,_⟩ := groupTrace events good
    obtain ⟨now,ok⟩ := groupTracked events good H.now
    refine ⟨now,?_⟩
    change ReadyAt c final.history
    rw [hist]
    apply ready_append H.waits
    intro j a' e cmp target mode atE ev
    rw [List.getElem?_map] at atE
    cases atJ : (h::tl)[j]? with
    | none => simp [atJ] at atE
    | some e' =>
      simp [atJ] at atE
      obtain ⟨rfl,rfl⟩ := atE
      rw [← List.map_take]
      exact ok j e' atJ cmp target mode ev
  | @deliver pre post o b old outstanding bound counter ordered disjoint access free =>
    rw [shape.pending] at outstanding; simp at outstanding

theorem history_clock {s : DistState} {sched f} {c : Counter} (run : Run (launch on n lanes rows cols w)
    ((launch on n lanes rows cols w).initial s) sched f) (hc : ControlCounter c)
    (zero : ∀ p, c = .word p → (s.cell p).readAs .nat = some 0) : Clock on n lanes rows cols w c f := by
  have start : Clock on n lanes rows cols w c ((launch on n lanes rows cols w).initial s) := by
    refine ⟨?_,by intro j a e cmp target mode atE; simp [Launch.initial] at atE⟩
    cases c with
    | word p => exact zero p rfl
    | phase | rendezvous | delivered => exact nonwordTracked (by intro p h; cases h)
  have walk {a b : Config Nat} {cs} (r : Run (launch on n lanes rows cols w) a cs b)
      (shape : Shape on n lanes rows cols a) (cnt : Clock on n lanes rows cols w c a) :
      Clock on n lanes rows cols w c b := by
    induction r with
    | nil => exact cnt
    | cons st _ ih => exact ih (step_shape shape st) (clock_step shape hc cnt st)
  exact walk run (shape_initial _ _ _ _ _ _ _) start

theorem role_prefix (H : Shape on n lanes rows cols s) (r : Role n lanes rows cols) :
    filterA r.owner (s.history.map erase) <+: fullLog r.owner (r.groups on) := by
  have hlog := H.log r.owner
  simp only [script,decode_owner,Option.map_some] at hlog
  exact agentLog_prefix hlog

theorem history_ready {s : DistState} {sched f} {c : Counter} (run : Run (launch on n lanes rows cols w)
    ((launch on n lanes rows cols w).initial s) sched f) (hc : ControlCounter c)
    (zero : ∀ p, c = .word p → (s.cell p).readAs .nat = some 0) : ReadyAt c f.history :=
  (history_clock run hc zero).waits

/-- Every issued occurrence in every reachable prefix has an actual owner,
group and member of the source program for that role. -/
theorem issued_group {i : Nat} {a : Agent} {e : Emission} (H : Shape on n lanes rows cols s) (hx : s.history[i]? = some (Occurrence.issued a e)) :
    ∃ (r : Role n lanes rows cols) (g : Group), r.owner = a ∧ g ∈ r.groups on ∧ e ∈ g.1 :: g.2 := by
  have elem : erase (.issued a e) ∈ filterA a (s.history.map erase) := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨_,List.mem_of_getElem? hx,rfl⟩,by simp [erase,Occurrence.program?]⟩
  obtain bad|⟨gs,hs,g,hg,x,hx',eq⟩ := agentLog_mem (H.log a) elem
  · cases bad
  · obtain ⟨r,hd,rfl⟩ := Option.map_eq_some_iff.mp hs
    cases eq; exact ⟨r,g,owner_of_decode hd,hg,hx'⟩

#print axioms history_clock
#print axioms role_prefix
#print axioms reachableShape
#print axioms reachableQuiet
#print axioms sound
end
end VeriTile.Tests.T05Pilot.Whole
