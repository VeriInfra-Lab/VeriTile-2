/- Distributed execution, schedule folds and blocked events for S4.2 (#48). -/
import VeriTile.Dist.Segment
import VeriTile.Dist.Event.Transfer
import VeriTile.Dist.Event.Access
import VeriTile.Dist.Event.Counter
import VeriTile.Dist.SymmHeap

namespace VeriTile.Dist
open VeriTile.Triton (MemCell)

/-- Signed (#47, via step_comm). Part 2. The memory operand or discarded result attached to an event. -/
inductive AccessValue where
  | noValue
  /-- A word-add whose old value is discarded before reaching the continuation. -/
  | discardAddResult
  | store (value : MemCell)
  | update (apply : MemCell → MemCell)

/-- Signed (#47, via step_comm). Part 2. An issued event together with its actor and value information. -/
structure Emission where
  actor : Agent
  event : Event
  data : AccessValue := .noValue

/-- Signed (#47, via step_comm). Part 2. Finish, or issue a nonempty group and continue with the result of each
member in source order. Each member carries its actor and typed payload. -/
inductive Next (P : Type) where
  | finish
  | emitGroup (head : Emission) (tail : List Emission) (k : List (Option MemCell) → P)

/-- Signed (#47, via step_comm). Part 2. Owner: S3.3. The program of one agent, cut at its
events. `segment p` is the code from program state `p` up to the next event,
or up to the end. `next p σ` is what follows that segment when it starts in
`σ`: the event with its evaluated arguments, and the program state after it.
A loop whose body holds an event is a program state that `next` returns
again; how often depends on the states and on the values read. -/
structure AgentProgram (P : Type) where
  segment : P → Segment
  next : P → DistState → Next P

/-- Port required from the S1.5 store. A write changes one cell and no
agent-local state. Location layout is fixed over this execution. -/
structure CellWrites where
  put : DistState → Addr → MemCell → DistState
  read_same : ∀ s p v, (put s p v).cell p = v
  read_other : ∀ s p q v, q ≠ p → (put s p v).cell q = s.cell q
  local_frame : ∀ s p v a, DistState.SameLocal a s (put s p v)
  commute : ∀ s p q u v, p ≠ q → put (put s p u) q v = put (put s q v) p u

/-- One occurrence, including accesses of a sequential segment. Delivery
belongs to the issuing agent for scope checks, outside its program order. -/
inductive Occurrence where
  | segment (owner : Agent) (reads writes : Set Addr)
  | issued (program : Agent) (emission : Emission)
  | delivered (owner : Agent) (t : Transfer) (start : Nat)

def Occurrence.owner : Occurrence → Agent
  | .segment a .. | .delivered a .. => a
  | .issued _ x => x.actor

def Occurrence.event? : Occurrence → Option (Agent × Event)
  | .segment .. => none
  | .issued _ x => some (x.actor,x.event)
  | .delivered a t _ => some (a,.complete t)

/-- Only program occurrences have a position on a source path. The actor
of an issued event still determines permission, scope and synchronization. -/
def Occurrence.program? : Occurrence → Option Agent
  | .segment a .. | .issued a _ => some a
  | .delivered .. => none

def Occurrence.access (p : Addr) : Occurrence → AccessKind → Mode → Prop
  | .segment _ r _, .load, .plain => p ∈ r
  | .segment _ _ w, .store, .plain => p ∈ w
  | .issued _ x, k, m => (k,p,m) ∈ x.event.accesses
  | .delivered _ t _, k, m => (k,p,m) ∈ (Event.complete t).accesses
  | _, _, _ => False

structure Outstanding where
  owner : Agent
  transfer : Transfer
  /-- Initiation occurrence; distinguishes repeated, field-identical puts. -/
  start : Nat
  /-- A blocking put snapshots the source; an NBI put reads on delivery. -/
  values : Option (List MemCell)

structure Machine where
  mem : DistState
  history : List Occurrence := []
  pending : List Outstanding := []

def Machine.trace (s : Machine) : Trace := s.history.filterMap Occurrence.event?

structure Launch (P : Type) where
  program : Agent → AgentProgram P
  start : Agent → Option P
  symm : VeriTile.Triton.RegionName → Bool
  reach : ShmemReach
  gridRank : Rank → Nat
  abstractInitial : {c : Counter // ∀ p, c ≠ .word p} → Nat
  /-- Participants of a documented collective, with a fixed object id and
  cumulative thresholds across generations. Supplied by the source lowering only for an actual barrier. -/
  roster : Counter → Option (List Agent)
  cells : CellWrites

/-- The launch has no separately settable initial word table. This extension
is used only for non-word trace folds; count? reads word values from memory. -/
def Launch.initialCount (l : Launch P) : Counter → Nat
  | .word _ => 0
  | .phase c i => l.abstractInitial ⟨.phase c i, by intro p h; cases h⟩
  | .rendezvous i => l.abstractInitial ⟨.rendezvous i, by intro p h; cases h⟩
  | .delivered a => l.abstractInitial ⟨.delivered a, by intro p h; cases h⟩

/-- A word read by an access and by a wait is the same physical cell. A
non-word counter is the signed fold over the synchronization trace. -/
noncomputable def Machine.count? (s : Machine) (init : Counter → Nat) : Counter → Option Nat
  | .word p => (s.mem.cell p).readAs .nat
  | c => some (Counter.value init s.trace c)

private def bumpMem (w : CellWrites) (s : DistState) (b : Bump) (old : Nat) : DistState :=
  match b.counter with
  | .word p => w.put s p (.of .nat (b.op.apply old b.amount))
  | _ => s

/-- Signed (#47, via step_comm; `wait` and `bump` re-signed 2026-11-26). N5. Loads and
updates return their old cell. A wait and an adding bump
return the old count only for a memory word; on a phase, rendezvous or
delivery counter they return none, as `__syncthreads`, `barrier_all` and
`quiet` return no count (#47, 2026-11-25). Stores, fences, set bumps and
initiations return none. A completion takes no continuation. An access with missing or
wrong data cannot execute. Actor choice and payload are separate from Event. -/
inductive Fire {P : Type} (l : Launch P) (s : Machine) :
    Emission → DistState → List Outstanding → Option MemCell → Prop where
  | load (a p m) : Fire l s ⟨a,.access .load p m,.noValue⟩ s.mem s.pending (some (s.mem.cell p))
  | store (a p m v) : Fire l s ⟨a,.access .store p m,.store v⟩
      (l.cells.put s.mem p v) s.pending none
  | update (a p m f) : Fire l s ⟨a,.access .update p m,.update f⟩
      (l.cells.put s.mem p (f (s.mem.cell p))) s.pending (some (s.mem.cell p))
  | fence (a m) : Fire l s ⟨a,.fence m,.noValue⟩ s.mem s.pending none
  | wait (a c cmp n m old) (read : s.count? l.initialCount c = some old) (enabled : cmp.holds old n) :
      Fire l s ⟨a,.wait c cmp n m,.noValue⟩ s.mem s.pending
        (match c with | .word _ => some (.of .nat old) | _ => none)
  | bump (a b old) (read : b.op = .add → s.count? l.initialCount b.counter = some old) :
      Fire l s ⟨a,.bump b,.noValue⟩ (bumpMem l.cells s.mem b old) s.pending
        (if b.op = .add then (match b.counter with | .word _ => some (.of .nat old) | _ => none)
          else none)
  | discardAdd (a p n m old) (read : s.count? l.initialCount (.word p) = some old) :
      Fire l s ⟨a,.bump ⟨.word p,.add,n,m⟩,.discardAddResult⟩
        (l.cells.put s.mem p (.of .nat (old + n))) s.pending none
  | initiate (a t) (sizes : t.src.length = t.dst.length) :
      Fire l s ⟨a,.initiate t,.noValue⟩ s.mem
        (⟨a,t,s.history.length,if t.nbi then none else some (t.src.map s.mem.cell)⟩ :: s.pending) none

/-- D4/D7: the caller participated in its own collective block operation.
This grants no coverage of operations issued separately by sibling threads. -/
def FenceCovers (caller issuer : Agent) : Prop :=
  caller = issuer ∨ ∃ c g t, caller = .thread c g t ∧ issuer = .cta c

/-- D1/D7: only eligible blocking puts to the signal PE are ordered. An
unbound blocking put can therefore block a subsequent fenced signal forever
under W5; a source promising liveness must supply a completion. -/
def PendingFence (s : Machine) (x : Emission) : Prop :=
  ∃ old ∈ s.pending, ∃ i mode b p r,
    old.transfer.nbi = false ∧ FenceCovers x.actor old.owner ∧ old.start < i ∧
    (s.history[i]? >>= Occurrence.event?) = some (x.actor,.fence (.shmem mode)) ∧
    x.event = .bump b ∧ b.counter = .word p ∧ (∃ order, b.mode = .shmem order) ∧
    p.space = .global r ∧ ∃ dst ∈ old.transfer.dst, dst.space = .global r

/-- Entire nonempty group is one scheduler choice. Earlier events in it are
visible to its later events. Other programs cannot enter between them. -/
inductive FireGroup {P} (l : Launch P) (program : Agent) : Machine → List Emission → Machine → List (Option MemCell) → Prop
  | nil (s) : FireGroup l program s [] s []
  | cons {s x mem pending v xs final vs} (access : x.event.AccessibleBy l.symm x.actor)
      (available : ∀ k p m, (k,p,m) ∈ x.event.accesses → ¬ InFlight s.trace p)
      (ordered : ¬ PendingFence s x)
      (fire : Fire l s x mem pending v)
      (rest : FireGroup l program ⟨mem,s.history ++ [.issued program x],pending⟩ xs final vs) :
      FireGroup l program s (x :: xs) final (v :: vs)

/-- The phase split allows another agent or the delivery engine to run after
a segment and before its events. A blocked wait never repeats its segment. -/
inductive Cursor (P : Type) where
  | ready (pc : P)
  | waiting (head : Emission) (tail : List Emission) (cont : List (Option MemCell) → P)

def Next.cursor : Next P → Option (Cursor P)
  | .finish => none
  | .emitGroup h t k => some (.waiting h t k)

structure Config (P : Type) extends Machine where
  pc : Agent → Option (Cursor P)

def Launch.initial (l : Launch P) (s : DistState) : Config P :=
  { mem := s, pc := fun a => (l.start a).map Cursor.ready }

inductive Choice where
  | agent (a : Agent)
  | delivery (ticket : Nat)

abbrev Schedule := List Choice

private noncomputable def deliverMemory (w : CellWrites) (s : Machine) (o : Outstanding)
    (b : Bump) (old : Nat) : DistState :=
  let data := o.values.getD (o.transfer.src.map s.mem.cell)
  let copied := (o.transfer.dst.zip data).foldl (fun acc (p,v) => w.put acc p v) s.mem
  bumpMem w copied b old

/-- D1/D7: a fence orders delivery of blocking operations only; it orders the caller's earlier puts to the same destination PE.
The caller participates in its CTA collective; it does not cover a sibling thread's separate put.
The event carries a destination list, so compare the actual destination ranks. -/
def FencedBefore (s : Machine) (x y : Outstanding) : Prop :=
  x.transfer.nbi = false ∧ y.transfer.nbi = false ∧ (∃ caller i m, FenceCovers caller x.owner ∧ FenceCovers caller y.owner ∧ x.start < i ∧ i < y.start ∧
    (s.history[i]? >>= Occurrence.event?) = some (caller,.fence (.shmem m))) ∧
  ∃ px ∈ x.transfer.dst, ∃ py ∈ y.transfer.dst, ∃ r, px.space = .global r ∧ py.space = .global r

/-- S4.2/#48 and S4.9/#55. A segment runs once, an enabled group fires once,
or a single matching pending transfer copies its captured/current values and
signals atomically. The engine may never deliver an unbound transfer. -/
inductive step {P} (l : Launch P) (s : Config P) : Choice → Config P → Prop where
  | segment {a pc seg mem} (atPC : s.pc a = some (.ready pc))
      (code : seg = (l.program a).segment pc) (owner : seg.agent = a)
      (access : ∀ p, p ∈ seg.reads s.mem ∪ seg.writes s.mem →
        AccessibleAt l.symm a p ∧ ¬ InFlight s.trace p)
      (success : seg.run s.mem = some mem) :
      step l s (.agent a) { s with
        mem := mem
        history := s.history ++ [.segment a (seg.reads s.mem) (seg.writes s.mem)]
        pc := Function.update s.pc a (((l.program a).next pc s.mem).cursor) }
  | fire {a h t k final values} (atPC : s.pc a = some (.waiting h t k))
      (owned : ∀ x ∈ h :: t, x.actor.within a)
      (events : FireGroup l a s.toMachine (h :: t) final values) :
      step l s (.agent a) { final with pc := Function.update s.pc a (some (.ready (k values))) }
  | deliver {pre post o b old} (outstanding : s.pending = pre ++ o :: post)
      (bound : o.transfer.completion = some b)
      (counter : b.op = .add → s.count? l.initialCount b.counter = some old)
      (ordered : ∀ prior ∈ pre ++ post, ¬ FencedBefore s.toMachine prior o)
      (disjointSignal : ∀ p, b.counter = .word p → p ∉ o.transfer.dst)
      (access : (Event.complete o.transfer).AccessibleBy l.symm o.owner)
      (free : ∀ k p m, (k,p,m) ∈ (Event.complete o.transfer).accesses →
        ∀ other ∈ pre ++ post, p ∉ other.transfer.dst) :
      step l s (.delivery o.start) { s with
        mem := deliverMemory l.cells s.toMachine o b old
        pending := pre ++ post
        history := s.history ++ [.delivered o.owner o.transfer o.start] }

/-- S4.2/#48. Relational fold, including all finite prefixes. -/
inductive Run {P} (l : Launch P) : Config P → Schedule → Config P → Prop
  | nil (s) : Run l s [] s
  | cons {s t u c cs} : step l s c t → Run l t cs u → Run l s (c :: cs) u

/-- S4.9/#55. A return requires every continuation to finish; drain transfers
with a completion, leave W5 destinations in flight and unavailable to observation. -/
def Complete (s : Config P) : Prop :=
  (∀ a, s.pc a = none) ∧ ∀ o ∈ s.pending, o.transfer.completion = none

/-- A well-formed but unsatisfied wait blocks. All other absent transitions
for the current instruction are faults. In a group, inspect members in order
so a blocked member does not misclassify a later instruction. -/
def BlockedMember (l : Launch P) (s : Machine) (x : Emission) : Prop :=
  x.event.AccessibleBy l.symm x.actor ∧
  (∀ k p m, (k,p,m) ∈ x.event.accesses → ¬ InFlight s.trace p) ∧
  (PendingFence s x ∨ ∃ c cmp n m actual, x.data = .noValue ∧ x.event = .wait c cmp n m ∧
    s.count? l.initialCount c = some actual ∧ ¬ cmp.holds actual n)

def BlockedGroup (l : Launch P) (program : Agent) (s : Machine) (es : List Emission) : Prop :=
  ∃ pre x post mid vs, es = pre ++ x :: post ∧ FireGroup l program s pre mid vs ∧ BlockedMember l mid x

private theorem Fire.deterministic {l : Launch P} {s : Machine} {x : Emission}
    (f : Fire l s x m pending v) (g : Fire l s x m' pending' v') :
    m = m' ∧ pending = pending' ∧ v = v' := by
  cases f <;> cases g <;> try exact ⟨rfl,rfl,rfl⟩
  case wait.wait a c cmp n mode old read enabled other read' enabled' =>
    cases Option.some.inj (read.symm.trans read')
    exact ⟨rfl,rfl,rfl⟩
  case bump.bump a b old read other read' =>
    cases op : b.op with
    | add =>
      cases Option.some.inj ((read op).symm.trans (read' op))
      exact ⟨rfl,rfl,rfl⟩
    | set =>
      cases h : b.counter <;> simp [bumpMem,h,op,SignalOp.apply]
  case discardAdd.discardAdd a p n mode old read other read' =>
    cases Option.some.inj (read.symm.trans read')
    exact ⟨rfl,rfl,rfl⟩

/-- Firing the same emissions from the same machine fixes the entire resulting
machine and all values supplied to the continuation. -/
theorem FireGroup.deterministic {l : Launch P}
    (f : FireGroup l a s es m vals) (g : FireGroup l a s es m' vals') :
    m = m' ∧ vals = vals' := by
  induction f generalizing m' vals' with
  | nil => cases g; exact ⟨rfl,rfl⟩
  | cons _ _ _ fire rest ih =>
    cases g with
    | cons _ _ _ fire' rest' =>
      obtain ⟨rfl,rfl,rfl⟩ := fire.deterministic fire'
      obtain ⟨rfl,rfl⟩ := ih rest'
      exact ⟨rfl,rfl⟩

private theorem FireGroup.splitAt {l : Launch P} {a : Agent} {pre post : List Emission}
    (wholeGroup : FireGroup l a s (pre ++ post) m vals) :
    ∃ mid before after, FireGroup l a s pre mid before ∧ FireGroup l a mid post m after := by
  induction pre generalizing s vals with
  | nil => exact ⟨s, [], vals, .nil _,wholeGroup⟩
  | cons x xs ih =>
    cases wholeGroup with
    | cons acc free ordered fire rest =>
      obtain ⟨mid,before,after,front,back⟩ := ih rest
      exact ⟨mid,_,after,.cons acc free ordered fire front,back⟩

/-- A group blocked after a successful prefix cannot issue as the agent's next step. -/
theorem step_not_enabled_of_blocked {l : Launch P} {s : Config P} {a : Agent}
    (atPC : s.pc a = some (.waiting h t k)) (blocked : BlockedGroup l a s.toMachine (h :: t)) :
    ¬ ∃ u, step l s (.agent a) u := by
  rintro ⟨u,move⟩
  cases move with
  | segment ready _ _ _ _ => simp [atPC] at ready
  | fire waiting _ events =>
    rw [atPC] at waiting
    cases waiting
    obtain ⟨pre,x,post,mid,vs,eqn,front,_,_,why⟩ := blocked
    rw [eqn] at events
    obtain ⟨other,_,_,alt,tail⟩ := events.splitAt
    obtain ⟨rfl,_⟩ := front.deterministic alt
    cases tail with
    | cons _ _ ordered fire _ =>
      rcases why with fence | ⟨c,cmp,n,mode,actual,data,event,read,disabled⟩
      · exact ordered fence
      · cases x with | mk actor e v =>
          cases event; cases data
          cases fire with | wait _ _ _ _ _ old observed enabled =>
            cases Option.some.inj (read.symm.trans observed)
            exact disabled enabled

private theorem Run.from_idle {l : Launch P} {s f : Config P} {cs : Schedule}
    (run : Run l s cs f) (idle : ∀ b, s.pc b = none) (empty : s.pending = []) :
    cs = [] ∧ f = s := by
  cases run with
  | nil => exact ⟨rfl,rfl⟩
  | cons move _ =>
    cases move with
    | segment atPC _ _ _ _ => simp [idle] at atPC
    | fire atPC _ _ => simp [idle] at atPC
    | deliver outstanding _ _ _ _ _ _ => simp [empty] at outstanding

/-- If just one agent starts and its next instruction is finish, every complete run
is its one segment step. Conversely, an owned, accessible segment which succeeds
has a complete one-step run with precisely its returned memory. -/
theorem run_single_segment (l : Launch P) (a : Agent) (pc : P) (σ : DistState)
    (starts : l.start a = some pc) (alone : ∀ b, b ≠ a → l.start b = none)
    (finish : ∀ mem, (l.program a).next pc mem = .finish) :
    (∀ {cs f}, Run l (l.initial σ) cs f → Complete f →
      cs = [.agent a] ∧ ((l.program a).segment pc).run σ = some f.mem) ∧
    (∀ {m}, ((l.program a).segment pc).agent = a →
      (∀ p, p ∈ ((l.program a).segment pc).reads σ ∪ ((l.program a).segment pc).writes σ →
        AccessibleAt l.symm a p) → ((l.program a).segment pc).run σ = some m →
      ∃ f, Run l (l.initial σ) [.agent a] f ∧ Complete f ∧ f.mem = m) := by
  have idle : ∀ b, Function.update (l.initial σ).pc a (((l.program a).next pc σ).cursor) b = none := by
    intro b; by_cases eq : b = a
    · subst b; simp [finish,Next.cursor]
    · simp [Function.update_of_ne eq,Launch.initial,alone b eq]
  constructor
  · intro cs f run complete
    cases run with
    | nil => simpa [Launch.initial,starts] using complete.1 a
    | cons move tail =>
      cases move with
      | @segment b pos seg mem ready code owner access success =>
        change (l.start b).map Cursor.ready = some (.ready pos) at ready
        have eq : b = a := by by_contra diff; simp [alone b diff] at ready
        cases eq; rw [starts] at ready; cases ready; subst seg
        obtain ⟨rfl,rfl⟩ := tail.from_idle idle rfl
        exact ⟨rfl,success⟩
      | @fire b _ _ _ _ _ waiting _ _ =>
        cases init : l.start b <;> simp [Launch.initial,init] at waiting
      | deliver pending _ _ _ _ _ _ => simp [Launch.initial] at pending
  · intro m owner access success
    have ready : (l.initial σ).pc a = some (.ready pc) := by simp [Launch.initial,starts]
    have first := step.segment (l := l) (s := l.initial σ) ready rfl owner
      (fun p hp => ⟨access p hp, by simp [Launch.initial,Machine.trace,InFlight,Transfer.pending]⟩) success
    exact ⟨_,.cons first (.nil _),⟨idle,by simp [Launch.initial]⟩,rfl⟩

end VeriTile.Dist
