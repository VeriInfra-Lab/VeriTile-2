/- Unsigned S4.1 design draft (#47). The event vocabulary and the first part
of SegmentSpec are signed. This file contains candidate statements to review,
not certificates. The five source/control comparisons are in
tests/lean/dist/JudgmentVariants.lean. -/
import VeriTile.Staging.Dist.SegmentSpec
import VeriTile.Triton.Concurrent.EventProgramIO

namespace VeriTile.Dist
open VeriTile.Triton (MemCell)

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
  | event (owner : Agent) (e : Event)
  | delivered (owner : Agent) (t : Transfer) (start : Nat)

def Occurrence.owner : Occurrence → Agent
  | .segment a .. | .event a _ | .delivered a .. => a

def Occurrence.event? : Occurrence → Option (Agent × Event)
  | .segment .. => none
  | .event a e => some (a,e)
  | .delivered a t _ => some (a,.complete t)

def Occurrence.delivery : Occurrence → Bool
  | .delivered .. => true
  | _ => false

def Occurrence.access (p : Addr) : Occurrence → AccessKind → Mode → Prop
  | .segment _ r _, .load, .plain => p ∈ r
  | .segment _ _ w, .store, .plain => p ∈ w
  | .event _ e, k, m => (k,p,m) ∈ e.accesses
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
  initialCount : Counter → Nat
  /-- Participants of a documented collective, with a fresh counter id per
  generation. Supplied by the source lowering only for an actual barrier. -/
  roster : Counter → Option (List Agent)
  cells : CellWrites

/-- A word read by an access and by a wait is the same physical cell. A
non-word counter is the signed fold over the synchronization trace. -/
noncomputable def Machine.count? (s : Machine) (init : Counter → Nat) : Counter → Option Nat
  | .word p => (s.mem.cell p).readAs .nat
  | c => some (Counter.value init s.trace c)

private def bumpMem (w : CellWrites) (s : DistState) (b : Bump) (old : Nat) : DistState :=
  match b.counter with
  | .word p => w.put s p (.of .nat (b.op.apply old b.amount))
  | _ => s

/-- N5. Loads and updates return their old cell, waits the observed natural
counter, adding bumps the old count. Stores, fences, set bumps and initiations
return none. A completion takes no continuation. An access with missing or
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
        (some (.of .nat old))
  | bump (a b old) (read : b.op = .add → s.count? l.initialCount b.counter = some old) :
      Fire l s ⟨a,.bump b,.noValue⟩ (bumpMem l.cells s.mem b old) s.pending
        (if b.op = .add then some (.of .nat old) else none)
  | initiate (a t) (sizes : t.src.length = t.dst.length) :
      Fire l s ⟨a,.initiate t,.noValue⟩ s.mem
        (⟨a,t,s.history.length,if t.nbi then none else some (t.src.map s.mem.cell)⟩ :: s.pending) none

/-- D1/D7: a blocking put issued earlier by this caller to this PE must
be delivered before a subsequent NVSHMEM signal becomes observable if the
caller fenced between them. NBI, another PE and another caller are excluded. -/
def PendingFence (s : Machine) (x : Emission) : Prop :=
  ∃ old ∈ s.pending, ∃ i mode b p r,
    old.transfer.nbi = false ∧ old.owner = x.actor ∧ old.start < i ∧
    s.history[i]? = some (.event x.actor (.fence (.shmem mode))) ∧
    x.event = .bump b ∧ b.counter = .word p ∧ (∃ order, b.mode = .shmem order) ∧
    p.space = .global r ∧ ∃ dst ∈ old.transfer.dst, dst.space = .global r

/-- Entire nonempty group is one scheduler choice. Earlier events in it are
visible to its later events. Other programs cannot enter between them. -/
inductive FireGroup {P} (l : Launch P) : Machine → List Emission → Machine → List (Option MemCell) → Prop
  | nil (s) : FireGroup l s [] s []
  | cons {s x mem pending v xs final vs} (access : x.event.AccessibleBy l.symm x.actor)
      (available : ∀ k p m, (k,p,m) ∈ x.event.accesses → ¬ InFlight s.trace p)
      (ordered : ¬ PendingFence s x)
      (fire : Fire l s x mem pending v)
      (rest : FireGroup l ⟨mem,s.history ++ [.event x.actor x.event],pending⟩ xs final vs) :
      FireGroup l s (x :: xs) final (v :: vs)

/-- The phase split allows another agent or the delivery engine to run after
a segment and before its events. A blocked wait never repeats its segment. -/
inductive Cursor (P : Type) where
  | ready (pc : P)
  | waiting (head : Emission) (tail : List Emission) (cont : List (Option MemCell) → P)

def Next.cursor (a : Agent) : Next P → Option (Cursor P)
  | .finish => none
  | .emit e k => some (.waiting ⟨a,e,.noValue⟩ [] fun vs => k (vs.head?.join))
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
A different thread's put is not ordered by a CTA's or another thread's fence.
The event carries a destination list, so compare the actual destination ranks. -/
def FencedBefore (s : Machine) (x y : Outstanding) : Prop :=
  x.transfer.nbi = false ∧ y.transfer.nbi = false ∧ x.owner = y.owner ∧ (∃ i m, x.start < i ∧ i < y.start ∧
    s.history[i]? = some (.event x.owner (.fence (.shmem m)))) ∧
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
        pc := Function.update s.pc a (((l.program a).next pc s.mem).cursor a) }
  | fire {a h t k final values} (atPC : s.pc a = some (.waiting h t k))
      (owned : ∀ x ∈ h :: t, x.actor.within a)
      (events : FireGroup l s.toMachine (h :: t) final values) :
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

abbrev History := List Occurrence

/-- Read-from on a synchronization counter. Require matching positions and
exclude an intervening write of that counter. Additional release-sequence,
fence and phase edges need their documented conditions (#55). -/
def ReadsFrom (h : History) (i j : Nat) (c : Counter) : Prop :=
  i < j ∧ ∀ k x, i < k → k < j → h[k]? = some x →
    match c with
    | .word q => ∀ k m, x.access q k m → k.writes = false
    | _ => ∀ e, x.event? = some e → ∀ m, e.2.releaseOf? ≠ some (c,m)

/-- D8/A5/A9 collective edges. A participant sees all arrivals of its
phase, not just the last increment. Fresh counter ids, exact roster and
scope checks prevent manufacturing a barrier from an ordinary word wait. -/
def RoundEdge (l : Launch P) (h : History) (p : Addr) (i j : Nat) : Prop :=
  ∃ c a b m m' members,
    (match c with | .phase .. | .rendezvous .. => True | _ => False) ∧
    l.roster c = some members ∧ members.Nodup ∧ b ∈ members ∧ l.initialCount c = 0 ∧
    i < j ∧ h[i]? = some (.event a (.bump ⟨c,.add,1,m⟩)) ∧
    h[j]? = some (.event b (.wait c .ge members.length m')) ∧
    (∀ k < j, ∀ x ∈ h[k]?, ∀ ae ∈ x.event?, ∀ bump ∈ ae.2.bump?,
      bump.counter = c → ae.2 = .bump ⟨c,.add,1,m⟩) ∧
    ((h.take j).filterMap (fun x => match x with
      | .event actor (.bump bump) => if bump.counter = c then some actor else none
      | _ => none)).Perm members ∧ Mode.Pairs l.reach p a b m m'

def DirectHB (l : Launch P) (h : History) (p : Addr) (i j : Nat) : Prop :=
  ∃ x y, h[i]? = some x ∧ h[j]? = some y ∧ i < j ∧
    ((x.owner = y.owner ∧ x.delivery = false ∧ y.delivery = false) ∨
      RoundEdge l h p i j ∨
      (∃ a t, x = .event a (.initiate t) ∧ y = .delivered a t i) ∨
      ∃ a b c m, x.event? = some a ∧ y.event? = some b ∧ a.2.releaseOf? = some (c,m) ∧
        ReadsFrom h i j c ∧ SyncEdge l.reach p a b)

/-- S4.3/#49. Scope visibility is indexed by the cell throughout the chain. -/
def HB (l : Launch P) (h : History) (p : Addr) := Relation.TransGen (DirectHB l h p)

def DataRace (l : Launch P) (h : History) : Prop :=
  ∃ i j x y p k k' m m', i < j ∧ h[i]? = some x ∧ h[j]? = some y ∧
    x.access p k m ∧ y.access p k' m' ∧ (k.writes = true ∨ k'.writes = true) ∧
    ¬ Mode.AtomicFor x.owner y.owner m m' ∧ ¬ HB l h p i j

/-- S4.3/#49. Race safety includes unfinished paths. -/
def DRF (l : Launch P) (s : DistState) : Prop :=
  ∀ sched final, Run l (l.initial s) sched final → ¬ DataRace l final.history

/-- A well-formed but unsatisfied wait blocks. All other absent transitions
for the current instruction are faults. In a group, inspect members in order
so a blocked member does not misclassify a later instruction. -/
def BlockedMember (l : Launch P) (s : Machine) (x : Emission) : Prop :=
  x.event.AccessibleBy l.symm x.actor ∧
  (∀ k p m, (k,p,m) ∈ x.event.accesses → ¬ InFlight s.trace p) ∧
  (PendingFence s x ∨ ∃ c cmp n m actual, x.data = .noValue ∧ x.event = .wait c cmp n m ∧
    s.count? l.initialCount c = some actual ∧ ¬ cmp.holds actual n)

def BlockedGroup (l : Launch P) (s : Machine) (es : List Emission) : Prop :=
  ∃ pre x post mid vs, es = pre ++ x :: post ∧ FireGroup l s pre mid vs ∧ BlockedMember l mid x

def Fault (l : Launch P) (s : Config P) : Prop :=
  ∃ a cursor, s.pc a = some cursor ∧ (¬ ∃ next, step l s (.agent a) next) ∧
    match cursor with
    | .ready _ => True
    | .waiting h t _ => ¬ ((∀ x ∈ h :: t, x.actor.within a) ∧ BlockedGroup l s.toMachine (h :: t))

def Safe (l : Launch P) (s : DistState) : Prop :=
  DRF l s ∧ ∀ sched final, Run l (l.initial s) sched final → ¬ Fault l final

/-- S4.4/#50. A race is a failure even if another schedule completes. Deadlock
alone leaves the universal postcondition vacuous; Completes is separate. -/
def ImplementsAll (l : Launch P) (s : DistState) (spec : Config P → Prop) : Prop :=
  Safe l s ∧ ∀ sched final, Run l (l.initial s) sched final → Complete final → spec final

def Completes (l : Launch P) (s : DistState) : Prop :=
  ∃ sched final, Run l (l.initial s) sched final ∧ Complete final ∧ ¬ DataRace l final.history

/-- S4.5/#51. Reservation sets conservatively include reads/writes, accessed
counter objects and transfers. Events inside a group are never swapped. -/
structure Resources where
  agents : Set Agent
  reads : Set Addr
  writes : Set Addr
  counters : Set Counter
  transfers : Set Transfer

def Independent (x y : Resources) : Prop :=
  (∀ a ∈ x.agents, ∀ b ∈ y.agents, ¬ a.within b ∧ ¬ b.within a) ∧
  Disjoint x.writes (y.reads ∪ y.writes) ∧ Disjoint y.writes (x.reads ∪ x.writes) ∧
  Disjoint x.counters y.counters ∧ Disjoint x.transfers y.transfers

/-- S4.5/#51. Resources must bound actual segments and all pending actions of
both agents. Segment footprints alone cannot justify commuting two emissions. -/
def Reserves (l : Launch P) (s : Config P) (c : Choice) (r : Resources) : Prop :=
  match c with
  | .agent a => a ∈ r.agents ∧ match s.pc a with
    | none => False
    | some (.ready pc) =>
      let seg := (l.program a).segment pc
      seg.reads s.mem ⊆ r.reads ∧ seg.writes s.mem ⊆ r.writes
    | some (.waiting h t _) => ∀ x ∈ h :: t, x.actor ∈ r.agents ∧
      (∀ k p m, (k,p,m) ∈ x.event.accesses → (k.reads → p ∈ r.reads) ∧ (k.writes → p ∈ r.writes)) ∧
      (∀ b, x.event.bump? = some b → b.counter ∈ r.counters) ∧
      (∀ q cmp v m, x.event = .wait q cmp v m → q ∈ r.counters) ∧
      (∀ tr, x.event = .initiate tr → tr ∈ r.transfers ∧ ∀ p ∈ tr.dst, p ∈ r.writes)
  | .delivery _ => False -- S4.9 must also account for the identity of an outstanding delivery.

def SoundLaunch (l : Launch P) : Prop :=
  ∀ a, (l.program a).NextLocal ∧ ∀ pc, ((l.program a).segment pc).FootprintSound

/-- C1 candidate, S4.5/#51. Histories record the swapped order, so the
equality asserted is on memory and continuations. -/
theorem step_comm {l : Launch P} (sound : SoundLaunch l) {s final : Config P} {a b : Choice}
    (first : Run l s [a,b] final) (ra rb : Resources) (ha : Reserves l s a ra)
    (hb : Reserves l s b rb) (apart : Independent ra rb) :
    ∃ swapped, Run l s [b,a] swapped ∧ swapped.mem = final.mem ∧ swapped.pc = final.pc := sorry

/-- C2, S4.6/#52. Only monotone threshold comparisons have this property;
a set that decreases the counter or equality with a threshold can disable a wait. -/
theorem wait_enabled_mono {init : Counter → Nat} {c : Counter} {n : Nat} {pre post : Trace}
    (prefixOf : pre <+: post) (monotone : c.SetsMonotone init post)
    (enabled : Cmp.ge.holds (c.value init pre) n) : Cmp.ge.holds (c.value init post) n :=
  Counter.ge_stable monotone prefixOf enabled

/-- S4.6/#52. State-level C2 covers physical words as well as abstract
counters. Every step that can modify the counter must preserve its type and
not decrease it. Equality waits do not satisfy threshold stability. -/
def CountMonotone (l : Launch P) (c : Counter) : Prop :=
  ∀ {s t action n}, step l s action t → s.count? l.initialCount c = some n →
    ∃ m ≥ n, t.count? l.initialCount c = some m

theorem threshold_stays_enabled {l : Launch P} {c : Counter} {s t : Config P}
    {sched n old} (mono : CountMonotone l c) (run : Run l s sched t)
    (seen : s.count? l.initialCount c = some old) (enabled : n ≤ old) :
    ∃ v ≥ n, t.count? l.initialCount c = some v := by
  induction run generalizing old with
  | nil => exact ⟨old,enabled,seen⟩
  | cons first _ ih =>
    obtain ⟨m, ge, found⟩ := mono first seen
    exact ih found (enabled.trans ge)

/-- C3 obstruction. Both scoped atomic sets are race-free with respect to
each other, but swapping them changes the final counter. -/
theorem atomic_sets_differ (p : Addr) (a b : Agent) :
    let w := fun (n : Nat) => Event.bump ⟨.word p,.set,n,.atomic .sys .relaxed⟩
    ¬ Conflict (a,w 1) (b,w 2) ∧
    Counter.value (fun _ => 0) [(a,w 1),(b,w 2)] (.word p) ≠
    Counter.value (fun _ => 0) [(b,w 2),(a,w 1)] (.word p) := by
  dsimp only
  constructor
  · simp [Conflict, Event.accesses, Bump.accesses, SignalOp.kind, Mode.AtomicFor, Scope.covers]
  · simp [Counter.value, Event.bump?, SignalOp.apply]

/-- The same obstruction at the data-store interface: both orders can
store, yet observing the common address distinguishes their final memories. -/
theorem atomic_set_memories_differ (w : CellWrites) (s : DistState) (p : Addr) :
    w.put (w.put s p (.of .nat 1)) p (.of .nat 2) ≠
    w.put (w.put s p (.of .nat 2)) p (.of .nat 1) := by
  intro h
  have h' := congrArg (fun σ : DistState => (σ.cell p).readAs .nat) h
  simp [w.read_same] at h'

/-- S4.7/#53. One local normalization move is an adjacent swap whose actual
states enable the two orders with the same continuation and observable store.
S4.7 owes a kernel/protocol invariant guaranteeing such a normalization. -/
inductive Swap (l : Launch P) (start : Config P) : Schedule → Schedule → Prop
  | adjacent {pre a b post s} (prefixRun : Run l start pre s) (ra rb : Resources)
      (ha : Reserves l s a ra) (hb : Reserves l s b rb) (ind : Independent ra rb) :
      Swap l start (pre ++ a :: b :: post) (pre ++ b :: a :: post)

/-- Candidate prerequisite for C3. Selecting the canonical schedule is only
meaningful for a complete reference run; a deterministic tie-break need not
find one. The atomic-sets example rules out deriving this solely from DRF. -/
def NormalizesTo (l : Launch P) (s : DistState) (canonical : Schedule) : Prop :=
  ∀ sched final, Run l (l.initial s) sched final → Complete final →
    Relation.ReflTransGen (Swap l (l.initial s)) sched canonical

/-- S4.7/#53. Choose a complete reference schedule of least source-supplied
rank (e.g. shortlex over the finite launch). The protocol must supply a
tie-free ranking if it needs a unique representative. -/
noncomputable def canonicalSchedule (l : Launch P) (s : DistState) (live : Completes l s)
    (rank : Schedule → Nat) : Schedule := by
  classical
  let feasible := fun n => ∃ sch f, rank sch = n ∧ Run l (l.initial s) sch f ∧ Complete f
  have h : ∃ n, feasible n := by
    obtain ⟨sch,f,run,done_,_⟩ := live
    exact ⟨rank sch,sch,f,rfl,run,done_⟩
  exact Classical.choose (Nat.find_spec h)

/-- S4.7/#53. A protocol supplies a decreasing out-of-order pair on each
noncanonical complete schedule, preserving completion. Its proof is a real
order-independence obligation; DRF does not imply it. -/
theorem normalize_of_decreasing_swap {l : Launch P} {s : DistState} {canonical : Schedule}
    (rank : Schedule → Nat)
    (decrease : ∀ sch f, Run l (l.initial s) sch f → Complete f → sch ≠ canonical →
      ∃ next g, Swap l (l.initial s) sch next ∧ rank next < rank sch ∧
        Run l (l.initial s) next g ∧ Complete g) : NormalizesTo l s canonical := by
  intro sch f run done_
  induction n : rank sch using Nat.strong_induction_on generalizing sch f with
  | h n ih =>
    by_cases eq : sch = canonical
    · subst sch; exact .refl
    · obtain ⟨next,g,swap,lt,reaches,complete⟩ := decrease sch f run done_ eq
      exact (Relation.ReflTransGen.single swap).trans
        (ih (rank next) (by omega) next g reaches complete rfl)

/-- Semantic obligation for S5.2/#57: every edge the source relies on
at the indicated location is an actual visibility edge on each reachable run. -/
def ScopeConsistentOn (l : Launch P) (s : DistState)
    (needs : History → Addr → Nat → Nat → Prop) : Prop :=
  ∀ sched final, Run l (l.initial s) sched final →
    ∀ p i j, needs final.history p i j → HB l final.history p i j

/-- C3 candidate, S4.7–8/#53/#54. The normalizing restriction is unsigned.
C1 will also need a simulation for suffixes, including reads-from and delivery
ticket renaming; equality of the raw event histories would be false. -/
theorem drf_scopeConsistent_complete_eq_canonical {l : Launch P} {s : DistState} {canonical sched : Schedule}
    {reference final : Config P} (sound : SoundLaunch l) (safe : DRF l s)
    (needs : History → Addr → Nat → Nat → Prop) (scopes : ScopeConsistentOn l s needs)
    (normal : NormalizesTo l s canonical) (refRun : Run l (l.initial s) canonical reference)
    (refComplete : Complete reference) (actual : Run l (l.initial s) sched final)
    (complete : Complete final) : final.mem = reference.mem := sorry

/-- S4.8/#54. For a memory specification, checking the canonical final
memory and establishing race/fault freedom suffices on the normalizing fragment. -/
theorem implementsAll_of_canonical {l : Launch P} {s : DistState} {canonical : Schedule}
    {reference : Config P} (sound : SoundLaunch l) (safe : Safe l s)
    (needs : History → Addr → Nat → Nat → Prop) (scopes : ScopeConsistentOn l s needs)
    (normal : NormalizesTo l s canonical) (refRun : Run l (l.initial s) canonical reference)
    (done_ : Complete reference) (spec : DistState → Prop) (ok : spec reference.mem) :
    ImplementsAll l s (fun final => spec final.mem) := by
  refine ⟨safe, fun sched final actual complete => ?_⟩
  change spec final.mem
  rw [drf_scopeConsistent_complete_eq_canonical sound safe.1 needs scopes normal refRun done_ actual complete]
  exact ok

open VeriTile.Triton.Concurrent (EventProgramIO Backend)

/-- S4.4/#50. The adapter proves source decoding, execution/trace refinement,
and observation/frame correspondence. Safety belongs to the same run that
supplies the outputs, as required by upstream ImplementsOn. -/
theorem implementsAll_completes_implementsOn
    {S I O V P : Type} (io : EventProgramIO S I O V) (backend : Backend V)
    (domain : io.Inputs → Prop) (formula : io.Inputs → io.Outputs)
    (launch : io.Inputs → Launch P)
    (embed : VeriTile.Triton.Concurrent.State V → DistState)
    (project : Config P → VeriTile.Triton.Concurrent.State V)
    (events : Config P → List VeriTile.Triton.Concurrent.Event)
    (implements : ∀ v, domain v → ∀ initial, io.InputBinding v initial →
      ImplementsAll (launch v) (embed initial) (fun f =>
        (∀ bounds, io.InBounds bounds → VeriTile.Triton.Concurrent.TapeSafe bounds (events f)) ∧
        io.OutputBinding (formula v) (project f) ∧ io.Frame initial (project f)))
    (live : ∀ v, domain v → ∀ initial, io.InputBinding v initial → Completes (launch v) (embed initial))
    (refines : ∀ v, domain v → ∀ initial, io.InputBinding v initial →
      ∀ sched f, Run (launch v) ((launch v).initial (embed initial)) sched f → Complete f →
        ∃ pg, io.decoded = some pg ∧ pg.Runs backend initial (events f) (project f)) :
    io.ImplementsOn backend domain formula := by
  intro v hv initial binding
  obtain ⟨sched, f, run, done_, _⟩ := live v hv initial binding
  obtain ⟨pg, decoded, simulation⟩ := refines v hv initial binding sched f run done_
  exact ⟨pg, decoded, events f, project f, simulation, (implements v hv initial binding).2 sched f run done_⟩

end VeriTile.Dist
