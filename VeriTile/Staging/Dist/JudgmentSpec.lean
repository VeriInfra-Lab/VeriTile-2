/- S4.1 design draft (#47). The event vocabulary and the first part
of SegmentSpec are signed. VeriTile.Dist.Exec now contains the signed execution
layer, schedule fold and blocking predicates (#48).

Signed on 2026-11-25 (user decisions of 2026-11-24 and 2026-11-25, recorded on
#47; the agent recorded the signature on the user's delegation): C1
`step_comm` (the statement only; its proof is owed by #51), C2
`wait_enabled_mono` and `threshold_stays_enabled`, the bridge
`SyncEdge.hb_of_readsFrom` and the add-only counting edge `CountingEdge.hb`,
with the definitions under them. C3, `implementsAll_of_canonical`,
`DetRaceFree`, `UnorderedAtomicRace` and `Occurrence.discardedAddAt` stay
unsigned and are signed with #54.

Re-signed on 2026-11-26 (user decision E1 of 2026-11-26, recorded on #47;
the agent recorded the signature on the user's delegation): this round signs
the new statement of C2 `threshold_stays_enabled`, whose `CountMonotone` is
restricted to configurations reachable from `l.initial σ₀` (decision 一 (a) of
2026-11-25), and re-accepts the definitions `Fire.wait` and `Fire.bump` under
`step_comm` with fix (a): a phase, rendezvous or delivery counter returns no
count. C3 `detRaceFree_complete_eq_canonical` stays UNSIGNED, with `sorry`.
Everything else in this file is a candidate
statement to review, not a certificate. The five source/control comparisons are in
tests/lean/dist/JudgmentVariants.lean. -/
import VeriTile.Staging.Dist.SegmentSpec
import VeriTile.Dist.Exec
import VeriTile.Triton.Concurrent.EventProgramIO

namespace VeriTile.Dist
open VeriTile.Triton (MemCell)

abbrev History := List Occurrence

/-- Read-from on a synchronization counter. Require matching positions and
exclude an intervening write of that counter. Add-only thresholds use CountingEdge.
General release sequences across mixed writes and fence-mediated edges belong to #55. -/
def ReadsFrom (h : History) (i j : Nat) (c : Counter) : Prop :=
  i < j ∧ ∀ k x, i < k → k < j → h[k]? = some x →
    match c with
    | .word q => ∀ k m, x.access q k m → k.writes = false
    | _ => ∀ e, x.event? = some e → ∀ m, e.2.releaseOf? ≠ some (c,m)

/-- D8/A5/A9. The kth arrival of a participant is paired with a wait for
k times the roster size. Faster participants cannot substitute for a missing
participant merely by incrementing the shared counter again. -/
def RoundEdge (l : Launch P) (h : History) (p : Addr) (i j : Nat) : Prop :=
  ∃ c a b m m' members k,
    (match c with | .phase .. | .rendezvous .. => True | _ => False) ∧
    l.roster c = some members ∧ members.Nodup ∧ a ∈ members ∧ b ∈ members ∧
    l.initialCount c = 0 ∧ 0 < k ∧ i < j ∧
    (h[i]? >>= Occurrence.event?) = some (a,.bump ⟨c,.add,1,m⟩) ∧
    (h[j]? >>= Occurrence.event?) = some (b,.wait c .ge (k * members.length) m') ∧
    (∀ x ∈ h.take j, ∀ ae ∈ x.event?, ∀ bump ∈ ae.2.bump?, bump.counter = c →
      ae.1 ∈ members ∧ ae.2 = .bump ⟨c,.add,1,m⟩) ∧
    (let arrivals := fun (n : Nat) (who : Agent) => ((h.take n).filterMap Occurrence.event?).countP
      (fun ae => decide (ae.1 = who ∧ ae.2.bump? = some ⟨c,.add,1,m⟩))
     arrivals (i+1) a = k ∧ ∀ who ∈ members, k ≤ arrivals j who) ∧
    Mode.Pairs l.reach p a b m m'

/-- Ordinary stores and updates (including transfer payload stores) break an
add-only prefix even when the same occurrence also adds to its signal. -/
def Event.onlyAddsTo (c : Counter) : Event → Prop
  | .access k q _ => c = .word q → k.writes = false
  | .bump b => b.counter = c → b.op = .add ∧ b.mode ≠ .plain
  | .complete t => (∀ b ∈ t.completion, b.counter = c → b.op = .add ∧ b.mode ≠ .plain) ∧
      ∀ q ∈ t.dst, c ≠ .word q
  | _ => True

def Occurrence.onlyAddsTo (c : Counter) : Occurrence → Prop
  | .segment _ _ writes => ∀ q, c = .word q → q ∉ writes
  | .issued _ e => e.event.onlyAddsTo c
  | .delivered _ t _ => (Event.complete t).onlyAddsTo c

/-- UNSIGNED. S4.1 counting edge (#47). An executed ge wait observes every
earlier release add to its add-only counter that pairs at the observed cell.
Fire.wait records the wait only after its threshold holds. Event.bump? also
covers delivered completion signals. The entire prefix before the observation,
including writes preceding the release, must be add-only. -/
def CountingEdge (l : Launch P) (h : History) (p : Addr) (i j : Nat) : Prop :=
  ∃ a event b c amount m n m', i < j ∧
    (h[i]? >>= Occurrence.event?) = some (a,event) ∧
    event.bump? = some ⟨c,.add,amount,m⟩ ∧
    (h[j]? >>= Occurrence.event?) = some (b,.wait c .ge n m') ∧
    (∀ x ∈ h.take j, x.onlyAddsTo c) ∧ Mode.Pairs l.reach p a b m m'

def DirectHB (l : Launch P) (h : History) (p : Addr) (i j : Nat) : Prop :=
  ∃ x y, h[i]? = some x ∧ h[j]? = some y ∧ i < j ∧
    ((∃ a, x.program? = some a ∧ y.program? = some a) ∨
      RoundEdge l h p i j ∨
      (∃ a t, x.event? = some (a,.initiate t) ∧ y = .delivered a t i) ∨
      (∃ a b c m, x.event? = some a ∧ y.event? = some b ∧ a.2.releaseOf? = some (c,m) ∧
        ReadsFrom h i j c ∧ SyncEdge l.reach p a b) ∨ CountingEdge l h p i j)

/-- S4.3/#49. Scope visibility is indexed by the cell throughout the chain. -/
def HB (l : Launch P) (h : History) (p : Addr) := Relation.TransGen (DirectHB l h p)

/-- Signed (#47). S5.1/S1: the scope checker supplies a synchronization pair for the
observed cell `p`. At its two history positions, the acquire must read from
this release on the same synchronization counter. -/
theorem SyncEdge.hb_of_readsFrom {l : Launch P} {h : History} {p : Addr} {i j : Nat}
    {rel acq : Agent × Event} {c : Counter} {m : Mode}
    (edge : SyncEdge l.reach p rel acq)
    (atRel : (h[i]? >>= Occurrence.event?) = some rel)
    (atAcq : (h[j]? >>= Occurrence.event?) = some acq)
    (released : rel.2.releaseOf? = some (c,m)) (source : ReadsFrom h i j c) :
    HB l h p i j := by
  obtain ⟨x, hx, ex⟩ := Option.bind_eq_some_iff.mp atRel
  obtain ⟨y, hy, ey⟩ := Option.bind_eq_some_iff.mp atAcq
  exact .single ⟨x, y, hx, hy, source.1,
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rel, acq, c, m, ex, ey, released, source, edge⟩)))⟩

/-- Signed (#47). S4.1. The add-only counting edge is a direct HB edge. Its scope
(a satisfied `ge` wait on an add-only counter) is widened only by #55. -/
theorem CountingEdge.hb {l : Launch P} {h : History} {p : Addr} {i j : Nat}
    (edge : CountingEdge l h p i j) : HB l h p i j := by
  obtain ⟨_, _, _, _, _, _, _, _, lt, src, _, dst, _⟩ := id edge
  obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.mp src
  obtain ⟨y, hy, _⟩ := Option.bind_eq_some_iff.mp dst
  exact .single ⟨x,y,hx,hy,lt, Or.inr (Or.inr (Or.inr (Or.inr edge)))⟩

def DataRace (l : Launch P) (h : History) : Prop :=
  ∃ i j x y p k k' m m', i < j ∧ h[i]? = some x ∧ h[j]? = some y ∧
    x.access p k m ∧ y.access p k' m' ∧ (k.writes = true ∨ k'.writes = true) ∧
    ¬ Mode.AtomicFor x.owner y.owner m m' ∧ ¬ HB l h p i j

/-- S4.3/#49. Race safety includes unfinished paths. -/
def DRF (l : Launch P) (s : DistState) : Prop :=
  ∀ sched final, Run l (l.initial s) sched final → ¬ DataRace l final.history

/-- UNSIGNED. Signed with #54. An issued word-add can discard its old value explicitly. A delivery returns
no old signal value to a continuation, so its completion add also qualifies
at its signal word. The transfer's payload accesses are checked separately. -/
def Occurrence.discardedAddAt (x : Occurrence) (p : Addr) : Prop :=
  match x with
  | .issued _ e => ∃ n m, e.event = .bump ⟨.word p,.add,n,m⟩ ∧ e.data = .discardAddResult
  | .delivered _ t _ => ∃ n m, t.completion = some ⟨.word p,.add,n,m⟩
  | .segment .. => False

/-- UNSIGNED. Signed with #54. Unordered conflicting atomic accesses, except discarded adds. -/
def UnorderedAtomicRace (l : Launch P) (h : History) : Prop :=
  ∃ i j x y p k k' m m', i < j ∧ h[i]? = some x ∧ h[j]? = some y ∧
    x.access p k m ∧ y.access p k' m' ∧ (k.writes = true ∨ k'.writes = true) ∧
    Mode.AtomicFor x.owner y.owner m m' ∧ ¬ HB l h p i j ∧
    ¬ (x.discardedAddAt p ∧ y.discardedAddAt p)

/-- UNSIGNED. Signed with #54. Ordinary and deterministic atomic race freedom on all prefixes. -/
def DetRaceFree (l : Launch P) (s : DistState) : Prop :=
  DRF l s ∧ ∀ sched final, Run l (l.initial s) sched final → ¬ UnorderedAtomicRace l final.history

def Fault (l : Launch P) (s : Config P) : Prop :=
  ∃ a cursor, s.pc a = some cursor ∧ (¬ ∃ next, step l s (.agent a) next) ∧
    match cursor with
    | .ready _ => True
    | .waiting h t _ => ¬ ((∀ x ∈ h :: t, x.actor.within a) ∧ BlockedGroup l a s.toMachine (h :: t))

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

/-- A multi-event group is exactly one CAS observation and write to the
same word by the same actor. Singleton emissions are ordinary source cuts. -/
def CASGroup (h : Emission) (tail : List Emission) : Prop :=
  tail = [] ∨ ∃ a p expected next scope readOrder writeOrder,
    h = ⟨a,.wait (.word p) .eq expected (.atomic scope readOrder),.noValue⟩ ∧
    tail = [⟨a,.bump ⟨.word p,.set,next,.atomic scope writeOrder⟩,.noValue⟩] ∧
    readOrder.releases = false ∧ writeOrder.acquires = false

structure SoundLaunch (l : Launch P) : Prop where
  localNext : ∀ a, (l.program a).NextLocal
  footprints : ∀ a pc, ((l.program a).segment pc).FootprintSound
  pidLength : ∀ a c, (l.start a).isSome → a.cta? = some c → c.pid.length = l.gridRank c.rank
  groups : ∀ a pc s h t k, (l.program a).next pc s = .emitGroup h t k →
    CASGroup h t ∧ ∀ x ∈ h :: t, x.actor.within a
  /-- A source path can switch between a collective and a participant. It
  cannot manufacture program order between two different sibling lanes. -/
  nestedPath : ∀ s sched f, Run l (l.initial s) sched f →
    ∀ x ∈ f.history, ∀ y ∈ f.history, ∀ a, x.program? = some a → y.program? = some a →
      x.owner.within y.owner ∨ y.owner.within x.owner

  /-- One thread's explicit instructions belong to one source path. CTA
  collective instructions can still be shared by its participants. -/
  uniqueThreadPath : ∀ s sched f, Run l (l.initial s) sched f →
    ∀ x ∈ f.history, ∀ y ∈ f.history, ∀ c g t, x.owner = .thread c g t →
      y.owner = .thread c g t → ∀ a b, x.program? = some a → y.program? = some b → a = b

def Safe (l : Launch P) (s : DistState) : Prop :=
  SoundLaunch l ∧ DRF l s ∧ ∀ sched final, Run l (l.initial s) sched final → ¬ Fault l final

/-- S4.4/#50. A race is a failure even if another schedule completes. Deadlock
alone leaves the universal postcondition vacuous; Completes is separate. -/
def ImplementsAll (l : Launch P) (s : DistState) (spec : Config P → Prop) : Prop :=
  Safe l s ∧ ∀ sched final, Run l (l.initial s) sched final → Complete final → spec final

/-- Signed (#47), statement only; the proof is owed by #51. C1, S4.5/#51. Histories record the swapped order, so the
equality asserted is on memory and continuations. -/
theorem step_comm {l : Launch P} (sound : SoundLaunch l) {s final : Config P} {a b : Choice}
    (first : Run l s [a,b] final) (ra rb : Resources) (ha : Reserves l s a ra)
    (hb : Reserves l s b rb) (apart : Independent ra rb) :
    ∃ swapped, Run l s [b,a] swapped ∧ swapped.mem = final.mem ∧ swapped.pc = final.pc := sorry

/-- Signed (#47). C2, S4.6/#52. Only monotone threshold comparisons have this property;
a set that decreases the counter or equality with a threshold can disable a wait. -/
theorem wait_enabled_mono {init : Counter → Nat} {c : Counter} {n : Nat} {pre post : Trace}
    (prefixOf : pre <+: post) (monotone : c.SetsMonotone init post)
    (enabled : Cmp.ge.holds (c.value init pre) n) : Cmp.ge.holds (c.value init post) n :=
  Counter.ge_stable monotone prefixOf enabled

/-- Signed (#47, re-signed 2026-11-26, via threshold_stays_enabled). S4.6/#52. State-level C2 covers physical words as well as abstract
counters. Every step from a configuration reachable from `l.initial σ₀` that
can modify the counter must preserve its type and not decrease it. Equality
waits do not satisfy threshold stability. Unreachable configurations are
excluded: over all configurations no launch satisfies this (#47, 2026-11-25). -/
def CountMonotone (l : Launch P) (σ₀ : DistState) (c : Counter) : Prop :=
  ∀ {pre s t action n}, Run l (l.initial σ₀) pre s → step l s action t →
    s.count? l.initialCount c = some n → ∃ m ≥ n, t.count? l.initialCount c = some m

private theorem Run.snoc {l : Launch P} {s t u : Config P} {xs : Schedule} {c : Choice}
    (run : Run l s xs t) (last : step l t c u) : Run l s (xs ++ [c]) u := by
  induction run with
  | nil => exact .cons last (.nil _)
  | cons first _ ih => exact .cons first (ih last)

/-- C2 at state level, S4.6/#52: a threshold that holds at a reachable
configuration stays enabled along any run whose steps never decrease the
counter. Signed (#47), re-signed 2026-11-26 with the reachable `CountMonotone`. -/
theorem threshold_stays_enabled {l : Launch P} {σ₀ : DistState} {c : Counter} {s t : Config P}
    {pre sched n old} (mono : CountMonotone l σ₀ c) (reach : Run l (l.initial σ₀) pre s)
    (run : Run l s sched t) (seen : s.count? l.initialCount c = some old) (enabled : n ≤ old) :
    ∃ v ≥ n, t.count? l.initialCount c = some v := by
  induction run generalizing pre old with
  | nil => exact ⟨old,enabled,seen⟩
  | cons first _ ih =>
    obtain ⟨m, ge, found⟩ := mono reach first seen
    exact ih (reach.snoc first) found (enabled.trans ge)

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

/-- UNSIGNED. Signed with #54. C3 candidate, S4.7–8/#53/#54. No scope-consistency
premise (#47, 2026-11-25): DetRaceFree uses HB, whose synchronization edges
already check scope through Mode.Pairs, and `Fire` returns no count of a
non-word counter, so an unrecorded observation cannot reach memory.
S5.2/#57 owns the source-level synchronization obligations, outside this
theorem. S4.7 owes normalization. Still false as stated after the 2026-11-25
fix: two `acqRel` fetch-adds on one word whose results are stored are
`DetRaceFree` in either order (tests/lean/dist/FetchAddObservation.lean).
C1 will also need a simulation for suffixes, including reads-from and delivery
ticket renaming; equality of the raw event histories would be false. -/
theorem detRaceFree_complete_eq_canonical {l : Launch P} {s : DistState} {canonical sched : Schedule}
    {reference final : Config P} (sound : SoundLaunch l) (safe : DetRaceFree l s)
    (refRun : Run l (l.initial s) canonical reference)
    (refComplete : Complete reference) (actual : Run l (l.initial s) sched final)
    (complete : Complete final) : final.mem = reference.mem := sorry

/-- UNSIGNED. Signed with #54. For a memory specification, checking the canonical final
memory and establishing race/fault freedom suffices on the deterministic-race-free
fragment, through `detRaceFree_complete_eq_canonical`. -/
theorem implementsAll_of_canonical {l : Launch P} {s : DistState} {canonical : Schedule}
    {reference : Config P} (sound : SoundLaunch l) (safe : Safe l s) (det : DetRaceFree l s)
    (refRun : Run l (l.initial s) canonical reference)
    (done_ : Complete reference) (spec : DistState → Prop) (ok : spec reference.mem) :
    ImplementsAll l s (fun final => spec final.mem) := by
  refine ⟨safe, fun sched final actual complete => ?_⟩
  change spec final.mem
  rw [detRaceFree_complete_eq_canonical sound det refRun done_ actual complete]
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
