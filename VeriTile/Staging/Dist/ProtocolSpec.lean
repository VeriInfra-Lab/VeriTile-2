/- S6.1 unsigned protocol interfaces (#60). The four theorem bodies are
reserved for #61–#64. The judgments and execution relation are those of S4.1. -/
import VeriTile.Staging.Dist.JudgmentSpec
import VeriTile.Triton.Concurrency.Atomic

namespace VeriTile.Dist.Protocol
open VeriTile.Triton (MemCell)

/-- One local action. A copy exposes two scheduling points and carries the
actual value returned by the load into the subsequent store. -/
inductive Instr where
  | emit (event : Event) (data : AccessValue)
  | copy (src dst : Addr)

def store (p : Addr) (v : MemCell) : Instr := .emit (.access .store p .plain) (.store v)
def wait (c : Counter) (cmp : Cmp) (n : Nat) (m : Mode) : Instr :=
  .emit (.wait c cmp n m) .noValue
def signal (c : Counter) (op : SignalOp) (n : Nat) (m : Mode) : Instr :=
  .emit (.bump ⟨c, op, n, m⟩) .noValue

/-- Compile a participant's remaining actions at an arbitrary encoding of its
program counter. A singleton Fire.load returns exactly one present cell. -/
def nextAction (a : Agent) (encode : List Instr → P) : List Instr → Next P
  | [] => .finish
  | .emit e v :: rest => .emitGroup ⟨a, e, v⟩ [] (fun _ => encode rest)
  | .copy src dst :: rest =>
    .emitGroup ⟨a, .access .load src .plain, .noValue⟩ [] fun results =>
      match results with
      | [some v] => encode (store dst v :: rest)
      | _ => encode []

/-- Protocol action boundaries run an identity segment owned by the participant. -/
def idleSegment (a : Agent) : Segment := ⟨a, some, fun _ => ∅, fun _ => ∅⟩

/-- A copy's second instruction uses the value observed at its first, even
when another agent could write the source between these choices. -/
example (a : Agent) (src dst : Addr) (v : MemCell) :
    (match nextAction a id [.copy src dst] with
     | .emitGroup _ [] k => k [some v]
     | _ => []) = [store dst v] := rfl

/-- Local control flow, including every possible value returned by a load. -/
inductive Suffix (entry : List Instr) : List Instr → Prop where
  | start : Suffix entry entry
  | emit : Suffix entry (.emit e v :: rest) → Suffix entry rest
  | copy (v : MemCell) : Suffix entry (.copy src dst :: rest) →
      Suffix entry (store dst v :: rest)

/-- A local obligation, checked before choosing a schedule. It fixes active
participants, footprints, event actors, operands and continuations. It only
constrains local control states reachable from that participant’s entry. -/
def Realizes (l : Launch P) (body : Agent → Option (List Instr)) : Prop :=
  ∃ encode : Agent → List Instr → P,
    (∀ a, l.start a = (body a).map (encode a)) ∧
    ∀ a entry, body a = some entry → ∀ code, Suffix entry code →
      (l.program a).segment (encode a code) = idleSegment a ∧
      ∀ s, (l.program a).next (encode a code) s = nextAction a (encode a) code

/-- Each finite protocol body has a client launch, keeping the environment's
cell writer, roster, initial counters, and accessibility settings. -/
def launch (env : Launch P) (body : Agent → Option (List Instr)) : Launch (List Instr) where
  program a := ⟨fun _ => idleSegment a, fun code _ => nextAction a id code⟩
  start := body
  symm := env.symm
  reach := env.reach
  gridRank := env.gridRank
  abstractInitial := env.abstractInitial
  roster := env.roster
  cells := env.cells

theorem launch_realizes (env : Launch P) (body : Agent → Option (List Instr)) :
    Realizes (launch env body) body := by
  refine ⟨fun _ => id, ?_, fun _ _ _ _ _ => ⟨rfl, fun _ => rfl⟩⟩
  intro a
  cases h : body a <;> simp [launch, h]

/-- Race freedom on all prefixes, existence of a completing schedule, and the
specified memory observation for every completing schedule. -/
def Outcome (l : Launch P) (s : DistState) (post : DistState → Prop) : Prop :=
  DRF l s ∧ Completes l s ∧
    ∀ sched final, Run l (l.initial s) sched final → Complete final → post final.mem

namespace Examples

/-- The concrete S1.5 cell store used by the small clients below. -/
def writes : CellWrites where
  put := DistState.putCell
  read_same := DistState.cell_putCell
  read_other := fun s p q v h => s.cell_putCell_ne h v
  local_frame := by intro s p v a; cases a <;> rfl
  commute := fun s p q u v h => s.putCell_commute h u v

def exampleState : DistState where
  numRanks := 2
  cell _ := .of .nat 0
  context _ := ⟨fun _ _ _ => none, fun _ _ => 0, fun _ => 1⟩

def exampleEnv (w : CellWrites) : Launch Unit where
  program a := ⟨fun _ => idleSegment a, fun _ _ => .finish⟩
  start _ := none
  symm _ := true
  reach := .global
  gridRank _ := 1
  abstractInitial _ := 0
  roster _ := none
  cells := w

end Examples
open Examples

/-- Slots, synchronization words and permanent outputs are separately allocated. -/
inductive RingCell (stages items : Nat) where
  | slot (j : Fin stages)
  | full (j : Fin stages)
  | empty (j : Fin stages)
  | output (i : Fin items)
  deriving DecidableEq

/-- An item occupies slot `i % stages` during epoch `i / stages`. The two
candidate guards are operands of the generated code, so an incorrect source
lowering can be submitted to the same obligations. -/
structure RingQueue where
  stages : Nat
  stages_pos : 0 < stages
  items : Nat
  producer : Agent
  consumer : Agent
  different : producer ≠ consumer
  scope : Scope
  covers : scope.covers producer consumer
  address : RingCell stages items → Addr
  disjoint : Function.Injective address
  value : Fin items → MemCell
  phase : Nat → Nat
  waitEmpty : Fin items → Bool

namespace RingQueue

def slot (q : RingQueue) (i : Fin q.items) : Fin q.stages :=
  ⟨i.val % q.stages, Nat.mod_lt _ q.stages_pos⟩

def epoch (q : RingQueue) (i : Fin q.items) : Nat := i.val / q.stages

/-- Each reused slot waits for the previous consumer. A first-use wait is
permitted: an empty word initially carries the opposite of the first full bit. -/
def WaitsOnReuse (q : RingQueue) : Prop :=
  ∀ i : Fin q.items, q.stages ≤ i.val → q.waitEmpty i = true

def UsesEpochBit (q : RingQueue) : Prop :=
  ∀ i : Fin q.items, q.phase (q.epoch i) = q.epoch i % 2

def produce (q : RingQueue) (i : Fin q.items) : List Instr :=
  let j := q.slot i
  let bit := q.phase (q.epoch i)
  (if q.waitEmpty i then
    [wait (.word (q.address (.empty j))) .eq ((bit + 1) % 2) (.atomic q.scope .acquire)]
   else []) ++
    [store (q.address (.slot j)) (q.value i),
     signal (.word (q.address (.full j))) .set bit (.atomic q.scope .release)]

def consume (q : RingQueue) (i : Fin q.items) : List Instr :=
  let j := q.slot i
  let bit := q.phase (q.epoch i)
  [wait (.word (q.address (.full j))) .eq bit (.atomic q.scope .acquire),
   .copy (q.address (.slot j)) (q.address (.output i)),
   signal (.word (q.address (.empty j))) .set bit (.atomic q.scope .release)]

def body (q : RingQueue) (a : Agent) : Option (List Instr) :=
  if a = q.producer then some ((List.finRange q.items).flatMap q.produce)
  else if a = q.consumer then some ((List.finRange q.items).flatMap q.consume)
  else none

/-- Each item is fully produced then copied out and retired. The reference
uses the mathematical epoch bit and the input value independently of either
program, its candidate guards, or any interleaving. All flag writes are visible. -/
def sequential (q : RingQueue) (w : CellWrites) (s : DistState) : DistState :=
  (List.finRange q.items).foldl (fun mem i =>
    let j := q.slot i
    let v := q.value i
    let bit := MemCell.of .nat (q.epoch i % 2)
    let m₁ := w.put mem (q.address (.slot j)) v
    let m₂ := w.put m₁ (q.address (.full j)) bit
    let m₃ := w.put m₂ (q.address (.output i)) v
    w.put m₃ (q.address (.empty j)) bit) s

/-- Both parties can access the slot and both words. Only the consumer
touches an output, which may be private to it. -/
def AccessibleIn (q : RingQueue) (symm : VeriTile.Triton.RegionName → Bool) : Prop :=
  ∀ c, AccessibleAt symm q.consumer (q.address c) ∧
    match c with
    | .output _ => True
    | _ => AccessibleAt symm q.producer (q.address c)

/-- Before epoch zero the full bit is unready and the empty bit is ready. -/
def Initialized (q : RingQueue) (s : DistState) : Prop :=
  ∀ j, s.cell (q.address (.full j)) = .of .nat 1 ∧
    s.cell (q.address (.empty j)) = .of .nat 1

/-- UNSIGNED. S6.2/#61. The producer releases full after writing the slot;
the consumer releases empty after copying it. The second handshake orders the
previous read before the next overwrite, including across a parity wrap. -/
theorem ringQueue_correct (q : RingQueue) (l : Launch P) (s : DistState)
    (code : Realizes l q.body) (accessible : q.AccessibleIn l.symm)
    (init : q.Initialized s) (reuse : q.WaitsOnReuse) (bits : q.UsesEpochBit) :
    Outcome l s (fun final => final = q.sequential l.cells s) := by
  sorry

/-- Three slots and ten items reach the fourth use of slot zero.
Physical regions differ by role and each offset identifies its index. -/
def threeStage : RingQueue where
  stages := 3
  stages_pos := by decide
  items := 10
  producer := .thread ⟨0, [0]⟩ 0 0
  consumer := .thread ⟨0, [0]⟩ 0 1
  different := by decide
  scope := .cta
  covers := by decide
  address
    | .slot j => ⟨.shared ⟨0, [0]⟩, ⟨"slot"⟩, j.val⟩
    | .full j => ⟨.shared ⟨0, [0]⟩, ⟨"full"⟩, j.val⟩
    | .empty j => ⟨.shared ⟨0, [0]⟩, ⟨"empty"⟩, j.val⟩
    | .output i => ⟨.global 0, ⟨"out"⟩, i.val⟩
  disjoint := by
    intro x y h
    cases x <;> cases y <;> simp_all [Fin.ext_iff]
  value i := .of .nat (i.val + 10)
  phase e := e % 2
  waitEmpty i := decide (3 ≤ i.val)

theorem threeStage_reuse : threeStage.WaitsOnReuse := by
  intro i hi
  simpa [threeStage] using hi

theorem threeStage_bits : threeStage.UsesEpochBit := fun _ => rfl

theorem threeStage_accessible (symm : VeriTile.Triton.RegionName → Bool) :
    threeStage.AccessibleIn symm := by
  intro c
  cases c <;> simp [threeStage, AccessibleAt, Accessible, Agent.within, Agent.cta?, Agent.rankOf]

/-- Initialize only the two flag regions to one. Payload and output cells
start at zero. The client exercises three reuses of slot zero. -/
def threeStageInitial : DistState :=
  { exampleState with cell := fun p =>
      if p.region = ⟨"full"⟩ ∨ p.region = ⟨"empty"⟩ then .of .nat 1 else .of .nat 0 }

example :
    let l := launch (exampleEnv writes) threeStage.body
    Outcome l threeStageInitial (fun final => final = threeStage.sequential l.cells threeStageInitial) :=
  threeStage.ringQueue_correct _ _ (launch_realizes _ _) (threeStage_accessible _)
    (fun _ => ⟨rfl, rfl⟩) threeStage_reuse threeStage_bits

example :
    (threeStage.body threeStage.producer).map List.length = some 27 ∧
    (threeStage.body threeStage.consumer).map List.length = some 30 := by decide

example :
    let final := threeStage.sequential writes threeStageInitial
    (final.cell (threeStage.address (.output ⟨0, by decide⟩))).readAs .nat = some 10 ∧
    (final.cell (threeStage.address (.output ⟨9, by decide⟩))).readAs .nat = some 19 ∧
    (final.cell (threeStage.address (.slot ⟨0, by decide⟩))).readAs .nat = some 19 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Change only the producer's wait policy. Item three returns to slot zero,
where the missing acquire permits overwrite before consumption of item zero. -/
def missingEmpty : RingQueue := { threeStage with waitEmpty := fun _ => false }

theorem missingEmpty_rejected : ¬ missingEmpty.WaitsOnReuse := by
  intro h
  exact Bool.noConfusion (h ⟨3, by decide⟩ (by decide))

/-- With three stages the proposed modulus yields 2 at item six, whereas
the binary full/empty words require epoch two to wrap to zero. -/
def stageModulus : RingQueue := { threeStage with phase := fun e => e % threeStage.stages }

theorem stageModulus_rejected : ¬ stageModulus.UsesEpochBit := by
  intro h
  have bad := h (⟨6, by decide⟩ : Fin 10)
  norm_num [stageModulus, threeStage, epoch] at bad

example : (threeStage.produce ⟨3, by decide⟩).length = 3 ∧
    (missingEmpty.produce ⟨3, by decide⟩).length = 2 := by decide

private def observedFullBit : List Instr → Option Nat
  | .emit (.wait (.word _) .eq n (.atomic .cta .acquire)) .noValue :: _ => some n
  | _ => none

example : observedFullBit (threeStage.consume ⟨6, by decide⟩) = some 0 ∧
    observedFullBit (stageModulus.consume ⟨6, by decide⟩) = some 2 := by decide

/- The two actors can be poised at adjacent, unordered accesses. Replay the
concrete prefix with S4.1 steps. This checker covers just the singleton load,
store, SET and equality wait used by this ring. -/
namespace ParityRace
open Examples
private abbrev lch := launch (exampleEnv writes) stageModulus.body
private abbrev initial := lch.initial threeStageInitial

private structure Prefix where
  cfg : Config (List Instr)
  pending : cfg.pending = []
  clean : ∀ x ∈ cfg.trace, ∀ t, x.2 ≠ .initiate t

private theorem Prefix.free (s : Prefix) (p : Addr) : ¬ InFlight s.cfg.trace p := by
  rintro ⟨t, pos, _⟩
  have hz : s.cfg.trace.countP (fun x => decide (x.2 = .initiate t)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro x hx
    simp [s.clean x hx t]
  simp [Transfer.pending, hz] at pos

private def start : Prefix := ⟨initial, rfl, by simp [Machine.trace, initial, Launch.initial]⟩

private abbrev advance (s : Prefix) (a : Agent) :=
  Σ' t : Prefix, step lch s.cfg (.agent a) t.cfg

private def enter (s : Prefix) (a : Agent) (pc : List Instr)
    (h : s.cfg.pc a = some (.ready pc)) : advance s a := by
  let t : Config (List Instr) := { s.cfg with
    history := s.cfg.history ++ [.segment a ∅ ∅]
    pc := Function.update s.cfg.pc a ((nextAction a id pc).cursor) }
  refine ⟨⟨t, s.pending, ?_⟩, ?_⟩
  · simpa [t, Machine.trace, Occurrence.event?, List.filterMap_append] using s.clean
  · exact step.segment (seg := idleSegment a) h rfl rfl (by simp [idleSegment]) rfl

private def issue (s : Prefix) (a : Agent) (e : Event) (d : AccessValue)
    (k : List (Option MemCell) → List Instr) (mem : DistState) (v : Option MemCell)
    (cursor : s.cfg.pc a = some (.waiting ⟨a,e,d⟩ [] k))
    (owned : a.within a) (accessible : e.AccessibleBy lch.symm a)
    (plain : ∀ t, e ≠ .initiate t) (fire : Fire lch s.cfg.toMachine ⟨a,e,d⟩ mem s.cfg.pending v) :
    advance s a := by
  let m : Machine := ⟨mem, s.cfg.history ++ [.issued a ⟨a,e,d⟩], s.cfg.pending⟩
  let t : Config (List Instr) := { m with pc := Function.update s.cfg.pc a (some (.ready (k [v]))) }
  refine ⟨⟨t, s.pending, ?_⟩, ?_⟩
  · intro x hx
    simp [t, m, Machine.trace, List.filterMap_append, Occurrence.event?] at hx
    rcases hx with prev | rfl
    · exact s.clean x (List.mem_filterMap.mpr prev)
    · exact plain
  · apply step.fire (final := m) (values := [v]) cursor
    · simpa using owned
    · refine .cons accessible (fun _ p _ _ => s.free p) ?_ fire (.nil _)
      rintro ⟨prior, member, _⟩
      simp [s.pending] at member

/-- Consume the actual program cursor, including the real load continuation.
A bad guard, an inaccessible address, or an unexpected event rejects the replay. -/
private def tick (s : Prefix) (a : Agent) : Option (advance s a) := do
  match h : s.cfg.pc a with
  | some (.ready pc) => return enter s a pc h
  | some (.waiting ⟨actor,e,d⟩ [] k) =>
    if ha : actor = a then
      if ho : a.within a then
        if accessible : e.accesses.all (fun (_,p,_) => decide (AccessibleAt lch.symm a p)) then
          have access : e.AccessibleBy lch.symm a := fun k p m member =>
            of_decide_eq_true (List.all_eq_true.mp accessible (k,p,m) member)
          match e, d, h, access with
          | .access .store p .plain, .store v, h, acc =>
            return issue s a _ _ k _ _ (ha ▸ h) ho acc
              (by intro t bad; cases bad) (.store a p _ v)
          | .access .load p .plain, .noValue, h, acc =>
            return issue s a _ _ k _ _ (ha ▸ h) ho acc
              (by intro t bad; cases bad) (.load a p _)
          | .bump ⟨.word p,.set,n,m⟩, .noValue, h, acc =>
            return issue s a _ _ k _ _ (ha ▸ h) ho acc
              (by intro t bad; cases bad) (.bump a _ 0 (by intro bad; cases bad))
          | .wait (.word p) .eq n m, .noValue, h, acc =>
            if hn : (s.cfg.mem.cell p).readAs .nat = some n then
              return issue s a _ _ k _ _ (ha ▸ h) ho acc
                (by intro t bad; cases bad) (.wait a (.word p) .eq n m n hn rfl)
            else none
          | _, _, _, _ => none
        else none
      else none
    else none
  | _ => none

private def replay (s : Prefix) : (agents : List Agent) →
    Option (Σ' t : Prefix, Run lch s.cfg (agents.map Choice.agent) t.cfg)
  | [] => some ⟨s, .nil _⟩
  | a :: as => do
    let ⟨next, h⟩ ← tick s a
    let ⟨final, rest⟩ ← replay next as
    return ⟨final, .cons h rest⟩

private abbrev producer := stageModulus.producer
private abbrev consumer := stageModulus.consumer
private abbrev slot0 := stageModulus.address (.slot ⟨0, by decide⟩)
private abbrev overwrite : Occurrence :=
  .issued producer ⟨producer, .access .store slot0 .plain, .store (.of .nat 19)⟩
private abbrev readSlot : Occurrence :=
  .issued consumer ⟨consumer, .access .load slot0 .plain, .noValue⟩

/-- Finish items 0–5 in order. Produce 6–8. Before the consumer retires 6,
the bad wait for item 9 already sees the empty bit from item 3. Position both
actors at their memory events, then fire the overwrite and load consecutively.
A singleton emission takes two choices (enter, fire); a copy takes four. -/
private def choices : List Agent :=
  let p := fun n => List.replicate n producer
  let c := fun n => List.replicate n consumer
  (List.replicate 3 (p 4 ++ c 8)).flatten ++
    (List.replicate 3 (p 6 ++ c 8)).flatten ++ p 18 ++ p 2 ++ c 2 ++
    [producer, consumer, producer, consumer]

private theorem directIncreasing {h : History} {i j} (e : DirectHB lch h slot0 i j) : i < j :=
  by
  obtain ⟨_, _, _, _, lt, _⟩ := e
  exact lt

private theorem hbIncreasing {h : History} {i j} (e : HB lch h slot0 i j) : i < j := by
  induction e with
  | single e => exact directIncreasing e
  | tail _ e ih => exact lt_trans ih (directIncreasing e)

private theorem adjacentRace (h : History) (i : Nat)
    (left : h[i]? = some overwrite) (right : h[i+1]? = some readSlot) :
    DataRace lch h := by
  refine ⟨i,i+1,overwrite,readSlot,slot0,.store,.load,.plain,.plain,by omega,
    left,right,by simp [Occurrence.access, Event.accesses],
    by simp [Occurrence.access, Event.accesses],Or.inl rfl,by simp [Mode.AtomicFor],?_⟩
  intro chain
  cases chain with
  | tail earlier last => have := hbIncreasing earlier; have := directIncreasing last; omega
  | single e =>
    obtain ⟨_,_,hx,hy,_,po | barrier | delivery | sync | count⟩ := e
    all_goals rw [left] at hx; rw [right] at hy; cases hx; cases hy
    · obtain ⟨a,ha,hb⟩ := po
      simp [Occurrence.program?] at ha hb
      have := ha.trans hb.symm
      contradiction
    · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,obs,_⟩ := barrier
      simp [right, Occurrence.event?] at obs
    · obtain ⟨_,_,_,bad⟩ := delivery; cases bad
    · obtain ⟨a,b,_,_,ha,hb,_,_,pair⟩ := sync
      simp [Occurrence.event?] at ha hb
      subst a; subst b
      simp [SyncEdge, Event.releaseOf?, Event.acquireOf?, Mode.Pairs, AccessKind.writes,
        AccessKind.reads] at pair
    · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,obs,_⟩ := count
      simp [right, Occurrence.event?] at obs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A reachable data race in the ten-item program, independent of the
unsigned protocol theorem. Item 9 writes 19 before item 6 can collect 16. -/
theorem stageModulus_races :
    let l := launch (exampleEnv writes) stageModulus.body
    ∃ sched final, Run l (l.initial threeStageInitial) sched final ∧ DataRace l final.history := by
  dsimp only
  let result := replay start choices
  have ok : result.isSome := by decide +revert
  let witness := result.get ok
  refine ⟨_, witness.1.cfg, witness.2, adjacentRace _ 102 ?_ ?_⟩ <;> rfl

/- Advance the consumer through its resulting store. Item 6 actually
receives item 9's payload (19), whereas its sequential value is 16. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
example :
    ((replay start (choices ++ [consumer, consumer])).bind fun result =>
      (result.1.cfg.mem.cell (stageModulus.address (.output ⟨6, by decide⟩))).readAs .nat) =
      some 19 ∧ (stageModulus.value ⟨6, by decide⟩).readAs .nat = some 16 := ⟨rfl, rfl⟩

end ParityRace

end RingQueue

/-- The completion of a blocking or nonblocking put may publish the chunk and
raise its flag in the same delivery occurrence. The writer owns its staging cells. -/
inductive FlagPublication where
  | direct
  | put (source : Addr → Addr) (nbi : Bool)

structure OneShotFlag where
  writer : Agent
  readers : List Agent
  flag : Addr
  chunk : List (Addr × MemCell)
  receipt : Agent → Addr → Addr
  publish : FlagPublication
  release : Mode
  acquire : Mode

namespace OneShotFlag

def staged (f : OneShotFlag) : List (Addr × MemCell) :=
  match f.publish with
  | .direct => []
  | .put source _ => f.chunk.map fun (p,v) => (source p,v)

def receipts (f : OneShotFlag) (a : Agent) : List (Addr × MemCell) :=
  f.chunk.map fun (p,v) => (f.receipt a p,v)

/-- Sequential initialization of source cells (for put), publication of the
chunk and flag, and readback of each observed payload into private result cells. -/
def sequentialWrites (f : OneShotFlag) : List (Addr × MemCell) :=
  f.staged ++ f.chunk ++ [(f.flag, .of .nat 1)] ++ f.readers.flatMap f.receipts

def body (f : OneShotFlag) (a : Agent) : Option (List Instr) :=
  if a = f.writer then some (match f.publish with
    | .direct => f.chunk.map (fun (p,v) => store p v) ++ [signal (.word f.flag) .set 1 f.release]
    | .put _ nbi =>
      let transfer : Transfer := ⟨f.staged.map Prod.fst, f.chunk.map Prod.fst, nbi,
        some ⟨.word f.flag, .set, 1, f.release⟩⟩
      f.staged.map (fun (p,v) => store p v) ++ [.emit (.initiate transfer) .noValue])
  else if a ∈ f.readers then
    some (wait (.word f.flag) .eq 1 f.acquire :: f.chunk.map (fun (p,_) => .copy p (f.receipt a p)))
  else none

structure Valid (f : OneShotFlag) (l : Launch P) (s : DistState) : Prop where
  hasReaders : f.readers ≠ []
  oneRole : f.writer ∉ f.readers
  uniqueReaders : f.readers.Nodup
  hasPayload : f.chunk ≠ []
  separate : (f.sequentialWrites.map Prod.fst).Nodup
  initiallyClear : s.cell f.flag = .of .nat 0
  writerAccess : ∀ p ∈ f.flag :: (f.staged ++ f.chunk).map Prod.fst, AccessibleAt l.symm f.writer p
  readerAccess : ∀ a ∈ f.readers, ∀ p ∈ f.flag :: (f.chunk ++ f.receipts a).map Prod.fst,
    AccessibleAt l.symm a p
  visible : ∀ a ∈ f.readers, ∀ p ∈ f.chunk.map Prod.fst, Mode.Pairs l.reach p f.writer a f.release f.acquire

/-- UNSIGNED. S6.3/#62. Each reader observes the published chunk. The single flag
write or completion separates its producer's stores from the reader's copies. -/
theorem oneShotFlag_correct (f : OneShotFlag) (l : Launch P) (s : DistState)
    (valid : f.Valid l s) (program : Realizes l f.body) :
    Outcome l s (fun final => final =
      f.sequentialWrites.foldl (fun mem pv => l.cells.put mem pv.1 pv.2) s) := by
  sorry

end OneShotFlag

/-- In each generation, each participant publishes one owned cell, arrives,
waits for all participants, then copies a peer's cell to an owned result. Each
generation uses separate payload and result cells, so faster participants may
start the next generation before every reader finishes the previous one. -/
structure PhaseBarrier where
  members : List Agent
  phases : Nat
  counter : Counter
  peer : Agent → Agent
  payload : Nat → Agent → Addr
  receipt : Nat → Agent → Addr
  value : Nat → Agent → MemCell
  release : Mode
  acquire : Mode

namespace PhaseBarrier

def round (b : PhaseBarrier) (n : Nat) (a : Agent) : List Instr :=
  [store (b.payload n a) (b.value n a),
   signal b.counter .add 1 b.release,
   wait b.counter .ge ((n+1)*b.members.length) b.acquire,
   .copy (b.payload n (b.peer a)) (b.receipt n a)]

def body (b : PhaseBarrier) (a : Agent) : Option (List Instr) :=
  if a ∈ b.members then some ((List.range b.phases).flatMap (fun n => b.round n a)) else none

/-- Phase-major reference: all publishers write, then all readers copy. The
reference depends only on the inputs and peer map, independent of a schedule. -/
def sequentialWrites (b : PhaseBarrier) : List (Addr × MemCell) :=
  (List.range b.phases).flatMap fun n =>
    b.members.map (fun a => (b.payload n a, b.value n a)) ++
    b.members.map (fun a => (b.receipt n a, b.value n (b.peer a)))

structure Valid (b : PhaseBarrier) (l : Launch P) : Prop where
  hasMembers : b.members ≠ []
  uniqueMembers : b.members.Nodup
  hasPhases : 0 < b.phases
  barrierObject : match b.counter with
    | .phase c _ => ∀ a ∈ b.members, a.cta? = some c
    | .rendezvous _ => True
    | _ => False
  roster : l.roster b.counter = some b.members
  initiallyZero : l.initialCount b.counter = 0
  participatingPeer : ∀ a ∈ b.members, b.peer a ∈ b.members
  separate : (b.sequentialWrites.map Prod.fst).Nodup
  storage : ∀ n < b.phases, ∀ a ∈ b.members,
    AccessibleAt l.symm a (b.payload n a) ∧ AccessibleAt l.symm a (b.payload n (b.peer a)) ∧
      AccessibleAt l.symm a (b.receipt n a)
  visible : ∀ n < b.phases, ∀ a ∈ b.members,
    Mode.Pairs l.reach (b.payload n (b.peer a)) (b.peer a) a b.release b.acquire

/-- UNSIGNED. S6.4/#63. With the exact roster, the kth arrival of each member
precedes each kth successful wait. No post-barrier copy reads a future phase. -/
theorem phaseBarrier_correct (b : PhaseBarrier) (l : Launch P) (s : DistState)
    (valid : b.Valid l) (program : Realizes l b.body) :
    Outcome l s (fun final => final =
      b.sequentialWrites.foldl (fun mem pv => l.cells.put mem pv.1 pv.2) s) := by
  sorry

end PhaseBarrier

namespace Examples

private def syncCell (offset : Nat) : Addr := ⟨.global 1, "protocol", offset⟩

/-- The same two-word publication using direct CUDA stores or the completion
of an NBI NVSHMEM put from separate staging cells. -/
def flagExample (viaPut : Bool) : OneShotFlag where
  writer := .rank 0
  readers := [.rank 1]
  flag := syncCell 0
  chunk := [(syncCell 1, .of .nat 31), (syncCell 2, .of .nat 47)]
  receipt _ p := syncCell (p.offset + 2)
  publish := if viaPut then .put (fun p => ⟨.global 0, "staging", p.offset⟩) true else .direct
  release := if viaPut then .shmem .release else .atomic .sys .release
  acquire := if viaPut then .shmem .acquire else .atomic .sys .acquire

private abbrev flagLaunch (viaPut : Bool) := launch (exampleEnv writes) (flagExample viaPut).body

private theorem flagValid (viaPut : Bool) : (flagExample viaPut).Valid (flagLaunch viaPut) exampleState := by
  constructor
  · cases viaPut <;> decide
  · cases viaPut <;> decide
  · cases viaPut <;> decide
  · intro h; cases h
  · cases viaPut <;> decide
  · rfl
  · cases viaPut <;> decide
  · cases viaPut <;> decide
  · intro _ _ _ _
    cases viaPut
    · exact ⟨rfl, rfl, trivial, trivial⟩
    · exact ⟨rfl, rfl, Or.inl rfl⟩

example (viaPut : Bool) : Outcome (flagLaunch viaPut) exampleState (fun final => final =
    (flagExample viaPut).sequentialWrites.foldl (fun s pv => writes.put s pv.1 pv.2) exampleState) :=
  (flagExample viaPut).oneShotFlag_correct _ _ (flagValid viaPut) (launch_realizes _ _)

example (viaPut : Bool) : (((flagExample viaPut).sequentialWrites.foldl (fun s pv => writes.put s pv.1 pv.2)
    exampleState).cell (syncCell 4)).readAs .nat = some 47 := by cases viaPut <;> rfl

-- Inspect the generated operands and completion binding directly.
private def flagSend? : Instr → Option (Sum Bump Transfer)
  | .emit (.bump b) _ => some (.inl b)
  | .emit (.initiate t) _ => some (.inr t)
  | _ => none

example : (((flagExample false).body (.rank 0)).getD []).filterMap flagSend? =
    [.inl ⟨.word (syncCell 0), .set, 1, .atomic .sys .release⟩] := rfl

example : (((flagExample true).body (.rank 0)).getD []).filterMap flagSend? =
    [.inr ⟨[⟨.global 0, "staging", 1⟩, ⟨.global 0, "staging", 2⟩],
      [syncCell 1, syncCell 2], true, some ⟨.word (syncCell 0), .set, 1, .shmem .release⟩⟩] := rfl

/-- A GPU-scoped acquire on rank 1 cannot synchronize with the rank-0 writer. -/
example : ¬ Mode.Pairs .global (syncCell 1) (flagExample false).writer (.rank 1)
    (flagExample false).release (.atomic .gpu .acquire) := by
  intro h; exact Nat.noConfusion h.2.2.2

/-- Two ranks exchange values across two generations of the same rendezvous. -/
def phaseExample : PhaseBarrier where
  members := [.rank 0, .rank 1]
  phases := 2
  counter := .rendezvous 7
  peer a := if a = .rank 0 then .rank 1 else .rank 0
  payload n a := syncCell (4*n + a.rankOf)
  receipt n a := syncCell (4*n + 2 + a.rankOf)
  value n a := .of .nat (10*n + a.rankOf + 1)
  release := .atomic .sys .release
  acquire := .atomic .sys .acquire

private def phaseEnv : Launch Unit :=
  { exampleEnv writes with roster := fun c => if c = phaseExample.counter then some phaseExample.members else none }
private abbrev phaseLaunch := launch phaseEnv phaseExample.body

private theorem phaseValid : phaseExample.Valid phaseLaunch := by
  constructor
  · decide
  · decide
  · decide
  · trivial
  · rfl
  · rfl
  · decide
  · decide
  · intro n _ a _
    exact ⟨⟨trivial, Or.inr rfl⟩, ⟨trivial, Or.inr rfl⟩, ⟨trivial, Or.inr rfl⟩⟩
  · intro _ _ _ _; exact ⟨rfl, rfl, trivial, trivial⟩

example : Outcome phaseLaunch exampleState (fun final => final =
    phaseExample.sequentialWrites.foldl (fun s pv => writes.put s pv.1 pv.2) exampleState) :=
  phaseExample.phaseBarrier_correct _ _ phaseValid (launch_realizes _ _)

example : ((phaseExample.sequentialWrites.foldl (fun s pv => writes.put s pv.1 pv.2)
    exampleState).cell (syncCell 6)).readAs .nat = some 12 := rfl

private def phaseWait? : Instr → Option (Counter × Cmp × Nat × Mode)
  | .emit (.wait c cmp n m) _ => some (c,cmp,n,m)
  | _ => none

example : ((phaseExample.body (.rank 0)).getD []).filterMap phaseWait? =
    [(.rendezvous 7, .ge, 2, .atomic .sys .acquire),
     (.rendezvous 7, .ge, 4, .atomic .sys .acquire)] := rfl

-- Rank 1 skips its second generation. The two straight-line programs issue
-- only three arrivals, fewer than rank 0's final threshold of four.
private def skipsLast (a : Agent) : Option (List Instr) :=
  if a = .rank 1 then some (phaseExample.round 0 a) else phaseExample.body a

example : phaseExample.body (.rank 1) ≠ skipsLast (.rank 1) := by
  intro h
  have impossible : (some 8 : Option Nat) = some 4 := congrArg (Option.map List.length) h
  contradiction

example : ¬ Cmp.ge.holds
    ((phaseExample.members.flatMap fun a => (skipsLast a).getD []).countP (fun i =>
      match i with
      | .emit (.bump b) _ => b == ⟨.rendezvous 7, .add, 1, .atomic .sys .release⟩
      | _ => false)) (2 * phaseExample.members.length) := by
  change ¬ 4 ≤ 3
  decide

end Examples

/-- The finite roster fixes the reference order. Each member contributes its listed
exact-real increments in program order, to the same physical cell. -/
structure AtomicAccumulation where
  agents : List Agent
  unique : agents.Nodup
  target : Addr
  increments : Agent → List ℝ

namespace AtomicAccumulation

/-- Use the real payload accessor of the upstream atomic-add trace model.
The initial-state premise excludes its fallback for non-real or undefined cells. -/
noncomputable def add (x : ℝ) (old : VeriTile.Triton.MemCell) : VeriTile.Triton.MemCell :=
  .real (old.realPayload + x)

/-- Only system-scope atomic updates are emitted. The generated per-agent body
depends on the inputs alone, so returned old values never determine later work. -/
noncomputable def body (q : AtomicAccumulation) (a : Agent) : Option (List Instr) :=
  if a ∈ q.agents then
    some ((q.increments a).map fun x =>
      .emit (.access .update q.target (.atomic .sys .relaxed)) (.update (add x)))
  else none

/-- The independent reference visits the roster in the declared order and each
member's increments in list order. It starts from the cell's actual initial value. -/
noncomputable def total (q : AtomicAccumulation) (initial : ℝ) : ℝ :=
  (q.agents.flatMap q.increments).foldl (· + ·) initial

/-- The update in the distributed step contributes exactly the same real
operand as the upstream single-address atomic-add trace event. -/
theorem add_upstream (tid : VeriTile.Triton.ThreadId) (p : Addr) (initial x : ℝ) :
    (add x (.real initial)).realPayload =
      initial + VeriTile.Triton.Trace.atomicAddRealSum
        [VeriTile.Triton.Stmt.atomicTraceEvent tid p.region p.offset .real x]
        (p.region, p.offset) := by
  simp [add]

/-- Two indivisible real additions commute, including at the same address. -/
theorem add_swap (initial x y : ℝ) :
    add y (add x (.real initial)) = add x (add y (.real initial)) := by
  simp [add, add_right_comm]

/-- UNSIGNED. S6.5. Every complete schedule leaves the canonical sequential
sum in the target and preserves all other memory, local contexts and geometry. -/
theorem atomicAccumulation_correct {P : Type} (q : AtomicAccumulation) (l : Launch P) (s : DistState)
    (initial : ℝ) (typed : s.cell q.target = .real initial)
    (access : ∀ a ∈ q.agents, AccessibleAt l.symm a q.target)
    (writes : l.cells.put = DistState.putCell) (programs : Realizes l q.body) :
    Outcome l s (fun final => final = s.putCell q.target (.real (q.total initial))) := by
  sorry

/-- Two CTAs on one rank independently add 2 and 3 to a single global cell. -/
noncomputable def twoCTAs : AtomicAccumulation where
  agents := [.cta ⟨0, [0]⟩, .cta ⟨0, [1]⟩]
  unique := by decide
  target := ⟨.global 0, "sum", 0⟩
  increments := fun a => if a = .cta ⟨0, [0]⟩ then [2] else [3]

/-- Check the operation at the program boundary independently of the unsigned
theorem: its selected opcode, scope, order and the updater's actual result. -/
example :
    (match twoCTAs.body (.cta ⟨0, [0]⟩) with
     | some [.emit (.access .update p (.atomic .sys .relaxed)) (.update f)] =>
       p = twoCTAs.target ∧ f (.real 7) = .real 9
     | _ => False) := by
  change twoCTAs.target = twoCTAs.target ∧ add 2 (.real 7) = .real 9
  exact ⟨rfl, by norm_num [add]⟩

theorem twoCTAs_total : twoCTAs.total 0 = 5 := by
  norm_num [total, twoCTAs, List.flatMap, List.foldl]

theorem twoCTAs_access (symm : VeriTile.Triton.RegionName → Bool) :
    ∀ a ∈ twoCTAs.agents, AccessibleAt symm a twoCTAs.target := by
  intro a ha
  simp [twoCTAs] at ha
  rcases ha with rfl | rfl <;> simp [twoCTAs, AccessibleAt, Accessible, Agent.rankOf]

/-- All obligations of the two-CTA client, including its actual initial
real cell, program correspondences, cell writer and shared address, hold. -/
example :
    let s := exampleState.putCell twoCTAs.target (.real 0)
    let l := launch (exampleEnv writes) twoCTAs.body
    Outcome l s (fun final => final = s.putCell twoCTAs.target (.real 5)) := by
  dsimp only
  rw [← twoCTAs_total]
  exact twoCTAs.atomicAccumulation_correct _ _ 0 (DistState.cell_putCell ..)
    (twoCTAs_access _) rfl (launch_realizes ..)

/-- The lost-update interleaving reads the same initial cell twice, then writes
those two separately computed results in order. Its final cell differs from the
serial sum. These writes cannot be generated by the atomic body above. -/
example (s : DistState) (h : s.cell twoCTAs.target = .real 0) :
    let p := twoCTAs.target
    let firstRead := s.cell p
    let secondRead := s.cell p
    let afterFirst := s.putCell p (add 2 firstRead)
    (afterFirst.putCell p (add 3 secondRead)).cell p ≠ .real (twoCTAs.total 0) := by
  dsimp only
  rw [DistState.cell_putCell, h, twoCTAs_total]
  intro bad
  have impossible := congrArg MemCell.realPayload bad
  norm_num [add] at impossible

end AtomicAccumulation

/- S6.6/#65: the multimem collective awaits documented completion and
ordering semantics. Its obligations and statement remain open. -/

end VeriTile.Dist.Protocol
