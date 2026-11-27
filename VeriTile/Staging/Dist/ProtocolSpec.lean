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

/-- Realizes checks only the encoded source cursors. A fresh, unreachable
cursor can emit an event for a different rank and invalidate SoundLaunch.groups
without changing any protocol action or environmental obligation. Thus the
four protocol results need launch soundness as an input to establish Safe. -/
theorem realizes_without_sound (env : Launch (Option (List Instr))) (body : Agent → Option (List Instr))
    (s : DistState) : ∃ l : Launch (Option (List Instr)), Realizes l body ∧ ¬ SoundLaunch l := by
  let foreign : Emission := ⟨.rank 1, .fence .plain, .noValue⟩
  let l : Launch (Option (List Instr)) := { env with
    start := fun a => (body a).map some
    program := fun a => ⟨fun _ => idleSegment a, fun pc _ => match pc with
      | some code => nextAction a some code
      | none => .emitGroup foreign [] (fun _ => none)⟩ }
  refine ⟨l, ⟨fun _ => some, fun _ => rfl, fun _ _ _ _ _ => ⟨rfl, fun _ => rfl⟩⟩, ?_⟩
  intro sound
  have owner := (sound.groups (.rank 0) none s foreign [] (fun _ => none) rfl).2 foreign (by simp)
  exact (by decide : ¬ (Agent.rank 1).within (.rank 0)) owner

private theorem withinSelf (a : Agent) : a.within a := by
  cases a <;> simp [Agent.within, Agent.cta?, Agent.rankOf]

private theorem idle_sound (a : Agent) : (idleSegment a).FootprintSound := by
  constructor
  · intro s s' h p _
    cases h
    rfl
  · intro s s' h
    cases h
    exact ⟨⟨s.view a, (s.setView_view a).symm⟩, fun _ _ _ => rfl⟩
  · intro s t _ localEq
    refine ⟨rfl, rfl, ?_⟩
    intro u h
    cases h
    exact ⟨t, rfl, fun _ hp => False.elim hp, localEq⟩

private def LocalCursors (s : Config (List Instr)) : Prop :=
  ∀ a h t k, s.pc a = some (.waiting h t k) → h.actor = a ∧ t = []

private def LocalHistory (s : Machine) : Prop :=
  ∀ x ∈ s.history, ∀ a, x.program? = some a → x.owner = a

private theorem next_singleton (a : Agent) (pc : List Instr) (h : Emission) (t : List Emission)
    (k : List (Option MemCell) → List Instr)
    (eq : nextAction a id pc = .emitGroup h t k) : h.actor = a ∧ t = [] := by
  cases pc with
  | nil => cases eq
  | cons i rest => cases i <;> cases eq <;> exact ⟨rfl, rfl⟩

private theorem step_local {env : Launch P} {body} {s t : Config (List Instr)}
    (progress : step (launch env body) s choice t)
    (pcs : LocalCursors s) (hist : LocalHistory s.toMachine) :
    LocalCursors t ∧ LocalHistory t.toMachine := by
  cases progress with
  | @segment a pc seg mem atPC code owner access success =>
    constructor
    · intro b h es k cursor
      by_cases eq : b = a
      · subst b
        simp only [Function.update_self] at cursor
        change (nextAction a id pc).cursor = some (.waiting h es k) at cursor
        cases hn : nextAction a id pc with
        | finish => simp [hn, Next.cursor] at cursor
        | emitGroup head tail cont =>
          simp [hn, Next.cursor] at cursor
          obtain ⟨rfl, rfl, rfl⟩ := cursor
          exact next_singleton _ _ _ _ _ hn
      · exact pcs b h es k (by simpa [Function.update, eq] using cursor)
    · intro x hx b hb
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hist x hx b hb
      · exact Option.some.inj hb
  | @fire a h es k final vs atPC owned events =>
    obtain ⟨actor, rfl⟩ := pcs _ _ _ _ atPC
    cases events with
    | cons access free ordered fire rest =>
      cases rest
      constructor
      · intro b head tail cont cursor
        by_cases eq : b = a
        · subst b
          simp [Function.update] at cursor
        · exact pcs b head tail cont (by simpa [Function.update, eq] using cursor)
      · intro x hx b hb
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hist x hx b hb
        · exact actor.trans (Option.some.inj hb)
  | deliver =>
    refine ⟨pcs, ?_⟩
    intro x hx b hb
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hist x hx b hb
    · cases hb

/-- The compiler emits singleton groups owned by their program. Its only
environmental geometry requirement is the dimension of an active CTA's pid. -/
theorem launch_sound (env : Launch P) (body : Agent → Option (List Instr))
    (dims : ∀ a c, (body a).isSome → a.cta? = some c → c.pid.length = env.gridRank c.rank) :
    SoundLaunch (launch env body) := by
  have owns : ∀ {s cs f}, Run (launch env body) ((launch env body).initial s) cs f →
      LocalHistory f.toMachine := by
    intro s cs f run
    have preserve : ∀ {x cs z}, Run (launch env body) x cs z →
        LocalCursors x → LocalHistory x.toMachine → LocalHistory z.toMachine := by
      intro x cs z h
      induction h with
      | nil => exact fun _ h => h
      | cons step _ ih =>
        intro pcs hist
        obtain ⟨pcs', hist'⟩ := step_local step pcs hist
        exact ih pcs' hist'
    apply preserve run
    · intro a h t k eq
      change (body a).map Cursor.ready = some (.waiting h t k) at eq
      cases hbody : body a <;> simp [hbody] at eq
    · intro _ hx
      cases hx
  constructor
  · exact fun _ _ _ _ _ _ => rfl
  · exact fun a _ => idle_sound a
  · exact dims
  · intro a pc _ h es k hn
    obtain ⟨actor, rfl⟩ := next_singleton _ _ _ _ _ hn
    exact ⟨Or.inl rfl, by simpa [actor] using withinSelf a⟩
  · intro _ _ _ run x hx y hy a h₁ h₂
    rw [owns run x hx a h₁, owns run y hy a h₂]
    exact Or.inl (withinSelf a)
  · intro _ _ _ run x hx y hy c g t tx ty a b px py
    exact (owns run x hx a px).symm.trans (tx.trans (ty.symm.trans (owns run y hy b py)))

/-- A source step may be silent or expand to several protocol steps. The
relation and completed memory are the only observations required here.
This statement does not require preservation of individual events, physical
word addresses, enabled steps or faults. -/
structure Projection (source : Launch P) (target : Launch Q) where
  related : Config P → Config Q → Prop
  entry : ∀ s, related (source.initial s) (target.initial s)
  simulate : ∀ {s t u choice}, related s t → step source s choice u →
    ∃ choices v, Run target t choices v ∧ related u v
  observe : ∀ {s t}, related s t → Complete s → Complete t ∧ s.mem = t.mem

private theorem appendRun {l : Launch P} (h : Run l s xs t) (k : Run l t ys u) :
    Run l s (xs ++ ys) u := by
  induction h with
  | nil => exact k
  | cons first _ ih => exact .cons first (ih k)

/-- Transport a completed execution's memory observation across a projection.
Progress and fault freedom require separate reflection obligations. -/
theorem Projection.completed {source : Launch P} {target : Launch Q}
    (p : Projection source target) (run : Run source (source.initial s) choices f)
    (done : Complete f) :
    ∃ schedule g, Run target (target.initial s) schedule g ∧ Complete g ∧ f.mem = g.mem := by
  suffices lift : ∀ {x y cs z}, Run source x cs z → p.related x y →
      ∃ ds w, Run target y ds w ∧ p.related z w by
    obtain ⟨ds, w, hw, rel⟩ := lift run (p.entry s)
    exact ⟨ds, w, hw, p.observe rel done⟩
  intro x y cs z h
  induction h generalizing y with
  | nil => exact fun rel => ⟨[], y, .nil _, rel⟩
  | cons first _ ih =>
    intro rel
    obtain ⟨as, mid, ha, hm⟩ := p.simulate rel first
    obtain ⟨bs, dest, hb, hd⟩ := ih hm
    exact ⟨as ++ bs, dest, appendRun ha hb, hd⟩

/-- A sound launch, race and fault freedom on all prefixes, existence of a
completing schedule, and the specified memory observation on every completion. -/
def Outcome (l : Launch P) (s : DistState) (post : DistState → Prop) : Prop :=
  ImplementsAll l s (fun final => post final.mem) ∧ Completes l s

/-- The three safety obligations established by every protocol outcome. -/
theorem Outcome.safety (h : Outcome l s post) :
    SoundLaunch l ∧ DRF l s ∧ ∀ sched final, Run l (l.initial s) sched final → ¬ Fault l final :=
  h.1.1

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

/-- S6.2/#61 covers rings with two physical memory words per slot. TileLang
mbarrier / T.ws rings have a separate proof obligation. The head/tail index
queues K25, K26 and K28 belong to the DeepEP route (#179).
Slots, synchronization words and permanent outputs are separately allocated. -/
inductive RingCell (stages items width : Nat) where
  | slot (j : Fin stages) (cell : Fin width)
  | full (j : Fin stages)
  | empty (j : Fin stages)
  | output (i : Fin items) (cell : Fin width)
  deriving DecidableEq

/-- An item occupies slot `i % stages` during epoch `i / stages`. The two
candidate guards are operands of the generated code, so an incorrect source
lowering can be submitted to the same obligations. -/
structure RingQueue where
  stages : Nat
  stages_pos : 0 < stages
  items : Nat
  width : Nat
  producer : Agent
  consumer : Agent
  different : producer ≠ consumer
  scope : Scope
  covers : scope.covers producer consumer
  address : RingCell stages items width → Addr
  disjoint : Function.Injective address
  value : Fin items → Fin width → MemCell
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
    (List.finRange q.width).map (fun k => store (q.address (.slot j k)) (q.value i k)) ++
    [signal (.word (q.address (.full j))) .set bit (.atomic q.scope .release)]

def consume (q : RingQueue) (i : Fin q.items) : List Instr :=
  let j := q.slot i
  let bit := q.phase (q.epoch i)
  [wait (.word (q.address (.full j))) .eq bit (.atomic q.scope .acquire)] ++
    (List.finRange q.width).map (fun k => .copy (q.address (.slot j k)) (q.address (.output i k))) ++
    [signal (.word (q.address (.empty j))) .set bit (.atomic q.scope .release)]

/-- Synchronization addresses visible to a direct projection. Payload reads
and writes may be hidden without changing the aliasing of the signal words. -/
def wordAddress : Instr → Option Addr
  | .emit (.wait (.word p) ..) _ | .emit (.bump ⟨.word p, _, _, _⟩) _ => some p
  | _ => none

/-- Consumer at T01:124–146 of the pinned 01-distributed-notify-wait.py.
The wait and notify name the same local signal pointer plus queue_offset.
This records the synchronization slice; the payload copy and fence are silent
for this observation. The wait may use gpu or sys; the intra-node SET is a
system-scope release under the registered A2 reading of `dl.notify`
(PrimitiveSources.md §7). Only addresses are used in the negative theorem. -/
def tutorialConsumerWords (word : Addr) (generation : Nat) (scope : Scope) : List Instr :=
  [wait (.word word) .eq (2 * generation + 1) (.atomic scope .acquire),
   signal (.word word) .set (2 * generation + 2) (.atomic .sys .release)]

theorem consumer_word_addresses (q : RingQueue) (i : Fin q.items) :
    (q.consume i).filterMap wordAddress =
      [q.address (.full (q.slot i)), q.address (.empty (q.slot i))] := by
  simp [consume, wait, signal, wordAddress, List.filterMap_map]

/-- No single-valued renaming of tutorial 01's physical word can match the
two-word consumer, even if all non-word operations and both numeric payloads
are erased. This also applies to the sys-scope variant. The theorem
concerns only direct renaming; it makes no claim about other simulations. -/
theorem tutorial01_no_direct_word_projection (q : RingQueue) (i : Fin q.items)
    (word : Addr) (generation : Nat) (scope : Scope) (rename : Addr → Addr) :
    ((tutorialConsumerWords word generation scope).filterMap wordAddress).map rename ≠
      (q.consume i).filterMap wordAddress := by
  rw [consumer_word_addresses]
  intro h
  change [rename word, rename word] = [_, _] at h
  obtain ⟨h₁, h₂⟩ := List.cons.inj h
  have eq := h₁.symm.trans (List.cons.inj h₂).1
  cases q.disjoint eq

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
    let cells := List.finRange q.width
    let bit := MemCell.of .nat (q.epoch i % 2)
    let m₁ := cells.foldl (fun m k => w.put m (q.address (.slot j k)) (q.value i k)) mem
    let m₂ := w.put m₁ (q.address (.full j)) bit
    let m₃ := cells.foldl (fun m k => w.put m (q.address (.output i k)) (q.value i k)) m₂
    w.put m₃ (q.address (.empty j)) bit) s

/-- Both parties can access the slot and both words. Only the consumer
touches an output, which may be private to it. -/
def AccessibleIn (q : RingQueue) (symm : VeriTile.Triton.RegionName → Bool) : Prop :=
  ∀ c, AccessibleAt symm q.consumer (q.address c) ∧
    match c with
    | .output _ _ => True
    | _ => AccessibleAt symm q.producer (q.address c)

/-- Before epoch zero the full bit is unready and the empty bit is ready. -/
def Initialized (q : RingQueue) (s : DistState) : Prop :=
  ∀ j, s.cell (q.address (.full j)) = .of .nat 1 ∧
    s.cell (q.address (.empty j)) = .of .nat 1

/-- UNSIGNED. S6.2/#61. The producer releases full after writing the slot;
the consumer releases empty after copying it. The second handshake orders the
previous read before the next overwrite, including across a parity wrap. -/
theorem ringQueue_correct (q : RingQueue) (l : Launch P) (s : DistState) (sound : SoundLaunch l)
    (code : Realizes l q.body) (accessible : q.AccessibleIn l.symm)
    (init : q.Initialized s) (reuse : q.WaitsOnReuse) (bits : q.UsesEpochBit) :
    Outcome l s (fun final => final = q.sequential l.cells s) := by
  sorry

/-- Three slots and ten items reach the fourth use of slot zero.
Physical regions differ by role and each offset identifies its index. -/
def tiledThreeStage (width : Nat) : RingQueue where
  stages := 3
  stages_pos := by decide
  items := 10
  width := width
  producer := .thread ⟨0, [0]⟩ 0 0
  consumer := .thread ⟨0, [0]⟩ 0 1
  different := by decide
  scope := .cta
  covers := by decide
  address
    | .slot j k => ⟨.shared ⟨0, [0]⟩, ⟨"slot"⟩, k.val * 3 + j.val⟩
    | .full j => ⟨.shared ⟨0, [0]⟩, ⟨"full"⟩, j.val⟩
    | .empty j => ⟨.shared ⟨0, [0]⟩, ⟨"empty"⟩, j.val⟩
    | .output i k => ⟨.global 0, ⟨"out"⟩, k.val * 10 + i.val⟩
  disjoint := by
    intro x y h
    cases x <;> cases y <;> simp_all [Fin.ext_iff] <;> omega
  value i k := .of .nat (i.val + 10 + 100*k.val)
  phase e := e % 2
  waitEmpty i := decide (3 ≤ i.val)

abbrev threeStage := tiledThreeStage 1

example :
    let q := tiledThreeStage 2
    let final := q.sequential writes exampleState
    (final.cell (q.address (.output ⟨9, by decide⟩ ⟨0, by decide⟩))).readAs .nat = some 19 ∧
    (final.cell (q.address (.output ⟨9, by decide⟩ ⟨1, by decide⟩))).readAs .nat = some 119 ∧
    (q.produce ⟨3, by decide⟩).length = 4 ∧ (q.consume ⟨3, by decide⟩).length = 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem threeStage_reuse : threeStage.WaitsOnReuse := by
  intro i hi
  simpa [threeStage, tiledThreeStage] using hi

theorem threeStage_bits : threeStage.UsesEpochBit := fun _ => rfl

theorem threeStage_accessible (symm : VeriTile.Triton.RegionName → Bool) :
    threeStage.AccessibleIn symm := by
  intro c
  cases c <;> simp [threeStage, tiledThreeStage, AccessibleAt, Accessible, Agent.within, Agent.cta?, Agent.rankOf]

/-- Initialize only the two flag regions to one. Payload and output cells
start at zero. The client exercises three reuses of slot zero. -/
def threeStageInitial : DistState :=
  { exampleState with cell := fun p =>
      if p.region = ⟨"full"⟩ ∨ p.region = ⟨"empty"⟩ then .of .nat 1 else .of .nat 0 }

example :
    let l := launch (exampleEnv writes) threeStage.body
    Outcome l threeStageInitial (fun final => final = threeStage.sequential l.cells threeStageInitial) :=
  threeStage.ringQueue_correct _ _ (launch_sound _ _ (by
    intro a c active hc
    simp only [RingQueue.body] at active
    split at active <;> rename_i h
    · subst a; cases hc; rfl
    · split at active
      · rename_i he; subst a; cases hc; rfl
      · cases active)) (launch_realizes _ _) (threeStage_accessible _)
    (fun _ => ⟨rfl, rfl⟩) threeStage_reuse threeStage_bits

example :
    (threeStage.body threeStage.producer).map List.length = some 27 ∧
    (threeStage.body threeStage.consumer).map List.length = some 30 := by decide

example :
    let final := threeStage.sequential writes threeStageInitial
    (final.cell (threeStage.address (.output ⟨0, by decide⟩ ⟨0, by decide⟩))).readAs .nat = some 10 ∧
    (final.cell (threeStage.address (.output ⟨9, by decide⟩ ⟨0, by decide⟩))).readAs .nat = some 19 ∧
    (final.cell (threeStage.address (.slot ⟨0, by decide⟩ ⟨0, by decide⟩))).readAs .nat = some 19 := by
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
  norm_num [stageModulus, threeStage, tiledThreeStage, epoch] at bad

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
private abbrev ringLaunch (q : RingQueue) := launch (exampleEnv writes) q.body
private abbrev lch := ringLaunch stageModulus
private abbrev initial (q : RingQueue) := (ringLaunch q).initial threeStageInitial

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

private def start (q : RingQueue) : Prefix := ⟨initial q, rfl, by simp [Machine.trace, initial, Launch.initial]⟩

private abbrev advance (q : RingQueue) (s : Prefix) (a : Agent) :=
  Σ' t : Prefix, step (ringLaunch q) s.cfg (.agent a) t.cfg

private def enter (q : RingQueue) (s : Prefix) (a : Agent) (pc : List Instr)
    (h : s.cfg.pc a = some (.ready pc)) : advance q s a := by
  let t : Config (List Instr) := { s.cfg with
    history := s.cfg.history ++ [.segment a ∅ ∅]
    pc := Function.update s.cfg.pc a ((nextAction a id pc).cursor) }
  refine ⟨⟨t, s.pending, ?_⟩, ?_⟩
  · simpa [t, Machine.trace, Occurrence.event?, List.filterMap_append] using s.clean
  · exact step.segment (seg := idleSegment a) h rfl rfl (by simp [idleSegment]) rfl

private def issue (q : RingQueue) (s : Prefix) (a : Agent) (e : Event) (d : AccessValue)
    (k : List (Option MemCell) → List Instr) (mem : DistState) (v : Option MemCell)
    (cursor : s.cfg.pc a = some (.waiting ⟨a,e,d⟩ [] k))
    (owned : a.within a) (accessible : e.AccessibleBy (ringLaunch q).symm a)
    (plain : ∀ t, e ≠ .initiate t) (fire : Fire (ringLaunch q) s.cfg.toMachine ⟨a,e,d⟩ mem s.cfg.pending v) :
    advance q s a := by
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
private def tick (q : RingQueue) (s : Prefix) (a : Agent) : Option (advance q s a) := do
  match h : s.cfg.pc a with
  | some (.ready pc) => return enter q s a pc h
  | some (.waiting ⟨actor,e,d⟩ [] k) =>
    if ha : actor = a then
      if ho : a.within a then
        if accessible : e.accesses.all (fun (_,p,_) => decide (AccessibleAt (ringLaunch q).symm a p)) then
          have access : e.AccessibleBy (ringLaunch q).symm a := fun k p m member =>
            of_decide_eq_true (List.all_eq_true.mp accessible (k,p,m) member)
          match e, d, h, access with
          | .access .store p .plain, .store v, h, acc =>
            return issue q s a _ _ k _ _ (ha ▸ h) ho acc
              (by intro t bad; cases bad) (.store a p _ v)
          | .access .load p .plain, .noValue, h, acc =>
            return issue q s a _ _ k _ _ (ha ▸ h) ho acc
              (by intro t bad; cases bad) (.load a p _)
          | .bump ⟨.word p,.set,n,m⟩, .noValue, h, acc =>
            return issue q s a _ _ k _ _ (ha ▸ h) ho acc
              (by intro t bad; cases bad) (.bump a _ 0 (by intro bad; cases bad))
          | .wait (.word p) .eq n m, .noValue, h, acc =>
            if hn : (s.cfg.mem.cell p).readAs .nat = some n then
              return issue q s a _ _ k _ _ (ha ▸ h) ho acc
                (by intro t bad; cases bad) (.wait a (.word p) .eq n m n hn rfl)
            else none
          | _, _, _, _ => none
        else none
      else none
    else none
  | _ => none

private def replay (q : RingQueue) (s : Prefix) : (agents : List Agent) →
    Option (Σ' t : Prefix, Run (ringLaunch q) s.cfg (agents.map Choice.agent) t.cfg)
  | [] => some ⟨s, .nil _⟩
  | a :: as => do
    let ⟨next, h⟩ ← tick q s a
    let ⟨final, rest⟩ ← replay q next as
    return ⟨final, .cons h rest⟩

private abbrev producer := stageModulus.producer
private abbrev consumer := stageModulus.consumer
private abbrev slot0 := stageModulus.address (.slot ⟨0, by decide⟩ ⟨0, by decide⟩)
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
  let result := replay stageModulus (start stageModulus) choices
  have ok : result.isSome := by decide +revert
  let witness := result.get ok
  refine ⟨_, witness.1.cfg, witness.2, adjacentRace _ 102 ?_ ?_⟩ <;> rfl

/- Advance the consumer through its resulting store. Item 6 actually
receives item 9's payload (19), whereas its sequential value is 16. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
example :
    ((replay stageModulus (start stageModulus) (choices ++ [consumer, consumer])).bind fun result =>
      (result.1.cfg.mem.cell (stageModulus.address (.output ⟨6, by decide⟩ ⟨0, by decide⟩))).readAs .nat) =
      some 19 ∧ (stageModulus.value ⟨6, by decide⟩ ⟨0, by decide⟩).readAs .nat = some 16 := ⟨rfl, rfl⟩

private theorem inactivePC {l : Launch P} {s t : Config P} (r : Run l s sched t)
    (a : Agent) (off : s.pc a = none) : t.pc a = none := by
  induction r with
  | nil => exact off
  | cons step _ ih =>
    apply ih
    cases step with
    | @segment b pc seg mem atPC _ _ _ _ =>
      have ne : a ≠ b := by rintro rfl; rw [off] at atPC; contradiction
      simpa [Function.update_of_ne ne] using off
    | @fire b h t k final values atPC _ _ =>
      have ne : a ≠ b := by rintro rfl; rw [off] at atPC; contradiction
      simpa [Function.update_of_ne ne] using off
    | deliver => exact off

private def orderedChoices : List Agent :=
  let p := fun n => List.replicate n threeStage.producer
  let c := fun n => List.replicate n threeStage.consumer
  (List.replicate 3 (p 4 ++ c 8)).flatten ++
    (List.replicate 7 (p 6 ++ c 8)).flatten ++ [threeStage.producer, threeStage.consumer]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
/-- Replay ten items on three slots, spanning four epochs and both
participants' return steps. The entire final memory equals the independent
sequential fold, including every full/empty word and all untouched cells. -/
theorem threeStage_complete_replay :
    let l := launch (exampleEnv writes) threeStage.body
    ∃ sched final, Run l (l.initial threeStageInitial) sched final ∧
      Complete final ∧ final.mem = threeStage.sequential writes threeStageInitial := by
  dsimp only
  let result := replay threeStage (start threeStage) orderedChoices
  have ok : result.isSome := by decide +revert
  let w := result.get ok
  refine ⟨_, w.1.cfg, w.2, ⟨?_, ?_⟩, ?_⟩
  · intro a
    by_cases hp : a = threeStage.producer
    · subst a; rfl
    by_cases hc : a = threeStage.consumer
    · subst a; rfl
    apply inactivePC w.2
    change (threeStage.body a).map Cursor.ready = none
    simp [body, hp, hc]
  · intro o member
    rw [w.1.pending] at member
    cases member
  · -- Check the last reuse of slot zero before comparing the entire memory.
    let empty0 := threeStage.address (.empty ⟨0, by decide⟩)
    guard_expr (decide ((w.1.cfg.mem.cell empty0).readAs .nat =
      ((threeStage.sequential writes threeStageInitial).cell empty0).readAs .nat)) =~ true
    rfl

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
theorem oneShotFlag_correct (f : OneShotFlag) (l : Launch P) (s : DistState) (sound : SoundLaunch l)
    (valid : f.Valid l s) (program : Realizes l f.body) :
    Outcome l s (fun final => final =
      f.sequentialWrites.foldl (fun mem pv => l.cells.put mem pv.1 pv.2) s) := by
  sorry

end OneShotFlag

/-- In each generation, each participant publishes its owned tile, arrives,
waits for all participants, then copies each cell of a peer's tile to an owned result. Each
generation uses separate payload and result cells, so faster participants may
start the next generation before every reader finishes the previous one. -/
structure PhaseBarrier where
  width : Nat
  members : List Agent
  phases : Nat
  counter : Counter
  peer : Agent → Agent
  payload : Nat → Agent → Fin width → Addr
  receipt : Nat → Agent → Fin width → Addr
  value : Nat → Agent → Fin width → MemCell
  release : Mode
  acquire : Mode

namespace PhaseBarrier

def round (b : PhaseBarrier) (n : Nat) (a : Agent) : List Instr :=
  (List.finRange b.width).map (fun k => store (b.payload n a k) (b.value n a k)) ++
    [signal b.counter .add 1 b.release, wait b.counter .ge ((n+1)*b.members.length) b.acquire] ++
    (List.finRange b.width).map (fun k => .copy (b.payload n (b.peer a) k) (b.receipt n a k))

def body (b : PhaseBarrier) (a : Agent) : Option (List Instr) :=
  if a ∈ b.members then some ((List.range b.phases).flatMap (fun n => b.round n a)) else none

/-- Phase-major reference: all publishers write, then all readers copy. The
reference depends only on the inputs and peer map, independent of a schedule. -/
def sequentialWrites (b : PhaseBarrier) : List (Addr × MemCell) :=
  (List.range b.phases).flatMap fun n =>
    b.members.flatMap (fun a => (List.finRange b.width).map fun k => (b.payload n a k, b.value n a k)) ++
    b.members.flatMap (fun a => (List.finRange b.width).map fun k => (b.receipt n a k, b.value n (b.peer a) k))

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
  storage : ∀ n < b.phases, ∀ a ∈ b.members, ∀ k,
    AccessibleAt l.symm a (b.payload n a k) ∧ AccessibleAt l.symm a (b.payload n (b.peer a) k) ∧
      AccessibleAt l.symm a (b.receipt n a k)
  visible : ∀ n < b.phases, ∀ a ∈ b.members, ∀ k,
    Mode.Pairs l.reach (b.payload n (b.peer a) k) (b.peer a) a b.release b.acquire

/-- UNSIGNED. S6.4/#63. With the exact roster, the kth arrival of each member
precedes each kth successful wait. No post-barrier copy reads a future phase. -/
theorem phaseBarrier_correct (b : PhaseBarrier) (l : Launch P) (s : DistState) (sound : SoundLaunch l)
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
  (flagExample viaPut).oneShotFlag_correct _ _ (launch_sound _ _ (by
    intro a c active hc
    simp only [OneShotFlag.body] at active
    split at active
    · rename_i he; subst a; cases hc
    · split at active
      · rename_i hm; simp [flagExample] at hm; subst a; cases hc
      · cases active)) (flagValid viaPut) (launch_realizes _ _)

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
  width := 2
  members := [.rank 0, .rank 1]
  phases := 2
  counter := .rendezvous 7
  peer a := if a = .rank 0 then .rank 1 else .rank 0
  payload n a k := syncCell (8*n + 2*a.rankOf + k.val)
  receipt n a k := syncCell (8*n + 4 + 2*a.rankOf + k.val)
  value n a k := .of .nat (10*n + a.rankOf + 1 + 100*k.val)
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
  · intro n _ a _ k
    exact ⟨⟨trivial, Or.inr rfl⟩, ⟨trivial, Or.inr rfl⟩, ⟨trivial, Or.inr rfl⟩⟩
  · intro _ _ _ _ _; exact ⟨rfl, rfl, trivial, trivial⟩

example : Outcome phaseLaunch exampleState (fun final => final =
    phaseExample.sequentialWrites.foldl (fun s pv => writes.put s pv.1 pv.2) exampleState) :=
  phaseExample.phaseBarrier_correct _ _ (launch_sound _ _ (by
    intro a c active hc
    simp only [PhaseBarrier.body] at active
    split at active
    · rename_i hm; simp [phaseExample] at hm; rcases hm with rfl | rfl <;> cases hc
    · cases active)) phaseValid (launch_realizes _ _)

example :
    let final := phaseExample.sequentialWrites.foldl (fun s pv => writes.put s pv.1 pv.2) exampleState
    (final.cell (syncCell 12)).readAs .nat = some 12 ∧
    (final.cell (syncCell 13)).readAs .nat = some 112 := ⟨rfl, rfl⟩

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
  have impossible : (some 12 : Option Nat) = some 6 := congrArg (Option.map List.length) h
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
theorem atomicAccumulation_correct {P : Type} (q : AtomicAccumulation) (l : Launch P) (s : DistState) (sound : SoundLaunch l)
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
  exact twoCTAs.atomicAccumulation_correct _ _ (launch_sound _ _ (by
    intro a c active hc
    simp only [AtomicAccumulation.body] at active
    split at active
    · rename_i hm; simp [twoCTAs] at hm; rcases hm with rfl | rfl <;> cases hc <;> rfl
    · cases active)) 0 (DistState.cell_putCell ..)
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
