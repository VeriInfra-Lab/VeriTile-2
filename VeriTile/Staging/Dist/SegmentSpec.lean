/-
VeriTile.Staging.Dist.SegmentSpec

Segment interface, bridge statements and per-agent continuation of the Dist
line, drafted by ticket S3.1 (#43) and revised to the user's decisions of
2026-11-13. Part 1 is signed on 2026-11-23: its five theorems, each with the
definitions under it (`documents/dist/FrozenStatements.tsv`,
`FrozenDefinitions.tsv`). The user approved the choices N2, N3 and N4 below as
taken; the agent recorded the signature on the user's delegation. The stubs of
part 1 are under signed statements: the ticket that defines one changes its
recorded fingerprint, and the coordinator reviews and records that change.
Part 2 is signed on 2026-11-27 (user decision 三 of 2026-11-25, recorded on
#43): the six statements `AgentProgram.Step.deterministic`,
`AgentProgram.ofBody_step_noSync`, `slice_noSync`, `slice_sync`,
`AgentProgram.ofBody_steps` and `exec_noSync_eq_exec`, with the definitions
under them (`AgentProgram.Step`, `AgentProgram.Steps`, `AgentProgram.ofBody`,
`slice`). The same decision ratifies N1, N5, N5' and N6 as already frozen:
`AccessValue`, `Emission`, `Next`, `AgentProgram` and `AgentProgram.NextLocal`
lie under the signed `step_comm` (#47) and are frozen with it. It takes N7
(both `ofBody` and `ofCuts`) and N9 (`ofBody` a definition) as written, and
makes `slice` a definition. `EventCut` and `AgentProgram.ofCuts` are decided
by N7 but not frozen: no signed statement mentions them. The notes on N1 to
N9 below are the record of the choices as first drafted; where they differ
from the declarations, the 2026-11-24 choices on #47 (part 2 below) and
decision 三 govern.

An agent runs sequential code between synchronization or communication
points. A segment is one such piece of code, seen as a transformer of the
distributed state together with the cells it may read and may write. The
program of an agent is run step by step: from a program state the agent runs
the segment up to its next event, emits that event and continues, or finishes.

The file has two parts, signed separately. No declaration of part 1 mentions a
declaration of part 2 or an `Event`.

- Part 1: `Segment`, `Segment.FootprintSound`, and the bridge for one segment
  made from upstream statements. The agent views, `Segment`,
  `Segment.FootprintSound` and `Segment.frame` now live in
  `VeriTile/Dist/Segment.lean` (S3.2, #44); this file imports them.
- Part 2: `Next`, `AgentProgram`, the step relation `AgentProgram.Step`, the
  flat body as one program (`AgentProgram.ofBody`, `slice`) and the statements
  about them.

Part 2 proves the flat slice equations, step determinism and the sequence of
segments and events. Its no-sync step equation uses the part-1 run-view bridge,
which still awaits the implementation of `Segment.ofStmts`. #48 owns the later
move of the signed program declarations. `EventControlFlow.md` below is
`documents/dist/EventControlFlow.md`; K1 to K28 are its kernel rows.

Decisions (user decision, 2026-11-13, recorded on #43):

1. A segment is a partial function `DistState → Option DistState`; `none` is
   the failure of the upstream sequential execution. Access violations and
   data races are judged by the execution semantics (S4) from the footprints.
2. A footprint is a set of cells, `Set Addr`.
3. A footprint is a function of the state in which the segment starts;
   `FootprintSound` says that it is stable.
4. `FootprintSound` has three clauses: `frame`, `confined`, `reads_determine`.
5. A segment is owned by an agent: a CTA, or a group or a thread below it. The
   CTA is the special case.
6. Slicing yields, per agent, a continuation that is run to the next event,
   stated as a step relation. The flat list of segments fixed before execution
   is kept as a derived lemma for the programs it covers.
7. A body with `n` events gives `n + 1` segments, some of which may hold no
   statement.
8. `DistState.cell` and `DistState.setBlock` are declared here and belong to
   the multi-rank state of ticket S1.5 (#34).
9. Signing is in two steps: part 1 first, part 2 after it.

Decisions on spin loops and waits (user decisions), recorded where they meet
part 2:

- 2026-11-13: a spin loop with an empty body is one blocking event. It is an
  event of the step relation, not a loop of segments.
- 2026-11-21: the spin loops of the DeepEP port have bodies that are not empty
  and are left to the continuation. A round is steps of one agent: it
  evaluates the condition, which reads memory another agent writes, and then
  runs the body or leaves the loop. `AgentProgram` expresses both ways of
  reading: a load that is an event hands its value to the continuation
  (`Next.emit e k`; `k v` is the body or the exit), and a load inside the
  segment is seen by `next`, which reads the state the segment starts in.
- 2026-11-21: a wait followed by a swap in one step is a `wait` and a `set`
  write that the step relation fires together; there is no new event
  constructor. `Next.emit` carries one event, so the file does not express
  this yet: two `emit`s in a row are two steps. Settled by the 2026-11-24
  choices on #47: `Next.emitGroup` issues the wait and the `set` as one
  group, the CAS group that `SoundLaunch` admits.

New choices. Each was needed to make the file elaborate; the file takes the
option marked "taken". N2, N3 and N4 bear on part 1 and are decided as taken
(user decision, 2026-11-23). The others bear on part 2 and are decided by
decision 三 of 2026-11-25 (above); N8 is superseded by the 2026-11-24 choices
on #47.
The pull request of the revision (#474) gives the evidence.

N1. The program state of an agent.
    (a) Taken: any type `P`, with two functions (`AgentProgram P`): the
        segment that starts at a program state, and what follows it. The flat
        body `List (Stmt ⊕ Event)` is one instance. Cost: no shared syntax, so
        each front end defines its own `P` and proves its own footprints; a
        loop is whatever the front end makes `next` return.
    (b) One syntax tree of the Dist line: upstream statements, an event
        marker, a branch and a loop that may hold events. Cost: fixes a syntax
        before the TileLang line has one; the kernels that need a loop (K25,
        K26, K28) are TileLang, not upstream statements.
    Recommended: (a) now; (b) can later be given as an instance of (a).
N2. The local state of a group or a thread.
    (a) Taken: an upstream `BlockState` again (`DistState.view`): the memory
        the agent can reach and the registers that are its own. Whether a
        group's registers are a store of their own or the CTA's registers
        restricted to the group is left to S1.6 (#35): `confined` speaks only
        of agents that do not contain one another, so it holds under both.
        Cost: S1.6 owes the laws listed at `DistState.subView`.
    (b) A new state type for agents below the CTA. Cost: `stepStmts` does not
        run on it, so there is no bridge for such an agent.
    Recommended: (a), with a separate register store per agent.
N3. A whole rank (`Agent.rank`) owns no segment that changes the state: its
    view is the default state and writing it back does nothing. The other
    option, a stub, adds laws about the host that no ticket owns.
N4. The bridge for an agent below the CTA.
    (a) Taken: the run equation is claimed for every agent
        (`Segment.ofStmts_run_view`); it defines what running upstream
        statements on a projection is. Soundness of the computed footprints is
        claimed for a CTA only (`Segment.ofStmts_footprintSound`).
    (b) Soundness for every agent now. Cost: signs a statement whose proof
        needs laws that S1.6 has not designed.
    (c) No bridge below the CTA. Cost: the flat body of a thread (K3, K4,
        K11) has no segment.
    Recommended: (a); state soundness below the CTA when S1.6 is frozen.
N5. How the value that an event reads reaches the agent. `Event` carries no
    such value and no destination register.
    (a) Taken: the continuation takes it (`Next.emit e k`, `k : Option MemCell
        → P`); `none` for an event that reads nothing. Cost: S4.1 has to say,
        per event, which value it passes.
    (b) The event comes with a transformer that S4 runs with it. Cost: a
        second place that says what an event does to memory.
    (c) A slot of the distributed state. Cost: one more stub for S1.5.
    Recommended: (a).
N6. `AgentProgram.next` reads the state in which the segment starts, not the
    one it ends in: the end state need not record which branch was taken.
    Not stated: that `next` depends only on the read footprint and the local
    state. The commutation theorem of S4 needs it; S4.1 (#47) should add it.
N7. The flat body carries evaluated events (`Stmt ⊕ Event`), so the derived
    lemma covers only bodies whose event arguments are known before execution.
    K6 is not among them (`EventControlFlow.md`, section 1.4). The other
    option, an event computed from the state at each cut, covers K6 at the
    cost of a flat list that is no longer fixed before execution.
N8. An event is performed by the agent whose program emits it. A program of a
    CTA cannot give one of its events to a single thread (the fence of K1,
    thread 0 of K6). The other option is an agent field on `Next.emit`; it
    decides the ordering convention of K3, K4, K23 and K27 and is not taken.
N9. `AgentProgram.ofBody` is a definition, not a stub: it is five lines and the
    reader sees which program a flat body is. `slice` is a definition too
    (user decision, 2026-11-25): `slice_noSync` and `slice_sync` determine it.

The event type is `Event` of `VeriTile/Dist/Event.lean`, signed
on 2026-11-13; it is no longer a parameter.
-/
import VeriTile.Triton.Semantics.Step
import VeriTile.Dist.State
import VeriTile.Dist.Segment
import VeriTile.Staging.Dist.LocationSpec
import VeriTile.Dist.Event.Transfer

namespace VeriTile.Dist

open VeriTile.Triton (BlockState MemCell Stmt Kernel stepStmts exec)

/-! # Part 1: segments, footprint soundness, the bridge for one segment -/

/-! ## Segments of upstream statements (S3.3) -/

/-- Under signed statements (S3.3). Part 1. The segment that runs the upstream
statements `code` as agent `a`: upstream `stepStmts` on the view of `a`,
written back. Both footprints are every cell visible to `a`, and empty when
`code` is empty. They do not look at what the statements access. -/
noncomputable def Segment.ofStmts (a : Agent) (code : List Stmt) : Segment where
  agent := a
  run σ := (stepStmts code (σ.view a)).map (σ.setView a)
  reads _ := {p | code ≠ [] ∧ ViewName.Visible a p}
  writes _ := {p | code ≠ [] ∧ ViewName.Visible a p}

/-- Signed. Part 1. Proved by S3.3. A segment made from statements is run by
the agent it was made for. -/
theorem Segment.ofStmts_agent (a : Agent) (code : List Stmt) :
    (Segment.ofStmts a code).agent = a := rfl

/-- Signed. Part 1. Proved by S3.3. The bridge for one segment of a CTA:
running it on the distributed state is running the upstream `stepStmts` of its
statements on the block state of the CTA and writing the result back. It fails
exactly when the upstream execution fails. -/
theorem Segment.ofStmts_run (c : Cta) (code : List Stmt) (σ : DistState) :
    (Segment.ofStmts (.cta c) code).run σ =
      (stepStmts code (σ.block c.rank c.pid)).map (σ.setBlock c.rank c.pid) := rfl

/-- Signed. Part 1. Proved by S3.3. The same equation for every agent, on
the projection of the agent. For a group or a thread it is what running
upstream statements as that agent means, and it says nothing before S1.6
defines the projection. Not claimed: that the runs of the threads of a CTA
compose to the upstream execution on the block state of the CTA. -/
theorem Segment.ofStmts_run_view (a : Agent) (code : List Stmt) (σ : DistState) :
    (Segment.ofStmts a code).run σ = (stepStmts code (σ.view a)).map (σ.setView a) := rfl

/-- A block state with its memory replaced by that of another one is the other
one when the rest agrees. -/
private theorem withMem_eq {x y : BlockState} (hr : x.regs = y.regs) (hp : x.pids = y.pids)
    (hu : x.undef = y.undef) (hn : x.numPids = y.numPids) : { x with mem := y.mem } = y := by
  cases x; cases y; cases hr; cases hp; cases hu; cases hn; rfl

/-- Two states whose contexts agree at `t` give `t` the same local state. -/
private theorem sameLocal_of_context {σ τ : DistState} {t : Agent}
    (h : σ.context t = τ.context t) : DistState.SameLocal t σ τ := by
  cases t with
  | rank => rfl
  | _ =>
    refine withMem_eq (x := σ.view _) (y := τ.view _) ?_ rfl ?_ ?_
    · exact congrArg AgentContext.regs h
    · exact congrArg AgentContext.undef h
    · exact congrArg AgentContext.numPids h

/-- Signed. Part 1. Proved by S3.3. The footprints computed from the
statements of a CTA are sound. Nothing is claimed here for a group or a
thread: it needs the laws that S1.6 gives the projection. -/
theorem Segment.ofStmts_footprintSound (c : Cta) (code : List Stmt) :
    (Segment.ofStmts (.cta c) code).FootprintSound := by
  constructor
  · intro σ σ' hrun p hp
    rw [Segment.ofStmts_run, Option.map_eq_some_iff] at hrun
    obtain ⟨b, hb, rfl⟩ := hrun
    by_cases hcode : code = []
    · subst hcode
      rw [stepStmts.nil, Option.some.injEq] at hb
      rw [← hb, DistState.setBlock_block]
    · rw [DistState.setBlock_eq_setSubView]
      exact DistState.cell_setSubView_of_not_visible _ _ _ _ fun hv => hp ⟨hcode, hv⟩
  · intro σ σ' hrun
    rw [Segment.ofStmts_run, Option.map_eq_some_iff] at hrun
    obtain ⟨b, -, rfl⟩ := hrun
    refine ⟨⟨b, rfl⟩, fun t ht _ => sameLocal_of_context ?_⟩
    have hne : t ≠ .cta c := by
      rintro rfl
      exact ht rfl
    exact (DistState.context_setSubView_ne σ hne b).symm
  · intro σ₁ σ₂ hagree hlocal
    refine ⟨rfl, rfl, fun σ₁' hrun => ?_⟩
    rw [Segment.ofStmts_run, Option.map_eq_some_iff] at hrun
    obtain ⟨b, hb, rfl⟩ := hrun
    by_cases hcode : code = []
    · subst hcode
      rw [stepStmts.nil, Option.some.injEq] at hb
      refine ⟨σ₂, ?_, fun p hp => (hp.1 rfl).elim, ?_⟩
      · rw [Segment.ofStmts_run, stepStmts.nil, Option.map_some, DistState.setBlock_block]
      · rw [← hb, DistState.setBlock_block]
        exact hlocal
    · -- The block state of the CTA is its visible cells and its local state.
      have hblock : σ₁.block c.rank c.pid = σ₂.block c.rank c.pid := by
        have hmem : (σ₁.block c.rank c.pid).mem = (σ₂.block c.rank c.pid).mem := by
          funext n i
          exact hagree _ ⟨hcode, ViewName.visible_address (.cta c) n i⟩
        have hl : { σ₁.block c.rank c.pid with mem := (σ₂.block c.rank c.pid).mem } =
            σ₂.block c.rank c.pid := hlocal
        rw [← hl]
        exact congrArg (fun m => { σ₁.block c.rank c.pid with mem := m }) hmem
      refine ⟨σ₂.setBlock c.rank c.pid b, ?_, ?_, ?_⟩
      · rw [Segment.ofStmts_run, ← hblock, hb, Option.map_some]
      · intro p hp
        rw [DistState.cell_setBlock_of_visible _ _ _ _ hp.2,
          DistState.cell_setBlock_of_visible _ _ _ _ hp.2]
      · have hu : (σ₁.context (.cta ⟨c.rank, c.pid⟩)).undef =
            (σ₂.context (.cta ⟨c.rank, c.pid⟩)).undef := congrArg BlockState.undef hblock
        have hn : (σ₁.context (.cta ⟨c.rank, c.pid⟩)).numPids =
            (σ₂.context (.cta ⟨c.rank, c.pid⟩)).numPids := congrArg BlockState.numPids hblock
        show { (σ₁.setBlock c.rank c.pid b).block c.rank c.pid with
            mem := ((σ₂.setBlock c.rank c.pid b).block c.rank c.pid).mem } =
          (σ₂.setBlock c.rank c.pid b).block c.rank c.pid
        rw [DistState.block_setBlock, DistState.block_setBlock, hu, hn]

/-! # Part 2: the continuation of an agent -/

/-! ## Programs and steps (S3.3) -/

/-! The 2026-11-24 choices on #47 supersede the historical N8 and singleton
notes in the header. Every issue names its actor; the scheduling unit is one
nonempty group. SoundLaunch restricts multi-event groups to a CAS pair.
The declarations marked "Signed (#47, via step_comm)" are frozen under
`step_comm`; those marked "Signed (#43, part 2)" are signed with #43 part 2.
`EventCut` and `AgentProgram.ofCuts` are decided (N7) but not frozen. -/

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

/-- Signed (#43, part 2). Owner: S3.3. One step of an agent: from program state
`p` and state `σ` it runs the segment up to its next event, reaches `σ'`, and
then finishes or emits that event and continues, as `n` says. The effect of
the event and the interleaving with other agents belong to S4. -/
def AgentProgram.Step {P : Type} (prog : AgentProgram P) (p : P) (σ σ' : DistState)
    (n : Next P) : Prop :=
  (prog.segment p).run σ = some σ' ∧ prog.next p σ = n

/-- Signed (#43, part 2). Owner: S3.3. `prog.Steps p l`: started in program state
`p`, the agent can take the steps `l` for some states and some values read at
its events: the segments it runs and the events it emits, in order, down to
the end of the program. The runs are not required to succeed. -/
inductive AgentProgram.Steps {P : Type} (prog : AgentProgram P) :
    P → List (Segment ⊕ Event) → Prop where
  | finish {p : P} {σ : DistState} (h : prog.next p σ = .finish) :
      prog.Steps p [Sum.inl (prog.segment p)]
  | emitGroup {p : P} {σ : DistState} {e : Emission} {es : List Emission}
      {k : List (Option MemCell) → P} {vs : List (Option MemCell)} {l : List (Segment ⊕ Event)}
      (h : prog.next p σ = .emitGroup e es k) (arity : vs.length = es.length + 1)
      (rest : prog.Steps (k vs) l) :
      prog.Steps p (.inl (prog.segment p) :: ((e :: es).map (fun x => .inr x.event) ++ l))

/-- Signed (#47, via step_comm). Part 2. N6. The event, actor, payload and continuation are determined by the
segment's declared reads and its local state. Required of launch programs. -/
def AgentProgram.NextLocal {P : Type} (p : AgentProgram P) : Prop :=
  ∀ pc σ τ, DistState.AgreesOn ((p.segment pc).reads σ) σ τ →
    DistState.SameLocal (p.segment pc).agent σ τ → p.next pc σ = p.next pc τ

/-- UNSIGNED. Part 2. N7, decided as written (2026-11-25); not frozen. A cut
can compute its events from the state in which the preceding
segment starts. This includes K6's loaded lengths; ofBody retains fixed events. -/
structure EventCut where
  code : Segment
  issue : DistState → Emission × List Emission

/-- UNSIGNED. Part 2. N7, decided as written (2026-11-25); not frozen. Run
the segments and issue their event groups in list order. -/
noncomputable def AgentProgram.ofCuts (owner : Agent) : AgentProgram (List EventCut) where
  segment cuts := cuts.head?.map EventCut.code |>.getD (Segment.ofStmts owner [])
  next cuts σ := match cuts with
    | [] => .finish
    | c :: rest => let (e, es) := c.issue σ; .emitGroup e es fun _ => rest

/-- Signed (#43, part 2). Proved by S3.3. The segment part of a step is
deterministic: a program state and a state fix the state reached, the event
and the continuation. -/
theorem AgentProgram.Step.deterministic {P : Type} {prog : AgentProgram P} {p : P}
    {σ σ₁ σ₂ : DistState} {n₁ n₂ : Next P} (h₁ : prog.Step p σ σ₁ n₁)
    (h₂ : prog.Step p σ σ₂ n₂) : σ₁ = σ₂ ∧ n₁ = n₂ :=
  ⟨Option.some.inj (h₁.1.symm.trans h₂.1), h₁.2.symm.trans h₂.2⟩

/-- A singleton event can branch on its result just like a member of a CAS group. -/
example (seg : Segment) (e : Emission) (σ : DistState) (v : MemCell) :
    let prog : AgentProgram Bool :=
      ⟨fun _ => seg, fun p _ => if p then .emitGroup e [] (fun vs => vs.head?.join.isSome)
                                else .finish⟩
    prog.Steps true [.inl seg, .inr e.event, .inl seg] ∧
      prog.Steps true [.inl seg, .inr e.event, .inl seg, .inr e.event, .inl seg] :=
by
  let prog : AgentProgram Bool :=
    ⟨fun _ => seg, fun p _ => if p then .emitGroup e [] (fun vs => vs.head?.join.isSome) else .finish⟩
  change prog.Steps true _ ∧ prog.Steps true _
  have done_ : prog.Steps false [.inl seg] := .finish (σ := σ) rfl
  have once : prog.Steps true [.inl seg, .inr e.event, .inl seg] :=
    .emitGroup (p := true) (σ := σ) (e := e) (es := []) (vs := [none])
      (k := fun vs => vs.head?.join.isSome) rfl rfl done_
  exact ⟨once, .emitGroup (p := true) (σ := σ) (e := e) (es := []) (vs := [some v])
    (k := fun vs => vs.head?.join.isSome) rfl rfl once⟩

/-! ## The flat body as a program (S3.3) -/

/-- Signed (#43, part 2). Owner: S3.3. The program of agent `a` whose program
state is what is left of a flat body: upstream statements and, at each
synchronization or communication point, the event performed there. A step
runs the statements before the first event, emits that event and continues
with the body after it, whatever the event read. -/
noncomputable def AgentProgram.ofBody (a : Agent) : AgentProgram (List (Stmt ⊕ Emission)) where
  segment body := Segment.ofStmts a ((body.takeWhile Sum.isLeft).filterMap Sum.getLeft?)
  next body _ :=
    match body.dropWhile Sum.isLeft with
    | Sum.inr e :: rest => .emitGroup e [] fun _ => rest
    | _ => .finish

private theorem body_prefix (code : List Stmt) (tail : List (Stmt ⊕ Emission)) :
    ((code.map Sum.inl ++ tail).takeWhile Sum.isLeft).filterMap Sum.getLeft? =
        code ++ (tail.takeWhile Sum.isLeft).filterMap Sum.getLeft? ∧
      (code.map Sum.inl ++ tail).dropWhile Sum.isLeft = tail.dropWhile Sum.isLeft := by
  induction code with
  | nil => simp
  | cons s code ih => simp [ih.2]

/-- Signed (#43, part 2). Proved by S3.3. A step with no event left is the
upstream execution of the rest on the projection of the agent, written back;
then the agent has finished. -/
theorem AgentProgram.ofBody_step_noSync (a : Agent) (code : List Stmt) (σ σ' : DistState)
    (n : Next (List (Stmt ⊕ Emission))) :
    (AgentProgram.ofBody a).Step (code.map Sum.inl) σ σ' n ↔
      (stepStmts code (σ.view a)).map (σ.setView a) = some σ' ∧ n = .finish := by
  obtain ⟨head,tail⟩ := body_prefix code []
  simp at head tail
  simp [Step,ofBody,head,tail,Segment.ofStmts_run_view,eq_comm (a := n)]

/-- Signed (#43, part 2). Owner: S3.3. Slicing of a flat body of agent `a`. The
result lists, in program order, the segments between the events and the
events. It is fixed before execution. `go code` slices a body after the
statements `code`, which have not yet been closed into a segment. -/
noncomputable def slice (a : Agent) (body : List (Stmt ⊕ Emission)) : List (Segment ⊕ Event) :=
  go [] body
where
  go (code : List Stmt) : List (Stmt ⊕ Emission) → List (Segment ⊕ Event)
    | [] => [.inl (Segment.ofStmts a code)]
    | .inl stmt :: rest => go (code ++ [stmt]) rest
    | .inr e :: rest => .inl (Segment.ofStmts a code) :: .inr e.event :: go [] rest

private theorem slice.go_stmts (a : Agent) (code more : List Stmt) (rest : List (Stmt ⊕ Emission)) :
    slice.go a code (more.map Sum.inl ++ rest) = slice.go a (code ++ more) rest := by
  induction more generalizing code with
  | nil => simp
  | cons stmt more ih => simp [slice.go, ih]

/-- Signed (#43, part 2). A body with no event is one segment. -/
theorem slice_noSync (a : Agent) (code : List Stmt) :
    slice a (code.map Sum.inl) = [Sum.inl (Segment.ofStmts a code)] := by
  simpa [slice.go] using slice.go_stmts a [] code []

/-- Signed (#43, part 2). Slicing cuts at the first event: the
statements before it are one segment, and the rest of the body is sliced in
the same way. -/
theorem slice_sync (a : Agent) (code : List Stmt) (e : Emission) (rest : List (Stmt ⊕ Emission)) :
    slice a (code.map Sum.inl ++ Sum.inr e :: rest) =
      Sum.inl (Segment.ofStmts a code) :: Sum.inr e.event :: slice a rest := by
  simpa [slice.go] using slice.go_stmts a [] code (Sum.inr e :: rest)

private theorem first_event (body : List (Stmt ⊕ Emission)) :
    (∃ code : List Stmt, body = code.map Sum.inl) ∨
      ∃ (code : List Stmt) (e : Emission) (rest : List (Stmt ⊕ Emission)),
        body = code.map Sum.inl ++ .inr e :: rest := by
  induction body with
  | nil => exact .inl ⟨[],rfl⟩
  | cons head tail ih =>
    cases head with
    | inr e => exact .inr ⟨[],e,tail,rfl⟩
    | inl s =>
      obtain ⟨code,rfl⟩|⟨code,e,rest,rfl⟩ := ih
      · exact .inl ⟨s :: code,rfl⟩
      · exact .inr ⟨s :: code,e,rest,rfl⟩

/-- Signed (#43, part 2). Proved by S3.3. The derived lemma: for a flat body, a
program with no loop around an event, the steps the agent takes are exactly
the segments and events of the flat list, whatever the states are. The proof
needs one state to exist; `DistState` (S1.5) has one. -/
theorem AgentProgram.ofBody_steps (a : Agent) (body : List (Stmt ⊕ Emission))
    (l : List (Segment ⊕ Event)) :
    (AgentProgram.ofBody a).Steps body l ↔ l = slice a body := by
  obtain ⟨code,rfl⟩|⟨code,e,rest,rfl⟩ := first_event body
  · obtain ⟨head,tail⟩ := body_prefix code []
    simp at head tail
    rw [slice_noSync]
    constructor
    · intro steps
      cases steps with
      | finish => simp [ofBody,head]
      | emitGroup h _ _ => simp [ofBody,tail] at h
    · rintro rfl
      have done_ := Steps.finish (prog := ofBody a) (p := code.map Sum.inl)
        (σ := DistState.single default) (by simp [ofBody,tail])
      simpa [ofBody,head] using done_
  · obtain ⟨head,tail⟩ := body_prefix code (.inr e :: rest)
    simp at head tail
    rw [slice_sync]
    constructor
    · intro steps
      cases steps with
      | finish h => simp [ofBody] at h
      | emitGroup h _ next =>
        simp [ofBody] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        simp [ofBody,(ofBody_steps a rest _).mp next]
    · rintro rfl
      have next := (ofBody_steps a rest _).mpr rfl
      have more := Steps.emitGroup (prog := ofBody a) (p := code.map Sum.inl ++ .inr e :: rest)
        (σ := DistState.single default) (e := e) (es := []) (k := fun _ => rest) (vs := [none])
        (by simp [ofBody]) rfl next
      simpa [ofBody,head] using more
termination_by body.length
decreasing_by all_goals subst body; simp; omega

/-! ## Bridge to the upstream execution (S3.4) -/

/-- Signed (#43, part 2). Proved by S3.4. A kernel with no synchronization point
takes one step: it runs the upstream `exec` on the block state of the CTA,
writes the result back and finishes. `body` is the body of the instance that
CTA `c` runs; `hbody` says that its statements are those of the upstream
kernel `k`, and `hsync` that it holds no event. -/
theorem exec_noSync_eq_exec (c : Cta) (k : Kernel) (body : List (Stmt ⊕ Emission))
    (hbody : body.filterMap Sum.getLeft? = k.body) (hsync : ∀ e, Sum.inr e ∉ body)
    (σ σ' : DistState) (n : Next (List (Stmt ⊕ Emission))) :
    (AgentProgram.ofBody (.cta c)).Step body σ σ' n ↔
      (exec k (σ.block c.rank c.pid)).map (σ.setBlock c.rank c.pid) = some σ' ∧
        n = .finish := sorry

end VeriTile.Dist

namespace VeriTile.Dist.DistState

open VeriTile.Triton (BlockState)

theorem view_eq_subView (σ : DistState) (a : Agent) : σ.view a = σ.subView a := by
  cases a <;> rfl

theorem setView_eq_setSubView (σ : DistState) (a : Agent) (b : BlockState) :
    σ.setView a b = σ.setSubView a b := by cases a <;> rfl

theorem setView_view (σ : DistState) (a : Agent) : σ.setView a (σ.view a) = σ := by
  simpa [setView_eq_setSubView, view_eq_subView] using σ.setSubView_subView a

theorem view_setView {a : Agent} {c : Cta} (ha : a.cta? = some c) (σ : DistState) (b : BlockState)
    (hp : b.pids = DistState.programIds c.pid) (hu : b.undef = (σ.context a).undef)
    (hg : b.numPids = (σ.context a).numPids) : (σ.setView a b).view a = b := by
  rw [setView_eq_setSubView, view_eq_subView, DistState.subView_setSubView _ ha]
  rw [← hp, ← hu, ← hg]

/-- A write leaves another agent's local part unchanged, including child
and enclosing agents when the caller and reader differ. -/
theorem sameLocal_setView_ne (σ : DistState) {w r : Agent} (hne : r ≠ w) (b : BlockState) :
    DistState.SameLocal r σ (σ.setView w b) := by
  rw [setView_eq_setSubView]
  unfold DistState.SameLocal
  simp only [view_eq_subView]
  cases r with
  | rank => rfl
  | _ =>
    apply BlockState.ext
    · intros; rfl
    · intros; change (σ.context _).regs _ _ _ = ((σ.setSubView w b).context _).regs _ _ _
      rw [DistState.context_setSubView_ne _ hne]
    · intros; rfl
    · intros; change (σ.context _).undef _ _ = ((σ.setSubView w b).context _).undef _ _
      rw [DistState.context_setSubView_ne _ hne]
    · intros; change (σ.context _).numPids _ = ((σ.setSubView w b).context _).numPids _
      rw [DistState.context_setSubView_ne _ hne]

theorem sameLocal_putCell (σ : DistState) (p : Addr) (v : VeriTile.Triton.MemCell) (a : Agent) :
    SameLocal a σ (σ.putCell p v) := by cases a <;> rfl

/-- A real upstream segment result automatically meets the metadata conditions of
view readback, for a CTA, group or thread. -/
theorem view_setView_after_stepStmts {a : Agent} {c : Cta} (ha : a.cta? = some c)
    (σ : DistState) (code : List VeriTile.Triton.Stmt) {b : BlockState}
    (hrun : VeriTile.Triton.stepStmts code (σ.view a) = some b) : (σ.setView a b).view a = b := by
  have hm := stepStmts_metadata code hrun
  rw [view_eq_subView] at hm
  have he : metadata (σ.subView a) = (programIds c.pid,(σ.context a).undef,(σ.context a).numPids) := by
    cases a <;> simp_all [Agent.cta?,subView,metadata]
    all_goals exact ⟨rfl,rfl,rfl⟩
  obtain ⟨hp,hrest⟩ := Prod.mk.inj (hm.trans he)
  obtain ⟨hu,hg⟩ := Prod.mk.inj hrest
  exact view_setView ha σ b hp hu hg

end VeriTile.Dist.DistState
