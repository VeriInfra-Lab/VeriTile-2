/-
VeriTile.Staging.Dist.SegmentSpec

Segment interface, bridge statements and per-agent continuation of the Dist
line, drafted by ticket S3.1 (#43) and revised to the user's decisions of
2026-11-13. Nothing in this file is signed.

An agent runs sequential code between synchronization or communication
points. A segment is one such piece of code, seen as a transformer of the
distributed state together with the cells it may read and may write. The
program of an agent is run step by step: from a program state the agent runs
the segment up to its next event, emits that event and continues, or finishes.

The file has two parts, signed separately. No declaration of part 1 mentions a
declaration of part 2 or an `Event`.

- Part 1: `Segment`, `Segment.FootprintSound`, and the bridge for one segment
  made from upstream statements.
- Part 2: `Next`, `AgentProgram`, the step relation `AgentProgram.Step`, the
  flat body as one program (`AgentProgram.ofBody`, `slice`) and the statements
  about them.

Each theorem is a statement with `sorry`. The ticket named in a docstring moves
that declaration to `VeriTile/Dist/` under the same name and type, proves it
and deletes it here in the same change. `EventControlFlow.md` below is
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

By a decision of the same day a spin loop with an empty body is one blocking
event. It is an event of the step relation, not a loop of segments.

New choices, not decided. Each was needed to make the file elaborate; the file
takes the option marked "taken". The pull request of this revision gives the
evidence.

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
    reader sees which program a flat body is. `slice` stays a stub, as drafted.

The event type is `Event` of `VeriTile/Staging/Dist/EventSpec.lean`, signed
on 2026-11-13; it is no longer a parameter.
-/
import VeriTile.Triton.Semantics.Step
import VeriTile.Dist.Agent
import VeriTile.Staging.Dist.LocationSpec
import VeriTile.Staging.Dist.EventSpec

namespace VeriTile.Dist

open VeriTile.Triton (BlockState MemCell Stmt Kernel stepStmts exec)

/-! # Part 1: segments, footprint soundness, the bridge for one segment -/

/-! ## State access that the statements need (stubs for S1.5 and S1.6) -/

/-- UNSIGNED stub (S1.5). Part 1. The content of cell `p` in the distributed
state. -/
noncomputable opaque DistState.cell : DistState → Addr → MemCell := fun _ _ => MemCell.real 0

/-- UNSIGNED stub (S1.5). Part 1. `σ.setBlock r pid b` writes the upstream
state `b` back as the state of the CTA with program ids `pid` on rank `r`: the
memory that this CTA can reach and its registers. It is the inverse direction
of `DistState.block`. -/
opaque DistState.setBlock : DistState → Rank → List Nat → BlockState → DistState :=
  fun σ _ _ _ => σ

/-- UNSIGNED stub (S1.6). Part 1. The upstream state that a group or a thread
`a` executes on: the memory that `a` can reach and the registers that are its
own. A `local` cell is reached by its thread alone; a `shared` cell by every
agent of the CTA.

Laws that S1.6 owes, with `view` and `setView` below: reading back what was
written and writing back what was read; how `cell` relates to the memory of a
view; that the program ids are those of the CTA; that `setView a` changes only
cells that `a` can reach, the registers of `a` and of the agents inside `a`,
and no synchronization object; that two agents neither of which lies within
the other have separate registers, also two thread agents that differ in the
group only. -/
opaque DistState.subView : DistState → Agent → BlockState

/-- UNSIGNED stub (S1.6). Part 1. Writes the upstream state `b` back as the
state of the group or thread `a`. The inverse direction of
`DistState.subView`. -/
opaque DistState.setSubView : DistState → Agent → BlockState → DistState := fun σ _ _ => σ

/-- UNSIGNED. Part 1. The upstream state that agent `a` executes on. For a CTA
it is `DistState.block`. A whole rank runs no segment. -/
noncomputable def DistState.view (σ : DistState) : Agent → BlockState
  | .rank _ => default
  | .cta c => σ.block c.rank c.pid
  | a => σ.subView a

/-- UNSIGNED. Part 1. Writes the upstream state `b` back as the state of
agent `a`. For a CTA it is `DistState.setBlock`. -/
def DistState.setView (σ : DistState) : Agent → BlockState → DistState
  | .rank _, _ => σ
  | .cta c, b => σ.setBlock c.rank c.pid b
  | a, b => σ.setSubView a b

/-- UNSIGNED. Part 1. The two states hold the same content in every cell of
`P`. -/
def DistState.AgreesOn (P : Set Addr) (σ₁ σ₂ : DistState) : Prop :=
  ∀ p ∈ P, σ₁.cell p = σ₂.cell p

/-- UNSIGNED. Part 1. The two states give agent `a` the same local state: the
same registers, program ids, grid dimensions and unspecified values. Memory is
not compared, also not the `local` cells of a thread: cells are compared by
`DistState.AgreesOn`. -/
def DistState.SameLocal (a : Agent) (σ₁ σ₂ : DistState) : Prop :=
  { σ₁.view a with mem := (σ₂.view a).mem } = σ₂.view a

/-! ## Segments and footprint soundness (S3.2) -/

/-- UNSIGNED. Part 1. Owner: S3.2. Sequential code between two synchronization
or communication points. `agent` is the agent that runs it: a CTA, or a group
or a thread of a CTA. `run` is its effect on the distributed state; `none` is
a failed execution. `reads σ` and `writes σ` are the cells it may read and may
write when it starts in `σ`. -/
structure Segment where
  agent : Agent
  run : DistState → Option DistState
  reads : DistState → Set Addr
  writes : DistState → Set Addr

/-- UNSIGNED. Part 1. Owner: S3.2. The footprints of a segment are sound.

`frame`: a run changes no cell outside the write footprint.

`confined`: a run changes the distributed state only by writing back the state
of its own agent, so it changes no synchronization object; and it leaves the
local state of every agent that neither contains its agent nor lies within it
as it was: another CTA, and another group or thread of the same CTA.

`reads_determine`: two states that agree on the read footprint and give the
agent the same local state have the same footprints, and if the run succeeds
in one it succeeds in the other, with results that agree on the write
footprint and on the local state. A written cell whose final content depends
on its old content therefore has to be in the read footprint too. -/
structure Segment.FootprintSound (seg : Segment) : Prop where
  frame : ∀ σ σ', seg.run σ = some σ' → ∀ p, p ∉ seg.writes σ → σ'.cell p = σ.cell p
  confined : ∀ σ σ', seg.run σ = some σ' →
    (∃ b, σ' = σ.setView seg.agent b) ∧
      ∀ a : Agent, ¬ a.within seg.agent → ¬ seg.agent.within a → DistState.SameLocal a σ σ'
  reads_determine : ∀ σ₁ σ₂, DistState.AgreesOn (seg.reads σ₁) σ₁ σ₂ →
    DistState.SameLocal seg.agent σ₁ σ₂ →
      seg.reads σ₂ = seg.reads σ₁ ∧ seg.writes σ₂ = seg.writes σ₁ ∧
        ∀ σ₁', seg.run σ₁ = some σ₁' →
          ∃ σ₂', seg.run σ₂ = some σ₂' ∧ DistState.AgreesOn (seg.writes σ₁) σ₁' σ₂' ∧
            DistState.SameLocal seg.agent σ₁' σ₂'

/-- UNSIGNED. Part 1. Proved by S3.2. The frame lemma: a segment with sound
footprints leaves every cell outside its write footprint as it was. -/
theorem Segment.frame {seg : Segment} (h : seg.FootprintSound) {σ σ' : DistState}
    (hrun : seg.run σ = some σ') {p : Addr} (hp : p ∉ seg.writes σ) :
    σ'.cell p = σ.cell p := sorry

/-! ## Segments of upstream statements (S3.3) -/

/-- UNSIGNED stub (S3.3). Part 1. The segment that runs the upstream
statements `code` as agent `a`, with the footprints computed from the
statements. -/
opaque Segment.ofStmts (a : Agent) (code : List Stmt) : Segment :=
  ⟨a, fun _ => none, fun _ => ∅, fun _ => ∅⟩

/-- UNSIGNED. Part 1. Proved by S3.3. A segment made from statements is run by
the agent it was made for. -/
theorem Segment.ofStmts_agent (a : Agent) (code : List Stmt) :
    (Segment.ofStmts a code).agent = a := sorry

/-- UNSIGNED. Part 1. Proved by S3.3. The bridge for one segment of a CTA:
running it on the distributed state is running the upstream `stepStmts` of its
statements on the block state of the CTA and writing the result back. It fails
exactly when the upstream execution fails. -/
theorem Segment.ofStmts_run (c : Cta) (code : List Stmt) (σ : DistState) :
    (Segment.ofStmts (.cta c) code).run σ =
      (stepStmts code (σ.block c.rank c.pid)).map (σ.setBlock c.rank c.pid) := sorry

/-- UNSIGNED. Part 1. Proved by S3.3. The same equation for every agent, on
the projection of the agent. For a group or a thread it is what running
upstream statements as that agent means, and it says nothing before S1.6
defines the projection. Not claimed: that the runs of the threads of a CTA
compose to the upstream execution on the block state of the CTA. -/
theorem Segment.ofStmts_run_view (a : Agent) (code : List Stmt) (σ : DistState) :
    (Segment.ofStmts a code).run σ = (stepStmts code (σ.view a)).map (σ.setView a) := sorry

/-- UNSIGNED. Part 1. Proved by S3.3. The footprints computed from the
statements of a CTA are sound. Nothing is claimed here for a group or a
thread: it needs the laws that S1.6 gives the projection. -/
theorem Segment.ofStmts_footprintSound (c : Cta) (code : List Stmt) :
    (Segment.ofStmts (.cta c) code).FootprintSound := sorry

/-! # Part 2: the continuation of an agent -/

/-! ## Programs and steps (S3.3) -/

/-- UNSIGNED. Part 2. Owner: S3.3. What follows the segment of a step, for an
agent whose program states have type `P`. `finish`: the agent has ended.
`emit e k`: the agent performs the event `e`, which may block, and continues
with the program state `k v`, where `v` is the value that the event read:
the content a load or an update found, `none` for an event that reads
nothing. -/
inductive Next (P : Type) where
  | finish
  | emit (e : Event) (k : Option MemCell → P)

/-- UNSIGNED. Part 2. Owner: S3.3. The program of one agent, cut at its
events. `segment p` is the code from program state `p` up to the next event,
or up to the end. `next p σ` is what follows that segment when it starts in
`σ`: the event with its evaluated arguments, and the program state after it.
A loop whose body holds an event is a program state that `next` returns
again; how often depends on the states and on the values read. -/
structure AgentProgram (P : Type) where
  segment : P → Segment
  next : P → DistState → Next P

/-- UNSIGNED. Part 2. Owner: S3.3. One step of an agent: from program state
`p` and state `σ` it runs the segment up to its next event, reaches `σ'`, and
then finishes or emits that event and continues, as `n` says. The effect of
the event and the interleaving with other agents belong to S4. -/
def AgentProgram.Step {P : Type} (prog : AgentProgram P) (p : P) (σ σ' : DistState)
    (n : Next P) : Prop :=
  (prog.segment p).run σ = some σ' ∧ prog.next p σ = n

/-- UNSIGNED. Part 2. Owner: S3.3. `prog.Steps p l`: started in program state
`p`, the agent can take the steps `l` for some states and some values read at
its events: the segments it runs and the events it emits, in order, down to
the end of the program. The runs are not required to succeed. -/
inductive AgentProgram.Steps {P : Type} (prog : AgentProgram P) :
    P → List (Segment ⊕ Event) → Prop where
  | finish {p : P} {σ : DistState} (h : prog.next p σ = .finish) :
      prog.Steps p [Sum.inl (prog.segment p)]
  | emit {p : P} {σ : DistState} {e : Event} {k : Option MemCell → P} {v : Option MemCell}
      {l : List (Segment ⊕ Event)} (h : prog.next p σ = .emit e k) (rest : prog.Steps (k v) l) :
      prog.Steps p (Sum.inl (prog.segment p) :: Sum.inr e :: l)

/-- UNSIGNED. Part 2. Proved by S3.3. The segment part of a step is
deterministic: a program state and a state fix the state reached, the event
and the continuation. -/
theorem AgentProgram.Step.deterministic {P : Type} {prog : AgentProgram P} {p : P}
    {σ σ₁ σ₂ : DistState} {n₁ n₂ : Next P} (h₁ : prog.Step p σ σ₁ n₁)
    (h₂ : prog.Step p σ σ₂ n₂) : σ₁ = σ₂ ∧ n₁ = n₂ := sorry

/-- A loop whose body holds an event, which no flat body expresses: the agent
runs `seg`, emits `e`, and goes round again exactly when the event read a
value. It can take three steps or five. -/
example (seg : Segment) (e : Event) (σ : DistState) (v : MemCell) :
    let prog : AgentProgram Bool :=
      ⟨fun _ => seg, fun p _ => if p then .emit e fun r => r.isSome else .finish⟩
    prog.Steps true [.inl seg, .inr e, .inl seg] ∧
      prog.Steps true [.inl seg, .inr e, .inl seg, .inr e, .inl seg] :=
  ⟨.emit (σ := σ) (v := none) rfl (.finish (σ := σ) rfl),
    .emit (σ := σ) (v := some v) rfl (.emit (σ := σ) (v := none) rfl (.finish (σ := σ) rfl))⟩

/-! ## The flat body as a program (S3.3) -/

/-- UNSIGNED. Part 2. Owner: S3.3. The program of agent `a` whose program
state is what is left of a flat body: upstream statements and, at each
synchronization or communication point, the event performed there. A step
runs the statements before the first event, emits that event and continues
with the body after it, whatever the event read. -/
def AgentProgram.ofBody (a : Agent) : AgentProgram (List (Stmt ⊕ Event)) where
  segment body := Segment.ofStmts a ((body.takeWhile Sum.isLeft).filterMap Sum.getLeft?)
  next body _ :=
    match body.dropWhile Sum.isLeft with
    | Sum.inr e :: rest => .emit e fun _ => rest
    | _ => .finish

/-- UNSIGNED. Part 2. Proved by S3.3. A step with no event left is the
upstream execution of the rest on the projection of the agent, written back;
then the agent has finished. -/
theorem AgentProgram.ofBody_step_noSync (a : Agent) (code : List Stmt) (σ σ' : DistState)
    (n : Next (List (Stmt ⊕ Event))) :
    (AgentProgram.ofBody a).Step (code.map Sum.inl) σ σ' n ↔
      (stepStmts code (σ.view a)).map (σ.setView a) = some σ' ∧ n = .finish := sorry

/-- UNSIGNED stub (S3.3). Part 2. Slicing of a flat body of agent `a`. The
result lists, in program order, the segments between the events and the
events. It is fixed before execution. -/
opaque slice (a : Agent) (body : List (Stmt ⊕ Event)) : List (Segment ⊕ Event)

/-- UNSIGNED. Part 2. Proved by S3.3. A body with no event is one segment. -/
theorem slice_noSync (a : Agent) (code : List Stmt) :
    slice a (code.map Sum.inl) = [Sum.inl (Segment.ofStmts a code)] := sorry

/-- UNSIGNED. Part 2. Proved by S3.3. Slicing cuts at the first event: the
statements before it are one segment, and the rest of the body is sliced in
the same way. -/
theorem slice_sync (a : Agent) (code : List Stmt) (e : Event) (rest : List (Stmt ⊕ Event)) :
    slice a (code.map Sum.inl ++ Sum.inr e :: rest) =
      Sum.inl (Segment.ofStmts a code) :: Sum.inr e :: slice a rest := sorry

/-- UNSIGNED. Part 2. Proved by S3.3. The derived lemma: for a flat body, a
program with no loop around an event, the steps the agent takes are exactly
the segments and events of the flat list, whatever the states are. The proof
needs one state to exist; `DistState` is opaque until S1.5 defines it. -/
theorem AgentProgram.ofBody_steps (a : Agent) (body : List (Stmt ⊕ Event))
    (l : List (Segment ⊕ Event)) :
    (AgentProgram.ofBody a).Steps body l ↔ l = slice a body := sorry

/-! ## Bridge to the upstream execution (S3.4) -/

/-- UNSIGNED. Part 2. Proved by S3.4. A kernel with no synchronization point
takes one step: it runs the upstream `exec` on the block state of the CTA,
writes the result back and finishes. `body` is the body of the instance that
CTA `c` runs; `hbody` says that its statements are those of the upstream
kernel `k`, and `hsync` that it holds no event. -/
theorem exec_noSync_eq_exec (c : Cta) (k : Kernel) (body : List (Stmt ⊕ Event))
    (hbody : body.filterMap Sum.getLeft? = k.body) (hsync : ∀ e, Sum.inr e ∉ body)
    (σ σ' : DistState) (n : Next (List (Stmt ⊕ Event))) :
    (AgentProgram.ofBody (.cta c)).Step body σ σ' n ↔
      (exec k (σ.block c.rank c.pid)).map (σ.setBlock c.rank c.pid) = some σ' ∧
        n = .finish := sorry

end VeriTile.Dist
