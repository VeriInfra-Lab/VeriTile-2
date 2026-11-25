/-
VeriTile.Dist.Segment

Segments and footprint soundness (S3.2, #44): the agent views a segment runs
on, the structure `Segment`, the predicate `Segment.FootprintSound` and the
frame lemma `Segment.frame`. Signed as part 1 of
`VeriTile/Staging/Dist/SegmentSpec.lean` on 2026-11-23 and moved here under the
same names and types; the rest of that file imports this module.
-/
import VeriTile.Dist.State

namespace VeriTile.Dist

open VeriTile.Triton (BlockState)

/-! ## Agent views -/

/-- Signed. Part 1. The upstream state that agent `a` executes on. For a CTA
it is `DistState.block`. A whole rank runs no segment. -/
noncomputable def DistState.view (σ : DistState) : Agent → BlockState
  | .rank _ => default
  | .cta c => σ.block c.rank c.pid
  | a => σ.subView a

/-- Signed. Part 1. Writes the upstream state `b` back as the state of
agent `a`. For a CTA it is `DistState.setBlock`. -/
def DistState.setView (σ : DistState) : Agent → BlockState → DistState
  | .rank _, _ => σ
  | .cta c, b => σ.setBlock c.rank c.pid b
  | a, b => σ.setSubView a b

/-- Signed. Part 1. The two states hold the same content in every cell of
`P`. -/
def DistState.AgreesOn (P : Set Addr) (σ₁ σ₂ : DistState) : Prop :=
  ∀ p ∈ P, σ₁.cell p = σ₂.cell p

/-- Signed. Part 1. The two states give agent `a` the same local state: the
same registers, program ids, grid dimensions and unspecified values. Memory is
not compared, also not the `local` cells of a thread: cells are compared by
`DistState.AgreesOn`. -/
def DistState.SameLocal (a : Agent) (σ₁ σ₂ : DistState) : Prop :=
  { σ₁.view a with mem := (σ₂.view a).mem } = σ₂.view a

/-! ## Segments and footprint soundness (S3.2) -/

/-- Signed. Part 1. Owner: S3.2. Sequential code between two synchronization
or communication points. `agent` is the agent that runs it: a CTA, or a group
or a thread of a CTA. `run` is its effect on the distributed state; `none` is
a failed execution. `reads σ` and `writes σ` are the cells it may read and may
write when it starts in `σ`. -/
structure Segment where
  agent : Agent
  run : DistState → Option DistState
  reads : DistState → Set Addr
  writes : DistState → Set Addr

/-- Signed. Part 1. Owner: S3.2. The footprints of a segment are sound.

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

/-- Signed. Part 1. Proved by S3.2. The frame lemma: a segment with sound
footprints leaves every cell outside its write footprint as it was. -/
theorem Segment.frame {seg : Segment} (h : seg.FootprintSound) {σ σ' : DistState}
    (hrun : seg.run σ = some σ') {p : Addr} (hp : p ∉ seg.writes σ) :
    σ'.cell p = σ.cell p :=
  h.frame σ σ' hrun p hp

end VeriTile.Dist
