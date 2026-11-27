/- S1.5/S1.6 exercise the signed staging views on the concrete state. -/
import VeriTile.Staging.Dist.SegmentSpec

namespace VeriTile.Dist.StateTests

open VeriTile.Triton (BlockState MemCell Region RegionName)

open DistState

/-- Running an empty CTA segment still projects the upstream block and writes
it back. All three soundness obligations are discharged for this segment. -/
private noncomputable def emptySegment (c : Cta) : Segment where
  agent := .cta c
  run σ := some (σ.setView (.cta c) (σ.view (.cta c)))
  reads _ := ∅
  writes _ := ∅

private theorem empty_sound (c : Cta) : (emptySegment c).FootprintSound := by
  constructor
  · intro σ σ' h p _
    simpa [emptySegment, setView_view] using congrArg (Option.map (·.cell p)) h.symm
  · intro σ σ' h
    have e : σ = σ' := by simpa [emptySegment, setView_view] using h
    subst σ'
    exact ⟨⟨σ.view (.cta c), (setView_view _ _).symm⟩, fun _ _ _ => rfl⟩
  · intro s t _ hl
    refine ⟨rfl, rfl, ?_⟩
    intro s' hs
    have e : s = s' := by simpa [emptySegment, setView_view] using hs
    subst s'
    exact ⟨t, by simp [emptySegment, setView_view], fun _ h => False.elim h, hl⟩

/-- Direct instance of the signed frame statement; uses the proved field
rather than the staging theorem whose proof belongs to S3.2. -/
example (c : Cta) {s t : DistState} (h : (emptySegment c).run s = some t) (p : Addr) :
    t.cell p = s.cell p := (empty_sound c).frame _ _ h _ (by simp [emptySegment])

/-- Two CTAs of a rank and two threads distinguished only by group never
share a register store. The stronger frame preserves all local metadata. -/
example (σ : DistState) (b : BlockState) :
    (σ.setView (.cta ⟨0, [0]⟩) b).context (.cta ⟨0, [1]⟩) = σ.context (.cta ⟨0, [1]⟩) ∧
    (σ.setView (.thread ⟨0, [0]⟩ 0 0) b).context (.thread ⟨0, [0]⟩ 1 0) =
      σ.context (.thread ⟨0, [0]⟩ 1 0) :=
  by
    simp only [setView_eq_setSubView]
    constructor <;> apply DistState.context_setSubView_ne <;> decide

private noncomputable def sharedState := DistState.single default

/-- Sibling threads see one shared cell. Distinct spaces and remote ranks have
distinct canonical names, including when the region name itself starts in '@'. -/
example (v : MemCell) :
    let c : Cta := ⟨0,[0]⟩
    let w := Agent.thread c 0 0
    let r := Agent.thread c 0 1
    let p : Addr := ⟨.shared c,"scratch",0⟩
    let b := (sharedState.view w).writeCell (ViewName.ofSpace w p.space p.region) 0 v
    ((sharedState.setView w b).view r).mem (ViewName.ofSpace r p.space p.region) 0 = v := by
  dsimp only
  rw [setView_eq_setSubView,view_eq_subView]
  exact (DistState.subView_mem_after_write sharedState (w := .thread ⟨0,[0]⟩ 0 0)
    (r := .thread ⟨0,[0]⟩ 0 1) rfl rfl _ ⟨.shared ⟨0,[0]⟩,"scratch",0⟩ rfl rfl).trans
    (by simp [ViewName.name,BlockState.writeCell])

example : ViewName.address (.cta ⟨2,[0]⟩) "buffer" 7 = ⟨.global 2,"buffer",7⟩ := rfl
example (a : Agent) (r : Rank) (n : RegionName) (i : Nat) :
    ViewName.address a (ViewName.ofSpace a (.global r) n) i = ⟨.global r,n,i⟩ :=
  ViewName.address_name a _ (ViewName.visible_global a r n i)

-- The reserved prefix is also valid in physical region names. An own-rank
-- alias is precisely the canonical home spelling; it cannot shadow a peer.
example :
    let a := Agent.cta ⟨2,[0]⟩
    ViewName.ofSpace a (.global 2) "@x" ≠ ViewName.ofSpace a (.global 3) "@x" := by
  decide

example (σ : DistState) (oracle) (P : Set Agent) (grid : Rank → List Nat)
    (hv : σ.LaunchValid grid oracle P) (h : Agent.cta ⟨0,[0,0]⟩ ∈ P) :
    (grid 0).length ≠ 1 := by
  have hlen := (hv _ h _ rfl).2.1
  change 2 = (grid 0).length at hlen
  omega

/-! A variable ABI contradicts the signed agreement premise. The same one-store
program runs in states with the same cells and local fields, but two names are
exchanged in one ABI. No write footprint can satisfy both soundness clauses. -/
namespace LayoutCounterexample

open VeriTile.Triton (Stmt stepStmts)

private def c : Cta := ⟨0, [0]⟩
private def x : Addr := ⟨.global 0, "x", 0⟩
private noncomputable def left : DistState := DistState.single default
private noncomputable def right : DistState :=
  { left with numRanks := 2 }

/-- A rejected design: two states bind names differently although every physical
cell and local field agrees. Using numRanks as the hidden selector exhibits
the same defect as an additional per-state layout field. -/
private def badName (s : DistState) : RegionName → RegionName :=
  if s.numRanks = 1 then id else (Equiv.swap ("x" : RegionName) "y").toFun

private def badBlock (s : DistState) : BlockState :=
  { s.block 0 [0] with mem := fun n i => (s.block 0 [0]).mem (badName s n) i }

private def badSetBlock (s : DistState) (b : BlockState) :=
  s.setBlock 0 [0] { b with mem := fun n i => b.mem (badName s n) i }

private def code : List Stmt :=
  [.store .nat [] (.region ⟨"x"⟩ (.constNat 0)) (.constNat 1) .none]

private def result (s : DistState) : DistState :=
  badSetBlock s ((badBlock s).writeMemTyped .nat ⟨"x"⟩ 0 1)

private theorem store_runs (s : DistState) :
    (stepStmts code (badBlock s)).map (badSetBlock s) = some (result s) := by
  simp [code, stepStmts, VeriTile.Triton.stepStmt, Region.cast,
    VeriTile.Triton.TileShape.allIndices, result]

-- With the fixed decoder the same store reaches physical x in both states.
example (s : DistState) :
    stepStmts code (s.block 0 [0]) = some ((s.block 0 [0]).writeMemTyped .nat ⟨"x"⟩ 0 1) := by
  simp [code, stepStmts, VeriTile.Triton.stepStmt, Region.cast,
    VeriTile.Triton.TileShape.allIndices]

example : ((left.setBlock 0 [0] ((left.block 0 [0]).writeMemTyped .nat ⟨"x"⟩ 0 1)).cell x).1 =
    .nat := rfl

example : ((right.setBlock 0 [0] ((right.block 0 [0]).writeMemTyped .nat ⟨"x"⟩ 0 1)).cell x).1 =
    .nat := rfl

/-- The run equation and the signed soundness obligation for this CTA cannot
both hold for this candidate state design. This proof uses neither staging
theorem and needs only two upstream names and one scalar store. -/
theorem no_sound_segment (seg : Segment) (ha : seg.agent = .cta c)
    (run : ∀ s, seg.run s = (stepStmts code (badBlock s)).map (badSetBlock s)) :
    ¬ seg.FootprintSound := by
  intro sound
  have lrun := (run left).trans (store_runs left)
  have rrun := (run right).trans (store_runs right)
  have xleft : ((result left).cell x).1 = .nat := rfl
  have xright : ((result right).cell x).1 = .real := rfl
  have xinitial : (left.cell x).1 = .real := rfl
  have hx : x ∈ seg.writes left := by
    by_contra hx
    have bad := congrArg Sigma.fst (sound.frame _ _ lrun x hx)
    rw [xleft, xinitial] at bad
    contradiction
  have hl : DistState.SameLocal seg.agent left right := by rw [ha]; rfl
  obtain ⟨_, _, transport⟩ := sound.reads_determine left right (fun _ _ => rfl) hl
  obtain ⟨t, ht, hc, _⟩ := transport _ lrun
  have et := Option.some.inj (ht.symm.trans rrun)
  subst t
  have bad := congrArg Sigma.fst (hc x hx)
  rw [xleft, xright] at bad
  contradiction

end LayoutCounterexample
end VeriTile.Dist.StateTests
