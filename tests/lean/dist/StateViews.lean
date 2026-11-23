/- S1.5/S1.6 exercise the signed staging views on the concrete state. -/
import VeriTile.Staging.Dist.SegmentSpec
import Mathlib.Tactic.DeriveCountable
import Mathlib.Logic.Denumerable
import Mathlib.Data.Fintype.EquivFin

namespace VeriTile.Dist.StateTests

open VeriTile.Triton (BlockState MemCell Region RegionName)

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

/-- The two CTAs see one rank-global cell even when they use different aliases. -/
example (σ : DistState) (r : Rank) (i j : List Nat) (n : RegionName) (k : Nat)
    (ha : σ.layout.allocated (.global r) n) :
    let p : Addr := ⟨.global r, n, k⟩
    let c : Cta := ⟨r, i⟩
    let d : Cta := ⟨r, j⟩
    (σ.view (.cta c)).mem (σ.layout.name (.cta c) p ⟨ha, trivial, Or.inl rfl⟩) k =
      (σ.view (.cta d)).mem (σ.layout.name (.cta d) p ⟨ha, trivial, Or.inl rfl⟩) k := by
  dsimp only
  simp only [view_eq_subView]
  exact (σ.subView_mem_visible rfl _ _).trans (σ.subView_mem_visible rfl _ _).symm

/-- Two CTAs of a rank and two threads distinguished only by group never
share a register store. The stronger frame preserves all local metadata. -/
example (σ : DistState) (b : BlockState) :
    (σ.setView (.cta ⟨0, [0]⟩) b).context (.cta ⟨0, [1]⟩) = σ.context (.cta ⟨0, [1]⟩) ∧
    (σ.setView (.thread ⟨0, [0]⟩ 0 0) b).context (.thread ⟨0, [0]⟩ 1 0) =
      σ.context (.thread ⟨0, [0]⟩ 1 0) :=
  by
    simp only [setView_eq_setSubView]
    constructor <;> apply DistState.context_setSubView_ne <;> decide

/-- Build a total layout allocating every physical region, with a bijection
for each upstream ABI. The witness uses abstract aliases; the cell and the
two thread IDs in the actual write/read test below are concrete. -/
private def allRegions (a : Agent) :=
  {q : Space × RegionName // true = true ∧ AccessibleAt (fun _ => true) a ⟨q.1, q.2, 0⟩}

private instance : Countable Char := Function.Injective.countable (f := Char.toNat) (by
  intro a b h
  exact Char.ext (UInt32.toNat_inj.mp h))

private instance : Countable RegionName := Function.Injective.countable
  (f := fun n : RegionName => n.name.toList) (fun x y h => by
    cases x; cases y; exact congrArg Region.mk (String.toList_injective h))

deriving instance Countable for Cta, Space

private instance : Infinite RegionName :=
  Infinite.of_injective (fun s : String => (⟨s⟩ : RegionName)) (fun _ _ h => congrArg Region.name h)

private noncomputable def sharedState : DistState :=
  { DistState.single default with
    layout := {
      symmetric := fun _ => true
      allocated := fun _ _ => true
      names := fun a => by
        letI : Countable (allRegions a) := inferInstanceAs (Countable (Subtype _))
        letI : Infinite (allRegions a) := Infinite.of_injective
          (fun n : RegionName => (⟨(.global a.rankOf, n), rfl, trivial, Or.inl rfl⟩ : allRegions a))
          (fun _ _ h => congrArg (fun q : allRegions a => q.val.2) h)
        exact (nonempty_equiv_of_countable (α := RegionName) (β := allRegions a)).some } }

/-- The first thread writes a real shared address. The second thread observes
the new value before its own unguarded write. Data-race classification is S4. -/
example (v : MemCell) :
    let c : Cta := ⟨0, [0]⟩
    let w := Agent.thread c 0 0
    let r := Agent.thread c 0 1
    let p : Addr := ⟨.shared c, "scratch", 0⟩
    let b := (sharedState.view w).writeCell
      (sharedState.layout.name w p ⟨rfl, rfl, trivial⟩) 0 v
    ((sharedState.setView w b).view r).mem (sharedState.layout.name r p ⟨rfl, rfl, trivial⟩) 0 = v := by
  dsimp only
  rw [setView_eq_setSubView, view_eq_subView, DistState.subView_mem_after_write _ rfl rfl _ _ _ _]
  · simp [BlockState.writeCell]
  · exact ⟨rfl, rfl, trivial⟩

/-! A variable ABI contradicts the signed agreement premise. The same one-store
program runs in states with the same cells and local fields, but two names are
exchanged in one ABI. No write footprint can satisfy both soundness clauses. -/
namespace LayoutCounterexample

open VeriTile.Triton (Stmt stepStmts)

private def c : Cta := ⟨0, [0]⟩
private def x : Addr := ⟨.global 0, "x", 0⟩
private noncomputable def left : DistState := DistState.single default
private noncomputable def right : DistState :=
  { left with layout := { left.layout with names := fun a =>
      (Equiv.swap ("x" : RegionName) "y").trans (left.layout.names a) } }

private def code : List Stmt :=
  [.store .nat [] (.region ⟨"x"⟩ (.constNat 0)) (.constNat 1) .none]

private def result (s : DistState) : DistState :=
  s.setBlock 0 [0] ((s.block 0 [0]).writeMemTyped .nat ⟨"x"⟩ 0 1)

private theorem store_runs (s : DistState) :
    (stepStmts code (s.block 0 [0])).map (s.setBlock 0 [0]) = some (result s) := by
  simp [code, stepStmts, VeriTile.Triton.stepStmt, Region.cast,
    VeriTile.Triton.TileShape.allIndices, result]

/-- The run equation and the signed soundness obligation for this CTA cannot
both hold for this candidate state design. This proof uses neither staging
theorem and needs only two upstream names and one scalar store. -/
theorem no_sound_segment (seg : Segment) (ha : seg.agent = .cta c)
    (run : ∀ s, seg.run s = (stepStmts code (s.block 0 [0])).map (s.setBlock 0 [0])) :
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
