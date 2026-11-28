import VeriTile.Dist.Segment

/-! Agent-relative region names and view laws for sliced segments (#45, #48). -/

namespace VeriTile.Dist.ViewName

/-- Translate an already-encoded CTA operand into the receiving agent's spelling
when building a sliced statement. The region and physical space come from the
source operand, including for names with leading tag characters. -/
def respellRegion (source target : Agent) (region : VeriTile.Triton.RegionName) :=
  let p := address source region 0
  ofSpace target p.space p.region

theorem address_respellRegion (source target : Agent) (region : VeriTile.Triton.RegionName)
    (i : Nat) (visible : Visible target (address source region i)) :
    address target (respellRegion source target region) i = address source region i := by
  simpa [respellRegion, name, address] using
    address_name target (address source region i) visible

end VeriTile.Dist.ViewName

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
