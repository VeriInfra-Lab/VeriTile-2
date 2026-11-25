/- S3.2: a read footprint that leaves out a cell the segment reads fails
`FootprintSound`; the same segment with that cell declared satisfies it. -/
import VeriTile.Staging.Dist.SegmentSpec

namespace VeriTile.Dist.SegmentFootprintTests

open VeriTile.Triton (MemCell)
open Classical

private def c : Cta := ⟨0, []⟩
private def p : Addr := ⟨.shared c, "flag", 0⟩

/-- A CTA segment that branches on cell `p`: it succeeds without changing
anything when `p` holds the real 0 and fails otherwise. It writes nothing. -/
private noncomputable def guard (reads : Set Addr) : Segment where
  agent := .cta c
  run σ := if σ.cell p = .real 0 then some σ else none
  reads _ := reads
  writes _ := ∅

private theorem zero_ne_one : MemCell.real 0 ≠ MemCell.real 1 := by
  intro h
  have := Option.some.inj (eq_of_heq (Sigma.mk.inj h).2)
  norm_num at this

/-- Negative example: the read of `p` is not declared. Two states that differ
only at `p` agree on the empty read footprint and give the CTA the same local
state, yet the run succeeds in one and fails in the other. -/
theorem guard_unsound : ¬ (guard ∅).FootprintSound := by
  intro h
  let σ₀ := DistState.single default
  obtain ⟨-, -, hrun⟩ := h.reads_determine (σ₀.putCell p (.real 0)) (σ₀.putCell p (.real 1))
    (fun _ hq => hq.elim) rfl
  obtain ⟨σ₂', h₂, -⟩ := hrun (σ₀.putCell p (.real 0)) (by simp [guard])
  simp [guard, zero_ne_one.symm] at h₂

/-- Positive control: with `p` in the read footprint the same segment is sound. -/
theorem guard_sound : (guard {p}).FootprintSound where
  frame σ σ' h q _ := by
    simp only [guard] at h; split at h <;> simp_all
  confined σ σ' h := by
    simp only [guard] at h; split at h
    · cases h
      exact ⟨⟨σ.view (.cta c), (DistState.setView_view σ _).symm⟩, fun _ _ _ => rfl⟩
    · cases h
  reads_determine σ₁ σ₂ hagree hl := by
    refine ⟨rfl, rfl, fun σ₁' h => ?_⟩
    simp only [guard] at h ⊢; split at h
    · cases h
      rename_i h0
      refine ⟨σ₂, by rw [if_pos ((hagree p rfl).symm.trans h0)], fun _ hq => hq.elim, hl⟩
    · cases h

end VeriTile.Dist.SegmentFootprintTests
