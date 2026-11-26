import tests.lean.dist.UnguardedShared

/-! # S1.7 location regressions

Each rejected case has an admitted control. The shared-store race witnesses reuse
S1.6's completed executions rather than constructing synthetic histories. -/

namespace LocationRegression

open VeriTile.Dist
open VeriTile.Triton (RegionName)

private def c0 : Cta := ⟨0, [0]⟩
private def c1 : Cta := ⟨0, [1]⟩

-- S1.2: another running CTA does not extend the lifetime of an ended CTA.
example : ¬ (Space.shared c0).live (fun c _ => c = c1) :=
  Space.not_live_of_cta_ended rfl (fun _ => by decide)

example : (Space.shared c0).live (fun c _ => c = c0) := ⟨0, rfl⟩

-- The local lifetime ends when its own thread ends, even inside a live CTA.
example : ¬ (Space.local c0 0).live (fun c t => c = c0 ∧ t = 1) :=
  Space.not_live_local_of_thread_ended (by decide)

example : (Space.local c0 1).live (fun c t => c = c0 ∧ t = 1) := ⟨rfl, rfl⟩

-- S1.3: system scope, not GPU scope, covers another rank.
example : ¬ Scope.gpu.covers (.rank 0) (.rank 1) := by
  intro h
  have eq := Scope.covers_ne_rank_eq_sys h (by decide)
  cases eq

example : Scope.gpu.covers (.rank 0) (.rank 0) := by decide
example : Scope.sys.covers (.rank 0) (.rank 1) := by decide

-- S1.4: ownership of a CTA-shared object is required, not just the same rank.
example : ¬ Accessible (.cta c0) (.shared c1) :=
  fun h => (by decide : (Agent.cta c0).cta? ≠ some c1) (accessible_shared_iff.mp h)

example : Accessible (.cta c0) (.shared c0) := accessible_shared_iff.mpr rfl

-- S1.5: ordinary global storage has no symmetric counterpart on a peer;
-- a peer cannot access such a cell even though its space passes Accessible.
example (region : RegionName) : symmAt (fun _ => false) ⟨.global 0, region, 0⟩ 1 = none := rfl

example (region : RegionName) :
    symmAt (fun _ => true) ⟨.global 0, region, 0⟩ 1 = some ⟨.global 1, region, 0⟩ := rfl

example (region : RegionName) :
    ¬ AccessibleAt (fun _ => false) (.rank 0) ⟨.global 1, region, 0⟩ :=
  not_accessibleAt_of_remote_not_symm rfl (by decide) rfl

example (region : RegionName) :
    AccessibleAt (fun _ => true) (.rank 0) ⟨.global 1, region, 0⟩ :=
  accessibleAt_of_symmAt (p := ⟨.global 0, region, 0⟩) rfl

-- State/name-resolution regressions from S1.5: an own-rank spelling cannot
-- shadow its peer, and a launch cannot silently truncate/pad a CTA's pid list.
example :
    ViewName.ofSpace (.cta ⟨2, [0]⟩) (.global 2) "@x" ≠
      ViewName.ofSpace (.cta ⟨2, [0]⟩) (.global 3) "@x" := by decide

example (s : DistState) (oracle) (P : Set Agent) (grid : Rank → List Nat)
    (h : Agent.cta ⟨0, [0, 0]⟩ ∈ P) (arity : (grid 0).length = 1) :
    ¬ s.LaunchValid grid oracle P := by
  intro valid
  have hlen := (valid _ h _ rfl).2.1
  simp [arity] at hlen

-- S1.6: two threads run the unguarded region; only thread 0 passes tid == 0.
example : ThreadGuard.all.Runs 2 0 ∧ ThreadGuard.all.Runs 2 1 := by
  change (0 < 2 ∧ true = true) ∧ (1 < 2 ∧ true = true)
  decide
example : ∃! t, (ThreadGuard.tidEq 0).Runs 2 t :=
  ThreadGuard.existsUnique_runs_tidEq (by decide)
example : (ThreadGuard.tidEq 0).Runs 2 0 ∧ ¬ (ThreadGuard.tidEq 0).Runs 2 1 := by
  simp [ThreadGuard.Runs, ThreadGuard.tidEq]

private def t0 : Agent := .thread c0 0 0
private def t1 : Agent := .thread c0 0 1
private def scratch : Addr := ⟨.shared c0, "scratch", 0⟩

-- Pin the two-agent schedule and each segment's write footprint in the public
-- judgment, even though the witness module deliberately keeps its launch private.
example (s : DistState) : ∃ (l : Launch Unit) (f : Config Unit),
    Run l (l.initial s) [.agent t0, .agent t1] f ∧ Complete f ∧
    DataRace l f.history ∧
    (∀ σ, ((l.program t0).segment ()).writes σ = {scratch}) ∧
    (∀ σ, ((l.program t1).segment ()).writes σ = {scratch}) := by
  obtain ⟨f, run, done_, race⟩ := UnguardedShared.unguardedSharedRace s
  exact ⟨_, f, run, done_, race, fun _ => rfl, fun _ => rfl⟩

-- The same schedule with the thread-0 guard has one writer and no race in
-- this completed run. This is not a claim of DRF for every launch schedule.
example (s : DistState) : ∃ (l : Launch Unit) (f : Config Unit),
    Run l (l.initial s) [.agent t0, .agent t1] f ∧ Complete f ∧
    ¬ DataRace l f.history ∧
    (∀ σ, ((l.program t0).segment ()).writes σ = {scratch}) ∧
    (∀ σ, ((l.program t1).segment ()).writes σ = ∅) := by
  obtain ⟨f, run, done_, noRace⟩ := UnguardedShared.guardedSharedNoRace s
  exact ⟨_, f, run, done_, noRace, fun _ => rfl, fun _ => rfl⟩

end LocationRegression
