import tests.lean.dist.Tutorial05

/-! Independent deletion control for the K11-to-K10 CUDA stream handoff.
Starting the tile at cursor 1 erases its initial empty segment and post-marker
wait. Its physical tile segment, the host copies, both CAS groups, the CTA
roster and both control words are exactly the positive launch's definitions. -/
namespace VeriTile.Tests.T05Pilot.Whole.NoStreamWait
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
open VeriTile.Tests.T05Pilot
open VeriTile.Tests.FetchAddObservation (putCellWrites)
noncomputable section

def withoutTileWait (n lanes rows cols : Nat) (w : CellWrites) : Launch Nat :=
  let base := launch true n lanes rows cols w
  { base with start := fun a =>
    match decode n lanes rows cols a with
    | some (.tile ..) => some 1
    | _ => base.start a }

theorem same_program (n lanes rows cols : Nat) (w : CellWrites) :
    (withoutTileWait n lanes rows cols w).program = (launch true n lanes rows cols w).program := rfl

private abbrev altered := withoutTileWait 2 128 1 1 putCellWrites
private abbrev tileAgent := Stream.tile 0 0
private abbrev peerAgent := Stream.host 1
private abbrev coord : Coordinate 1 1 := (0,0)

private def ended (fromState : Config Nat) (a : Agent) (pc : Nat) (seg : Segment) (out : DistState) :
    Config Nat := { fromState with
      mem := out
      history := fromState.history ++ [.segment a (seg.reads fromState.mem) (seg.writes fromState.mem)]
      pc := Function.update fromState.pc a (((altered.program a).next pc fromState.mem).cursor)}

/-- On the same stale input, the original 128-lane launch is safe. Dropping
just the tile's post wait admits two real, conflicting segment steps. -/
theorem original_safe_deleted_races :
    DRF (launch true 2 128 1 1 putCellWrites) TwoRank128.initial ∧
    ∃ f, Run altered (altered.initial TwoRank128.initial) [.agent tileAgent,.agent peerAgent] f ∧
      DataRace altered f.history := by
  refine ⟨race_free TwoRank128.initial_data (by decide) putCellWrites,?_⟩
  let initial := altered.initial TwoRank128.initial
  have zero (u : Coordinate 1 1) (src : Fin 2) (_ : tileIndex u = 0) :
      (initial.mem.cell (scatterSlot (0 : Fin 2) src u.1 u.2)).readAs .real = some ((0:ℝ) : WithBot ℝ) := by
    rfl
  obtain ⟨out,tileRuns,_,_⟩ := encodedTile_run (fun (_ : Fin 2) (_ : Fin (2*1) × Fin 1) => (0:ℝ))
    (0 : Fin 2) 0 initial.mem zero
  let tile := encodedTileSeg 1 1 (0 : Fin 2) 0
  let mid := ended initial tileAgent 1 tile out
  have st : step altered initial (.agent tileAgent) mid := by
    apply step.segment (l := altered) (a := tileAgent) (pc := 1) (seg := tile) rfl rfl rfl _ tileRuns
    intro p mem
    refine ⟨?_,quiet_free (h := initial.history) (by simp [initial,Launch.initial,Quiet]) p⟩
    rcases mem with ⟨u,src,_,rfl⟩|⟨u,_,rfl⟩
    all_goals exact ⟨trivial,.inl rfl⟩
  let host := hostCopySeg 1 1 (1 : Fin 2)
  obtain ⟨copied,copyRuns⟩ := hostCopy_runs 1 1 (1 : Fin 2) mid.mem
  let f := ended mid peerAgent 0 host copied
  have st' : step altered mid (.agent peerAgent) f := by
    apply step.segment (l := altered) (a := peerAgent) (pc := 0) (seg := host) (by rfl) rfl rfl _ copyRuns
    intro p mem
    have quiet : Quiet mid.history := quiet_snoc (by simp [initial,Launch.initial,Quiet]) (by simp [Occurrence.event?])
    refine ⟨?_,quiet_free quiet p⟩
    rcases mem with ⟨q,u,rfl⟩|⟨q,u,rfl⟩
    · exact ⟨trivial,.inl rfl⟩
    · exact ⟨trivial,.inr rfl⟩
  refine ⟨f,.cons st (.cons st' (.nil _)),?_⟩
  let read := Occurrence.segment tileAgent (@readsOf 2 1 1 0 0) (@writesOf 2 1 1 0 0)
  let write := Occurrence.segment peerAgent (copyReads 1 1 (1 : Fin 2)) (copyWrites 1 1 (1 : Fin 2))
  have readAt : f.history[0]? = some read := rfl
  have writeAt : f.history[1]? = some write := rfl
  refine ⟨0,1,read,write,scatterSlot (0 : Fin 2) (1 : Fin 2) coord.1 coord.2,.load,.store,
    .plain,.plain,by decide,readAt,writeAt,⟨coord,1,rfl,rfl⟩,⟨0,coord,rfl⟩,.inr rfl,
    by simp [Mode.AtomicFor],?_⟩
  apply Stream.firstTileNoHB writeAt
  intro k bound occ atK
  have : k=0 := by omega
  subst k; rw [readAt] at atK; cases atK
  decide

#print axioms same_program
#print axioms original_safe_deleted_races
end
end VeriTile.Tests.T05Pilot.Whole.NoStreamWait
