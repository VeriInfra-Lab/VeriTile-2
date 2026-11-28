import tests.lean.dist.IndexQueueCapacityTwoShape
import tests.lean.dist.IndexQueueCapacityTwoWitness
import tests.lean.dist.IndexQueueGeneral

namespace VeriTile.Tests.G1QueueRefinement.CapacityTwo
open VeriTile.Dist
open DeepEPChannel (sender receiver tail head rel)

theorem launchSound (threshold : Nat) (w : CellWrites) : SoundLaunch (launch threshold w) := by
  apply SingletonProgram.sound
  · intro a pc _ h t k hv
    cases pc <;> cases hv <;> exact ⟨rfl, rfl⟩
  · exact fun _ _ _ _ _ _ => rfl
  · exact fun a _ => FetchAddObservation.emptySound a
  · intro a c started cta
    by_cases h : a = sender ∨ a = receiver
    · rcases h with rfl | rfl <;> cases cta <;> rfl
    · simp [launch, not_or.mp h |>.1, not_or.mp h |>.2] at started

/-- The third token reuses the first token's slot under the release protocol. -/
theorem release_refines (w : CellWrites) (s : DistState)
    (ht : (s.cell tail).readAs .nat = some 0) (hh : (s.cell head).readAs .nat = some 0) :
    QueueRefines (launch 1 w) s queue.view :=
  IndexQueue.refines (launchSound 1 w) (shaped w s ht hh)
    (Dispatch.publish_pairs rel w) (Dispatch.release_ack_pairs w) ht hh

/-- The public cell contract holds for both physical addresses on every reachable prefix. -/
theorem cell_refines (w : CellWrites) (s : DistState)
    (ht : (s.cell tail).readAs .nat = some 0) (hh : (s.cell head).readAs .nat = some 0) :
    queue.cellView.Refines (launch 1 w) s :=
  IndexQueue.cellView_of_refines (shaped w s ht hh) (release_refines w s ht hh)

/-- The actual run orders the first take before the third put on their shared slot. -/
theorem completedReuse (w : CellWrites) (s : DistState)
    (ht : (s.cell tail).readAs .nat = some 0) (hh : (s.cell head).readAs .nat = some 0) :
    ∃ sched final, Run (launch 1 w) ((launch 1 w).initial s) sched final ∧ Complete final ∧
      queue.view.Take final.history 0 9 ∧ queue.view.Put final.history 2 17 ∧
      HB (launch 1 w) final.history (queue.slotOf 0) 9 17 := by
  obtain ⟨sched, final, run, done, first, _, _, third, _⟩ := completeRun w s
  obtain ⟨j, taken, _, ordered⟩ := (release_refines w s ht hh sched final run).2 0 17 third
  have before := NthAt.ordinal_lt taken first
  have after := NthAt.ordinal_lt first taken
  have same : j = 9 := by omega
  exact ⟨sched, final, run, done, first, third, same ▸ ordered⟩

#print axioms completedReuse

#print axioms launchSound
#print axioms release_refines
#print axioms cell_refines
end VeriTile.Tests.G1QueueRefinement.CapacityTwo
