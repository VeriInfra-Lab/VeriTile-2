import tests.lean.dist.IndexQueueCapacityTwoShape
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

#print axioms launchSound
#print axioms release_refines
#print axioms cell_refines
end VeriTile.Tests.G1QueueRefinement.CapacityTwo
