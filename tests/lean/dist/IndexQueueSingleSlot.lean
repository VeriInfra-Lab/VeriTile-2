import tests.lean.dist.IndexQueueSingleSlotRuns
import tests.lean.dist.IndexQueueSingleSlotShape
import tests.lean.dist.IndexQueueSingleSlotRefines
import tests.lean.dist.IndexQueueSingleSlotNegative
import tests.lean.dist.IndexQueueSingleSlotWitness

/-! Deliverable 1 of #651. The scheduler chooses each segment or group independently.
Both index words are initially zero; the initial data slot is unconstrained. -/
namespace VeriTile.Tests.G1QueueRefinement
open VeriTile.Dist
open DeepEPChannel (rel tail head slot)
open Dispatch

theorem Dispatch.shaped (w : CellWrites) (s : DistState)
    (tail0 : (s.cell DeepEPChannel.tail).readAs .nat = some 0) (head0 : (s.cell DeepEPChannel.head).readAs .nat = some 0) :
    (Q1 rel).Shaped (launch rel w) s :=
  shaped_of_prefix (fun _ _ => runPrefix w s tail0 head0)
    (fun _ _ => completePrefix w s tail0 head0)

/-- Handoff and reuse for this concrete launch, including every prefix of a complete run. -/
theorem IndexQueue.refines_singleSlot (w : CellWrites) (s : DistState)
    (tail0 : (s.cell DeepEPChannel.tail).readAs .nat = some 0) (head0 : (s.cell DeepEPChannel.head).readAs .nat = some 0) :
    QueueRefines (launch rel w) s (Q1 rel).view := by
  intro sched final run
  obtain ⟨_, tr⟩ := runPrefix w s tail0 head0 run
  exact prefixRefines tr w

/-- The value at the physical data slot immediately before either take is the matching payload. -/
theorem Dispatch.takeValue (w : CellWrites) (s : DistState)
    (tail0 : (s.cell DeepEPChannel.tail).readAs .nat = some 0) (head0 : (s.cell DeepEPChannel.head).readAs .nat = some 0)
    (run : Run (launch rel w) ((launch rel w).initial s) sched final)
    (take : (Q1 rel).view.Take final.history k j) :
    IndexQueue.lastValue s final.history slot j = (Q1 rel).payload k := by
  obtain ⟨_, tr⟩ := runPrefix w s tail0 head0 run
  exact takeLastStore tr s take

#print axioms Dispatch.shaped
#print axioms IndexQueue.refines_singleSlot
#print axioms Dispatch.takeValue
#print axioms Dispatch.SingleSlotWitness.completeScheduled
#print axioms Dispatch.relaxed_not_refines
#print axioms Dispatch.DecreasingTail.not_shaped
end VeriTile.Tests.G1QueueRefinement
