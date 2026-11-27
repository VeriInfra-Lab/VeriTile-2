import Mathlib.Tactic

/-! DeepEP K28 sender, one reached polling/publishing round of channel 0 with two
target ranks. At tile-ai/tilescale `9ba8a605d347f600a95d0275e2639cb00122c084`,
`examples/distributed/deepseek_deepep/intranode/combine.py` lines 109–112 and
141–149 give the launch and round-robin warp assignment. The warp sync at 180
and rank-group sync at 216 precede the election at 217 and the tail store to
`dst_pe=send_rank_id` at 218–224. The election and rank barrier group sizes differ:
96 consecutive threads versus 384 threads of a rank. `tilelang/language/builtin.py`
438–445 specifies one winner in a logical group. Neither witness below identifies
the lane selected by a particular runtime or establishes a synchronization edge. -/
namespace VeriTile.Tests.IndexQueueSenderElection

abbrev Thread := Fin 768
abbrev Window := Fin 8
abbrev TargetRank := Fin 2

def window (t : Thread) : Window := ⟨t.val / 96, by have := t.isLt; omega⟩

/-- DC:148 for the sender of the given channel, specialized to two ranks. -/
def sendRank (channel : Nat) (t : Thread) : TargetRank :=
  ⟨(channel + t.val / 32) % 2, Nat.mod_lt _ (by decide)⟩

def OnePerWindow (elected : Thread → Prop) : Prop :=
  ∀ w : Window, ∃! t : Thread, window t = w ∧ elected t

def CoversBoth (channel : Nat) (elected : Thread → Prop) : Prop :=
  ∀ r : TargetRank, ∃ t : Thread, elected t ∧ sendRank channel t = r

/-- The witness selects a local offset inside each of the eight election windows. -/
private def winner (select : Window → Fin 96) (w : Window) : Thread :=
  ⟨96 * w.val + (select w).val, by have := w.isLt; have := (select w).isLt; omega⟩

private theorem winner_window (select : Window → Fin 96) (w : Window) :
    window (winner select w) = w := by
  apply Fin.ext
  change (96 * w.val + (select w).val) / 96 = w.val
  have := (select w).isLt
  omega

private def electedBy (select : Window → Fin 96) (t : Thread) : Prop :=
  t = winner select (window t)

private theorem onePerWindow (select : Window → Fin 96) : OnePerWindow (electedBy select) := by
  intro w
  refine ⟨winner select w, ⟨winner_window _ _, ?_⟩, ?_⟩
  · simp [electedBy, winner_window]
  · rintro t ⟨atWindow, elected⟩
    simpa [electedBy, atWindow] using elected

/-- Window 0 begins at warp 0, window 1 at warp 3. Choose the first warp
in each even window and the second warp in each odd window. -/
private def evenWarp (w : Window) : Fin 96 := if w.val % 2 = 0 then 0 else 32

theorem sameRankElection : ∃ elected, OnePerWindow elected ∧
    ∀ t, elected t → sendRank 0 t = 0 := by
  refine ⟨electedBy evenWarp, onePerWindow _, ?_⟩
  intro t elected
  have allEven : ∀ w : Window, sendRank 0 (winner evenWarp w) = 0 := by decide
  exact (congrArg (sendRank 0) elected).trans (allEven _)

/-- One release-store candidate per 96-thread window does not supply the
K28 sender premise that each target rank has an elected publisher. -/
theorem onePerWindow_does_not_imply_coverage :
    ¬ (∀ elected, OnePerWindow elected → CoversBoth 0 elected) := by
  intro impliesCoverage
  obtain ⟨elected, one, onlyZero⟩ := sameRankElection
  obtain ⟨t, yes, oneRank⟩ := impliesCoverage elected one 1
  exact (by decide : (0 : TargetRank) ≠ 1) ((onlyZero t yes).symm.trans oneRank)

/-- The first thread of each 96-thread window also satisfies the same election
contract. Threads 0 and 96 are distinct publication candidates for ranks 0 and 1. -/
theorem coveringElection : ∃ elected, OnePerWindow elected ∧ CoversBoth 0 elected := by
  let first : Window → Fin 96 := fun _ => 0
  refine ⟨electedBy first, onePerWindow _, ?_⟩
  intro r
  fin_cases r
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨96, rfl, rfl⟩

#print axioms onePerWindow_does_not_imply_coverage
#print axioms coveringElection

end VeriTile.Tests.IndexQueueSenderElection
