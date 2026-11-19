/-
Allgather over real tensors (S7.2). The definition and signed statement move
unchanged from SpecLibSpec. Rows are concatenated in rank order.
-/
import VeriTile.Dist.Spec.RankTensor
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace VeriTile.Dist

/-- Owner: S7.2. Each rank holds a chunk of `n` rows. Afterwards
every rank holds all chunks in rank order. -/
def allGather {numRanks n : Nat} {ι : Type} (x : RankTensor numRanks (Fin n × ι)) :
    RankTensor numRanks (Fin (numRanks * n) × ι) :=
  fun _ i => x i.1.divNat (i.1.modNat, i.2)

/-- Owner: S7.2. On every rank, row `q * n + i` of the allgather
result is row `i` of the chunk of rank `q`. -/
theorem allGather_apply {numRanks n : Nat} {ι : Type} (x : RankTensor numRanks (Fin n × ι))
    (r q : Fin numRanks) (i : Fin n) (j : ι) :
    allGather x r (finProdFinEquiv (q, i), j) = x q (i, j) := by
  exact congrArg (fun p : Fin numRanks × Fin n => x p.1 (p.2, j))
    (finProdFinEquiv.symm_apply_apply (q, i))

/-- On either of two ranks, every column is the concatenation of the two
input chunks. The cast only identifies `n + n` rows with `2 * n` rows. -/
theorem allGather_twoRanks {n : Nat} {ι : Type} (x : RankTensor 2 (Fin n × ι))
    (r : Fin 2) (j : ι) :
    (fun i : Fin (n + n) => allGather x r (Fin.cast (by omega) i, j)) =
      Fin.append (fun i => x 0 (i, j)) (fun i => x 1 (i, j)) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    have hrow : Fin.cast (by omega : n + n = 2 * n) (Fin.castAdd n k) =
        finProdFinEquiv ((0 : Fin 2), k) := by
      ext
      simp [finProdFinEquiv]
    simp only [Fin.append_left]
    rw [hrow, allGather_apply]
  · intro k
    have hrow : Fin.cast (by omega : n + n = 2 * n) (Fin.natAdd n k) =
        finProdFinEquiv ((1 : Fin 2), k) := by
      ext
      simp [finProdFinEquiv, Nat.add_comm]
    simp only [Fin.append_right]
    rw [hrow, allGather_apply]

namespace AllGatherExamples

private def distinctChunks : RankTensor 2 (Fin 1 × Unit) :=
  fun r _ => if r = 0 then 0 else 1

private def swappedChunks : RankTensor 2 (Fin (2 * 1) × Unit) :=
  fun _ ij => Fin.append (fun i : Fin 1 => distinctChunks 1 (i, ij.2))
    (fun i : Fin 1 => distinctChunks 0 (i, ij.2)) ij.1

/-- Swapping two different rank chunks violates the signed row formula. -/
example : swappedChunks ≠ allGather distinctChunks := by
  intro h
  have hcell := congrArg
    (fun y : RankTensor 2 (Fin (2 * 1) × Unit) => y 0 (0, ())) h
  change distinctChunks 1 (0, ()) =
    allGather distinctChunks 0 (finProdFinEquiv ((0 : Fin 2), (0 : Fin 1)), ()) at hcell
  rw [allGather_apply] at hcell
  norm_num [distinctChunks] at hcell

end AllGatherExamples
end VeriTile.Dist
