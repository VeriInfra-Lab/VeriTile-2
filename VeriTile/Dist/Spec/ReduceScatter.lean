/-
Reduce-scatter, GEMM and their collective compositions over real tensors (S7.2).
The signed specifications move from SpecLibSpec with the same definitions.
The inner contraction reuses the upstream GEMM sum; the cross-rank sum uses
the order provided for each destination cell.
-/
import VeriTile.Dist.Spec.AllGather
import VeriTile.Triton.KernelLemmas.Matmul

namespace VeriTile.Dist

open VeriTile.Triton
open scoped BigOperators

/-- Signed (#66). Owner: S7.2. Each rank holds a full tensor of `numRanks * n`
rows. Afterwards rank `r` holds chunk `r` of the sum over ranks; the element at
index `i` of that chunk is added in the order `order r i`. -/
noncomputable def reduceScatter {numRanks n : Nat} {ι : Type}
    (order : Fin numRanks → Fin n × ι → ReduceOrder (Fin numRanks))
    (x : RankTensor numRanks (Fin (numRanks * n) × ι)) :
    RankTensor numRanks (Fin n × ι) :=
  fun r i => (order r i).eval fun q => x q (finProdFinEquiv (r, i.1), i.2)

/-- Signed (#66). Owner: S7.2 (`ReduceScatter.lean`).
With coverage, destination `r` receives its row chunk
of the sum across all source ranks. -/
theorem reduceScatter_eq_sum_of_covers {numRanks n : Nat} {ι : Type}
    (order : Fin numRanks → Fin n × ι → ReduceOrder (Fin numRanks))
    (x : RankTensor numRanks (Fin (numRanks * n) × ι))
    (r : Fin numRanks) (i : Fin n) (j : ι) (h : (order r (i, j)).Covers) :
    reduceScatter order x r (i, j) = ∑ q, x q (finProdFinEquiv (r, i), j) :=
  ReduceOrder.eval_eq_sum_of_covers (fun q => x q (finProdFinEquiv (r, i), j)) h

/-- Signed (#66). Owner: S7.2. What the specification says: rank `r` gets chunk
`r` of the sum, with rank 0 added before rank 1. -/
theorem reduceScatter_twoRanks {n : Nat} {ι : Type}
    (x : RankTensor 2 (Fin (2 * n) × ι)) (r : Fin 2) (i : Fin n) (j : ι) :
    reduceScatter (fun _ _ => .add (.input 0) (.input 1)) x r (i, j) =
      x 0 (finProdFinEquiv (r, i), j) + x 1 (finProdFinEquiv (r, i), j) := rfl

/-- Signed (#66). Owner: S7.2. The matrix product of the upstream matmul
specification `gemmSum`, on tensors: entry `(i, j)` is `∑ k, A i k * B k j`. -/
noncomputable def gemm {M K N : Nat} (A : TileIndex [M, K] → ℝ) (B : TileIndex [K, N] → ℝ) :
    TileIndex [M, N] → ℝ :=
  fun i =>
    gemmSum (fun k => if h : k < K then A (i.1, ⟨k, h⟩, PUnit.unit) else 0)
      (fun k => if h : k < K then B (⟨k, h⟩, i.2.1, PUnit.unit) else 0) K

/-- Signed (#66). Owner: S7.2. What the specification says: the Nat-indexed zero
padding is never read by `gemmSum`, whose sum stops at `K`. -/
theorem gemm_apply {M K N : Nat} (A : TileIndex [M, K] → ℝ) (B : TileIndex [K, N] → ℝ)
    (i : Fin M) (j : Fin N) :
    gemm A B (i, j, PUnit.unit) =
      ∑ k : Fin K, A (i, k, PUnit.unit) * B (k, j, PUnit.unit) := by
  unfold gemm gemmSum
  rw [Finset.sum_range]
  simp

/-- Signed (#66). Owner: S7.2. Allgather followed by a matrix product: rank `r`
holds the product of the gathered `A` with its own `B r`. -/
noncomputable def allGatherGemm {numRanks m K N : Nat}
    (A : RankTensor numRanks (TileIndex [m, K])) (B : RankTensor numRanks (TileIndex [K, N])) :
    RankTensor numRanks (TileIndex [numRanks * m, N]) :=
  fun r => gemm (allGather A r) (B r)

/-- Signed (#66). Owner: S7.2. What the composition says: the right operand is
local to the destination rank. -/
theorem allGatherGemm_eq {numRanks m K N : Nat}
    (A : RankTensor numRanks (TileIndex [m, K])) (B : RankTensor numRanks (TileIndex [K, N]))
    (r : Fin numRanks) : allGatherGemm A B r = gemm (allGather A r) (B r) := rfl

/-- The row gathered from rank `q` is multiplied by the destination's `B`. -/
theorem allGatherGemm_apply {numRanks m K N : Nat}
    (A : RankTensor numRanks (TileIndex [m, K])) (B : RankTensor numRanks (TileIndex [K, N]))
    (r q : Fin numRanks) (i : Fin m) (j : Fin N) :
    allGatherGemm A B r (finProdFinEquiv (q, i), j, PUnit.unit) =
      ∑ k : Fin K, A q (i, k, PUnit.unit) * B r (k, j, PUnit.unit) := by
  rw [allGatherGemm_eq, gemm_apply]
  simp only [allGather_apply]

/-- Signed (#66). Owner: S7.2. A matrix product followed by reduce-scatter: rank
`r` holds chunk `r` of the sum over ranks `q` of the products `A q * B q`. -/
noncomputable def gemmReduceScatter {numRanks m K N : Nat}
    (order : Fin numRanks → TileIndex [m, N] → ReduceOrder (Fin numRanks))
    (A : RankTensor numRanks (TileIndex [numRanks * m, K]))
    (B : RankTensor numRanks (TileIndex [K, N])) :
    RankTensor numRanks (TileIndex [m, N]) :=
  reduceScatter order fun q => gemm (A q) (B q)

/-- Signed (#66). Owner: S7.2. What the composition says: destination `r` takes
its own row chunk, and the supplied tree keeps the cross-rank sum order. -/
theorem gemmReduceScatter_apply {numRanks m K N : Nat}
    (order : Fin numRanks → TileIndex [m, N] → ReduceOrder (Fin numRanks))
    (A : RankTensor numRanks (TileIndex [numRanks * m, K]))
    (B : RankTensor numRanks (TileIndex [K, N]))
    (r : Fin numRanks) (i : Fin m) (j : Fin N) :
    gemmReduceScatter order A B r (i, j, PUnit.unit) =
      (order r (i, j, PUnit.unit)).eval (fun q =>
        ∑ k : Fin K, A q (finProdFinEquiv (r, i), k, PUnit.unit) *
          B q (k, j, PUnit.unit)) := by
  unfold gemmReduceScatter reduceScatter
  apply congrArg (fun f : Fin numRanks → ℝ => (order r (i, j, PUnit.unit)).eval f)
  funext q
  exact gemm_apply (A q) (B q) (finProdFinEquiv (r, i)) j

/-- Signed (#66). Owner: S7.2 (`ReduceScatter.lean`).
With coverage, a destination cell sums the corresponding
local matrix product cell from every source rank. -/
theorem gemmReduceScatter_eq_sum_of_covers {numRanks m K N : Nat}
    (order : Fin numRanks → TileIndex [m, N] → ReduceOrder (Fin numRanks))
    (A : RankTensor numRanks (TileIndex [numRanks * m, K]))
    (B : RankTensor numRanks (TileIndex [K, N]))
    (r : Fin numRanks) (i : Fin m) (j : Fin N) (h : (order r (i, j, PUnit.unit)).Covers) :
    gemmReduceScatter order A B r (i, j, PUnit.unit) =
      ∑ q, ∑ k : Fin K, A q (finProdFinEquiv (r, i), k, PUnit.unit) *
        B q (k, j, PUnit.unit) := by
  rw [gemmReduceScatter_apply]
  exact ReduceOrder.eval_eq_sum_of_covers _ h

namespace ReduceScatterExamples

/-- The same interface preserves the reverse source order as well. -/
example {n : Nat} {ι : Type} (x : RankTensor 2 (Fin (2 * n) × ι))
    (r : Fin 2) (i : Fin n) (j : ι) :
    reduceScatter (fun _ _ => .add (.input 1) (.input 0)) x r (i, j) =
      x 1 (finProdFinEquiv (r, i), j) + x 0 (finProdFinEquiv (r, i), j) := rfl

/-- An empty tree gives zero where the sum of the two inputs is nonzero. -/
example :
    reduceScatter (numRanks := 2) (n := 1) (ι := Unit)
      (fun _ _ => .zero) (fun _ _ => 1) 0 (0, ()) ≠ ∑ _q : Fin 2, (1 : ℝ) := by
  norm_num [reduceScatter, ReduceOrder.eval]

private def distinctRows : RankTensor 2 (Fin (2 * 1) × Unit) :=
  fun _ row => if row.1 = 0 then 0 else 1

/-- Destination 1 cannot take chunk 0 when the chunks differ. -/
example :
    reduceScatter (fun _ _ => .add (.input 0) (.input 1)) distinctRows 1 (0, ()) ≠
      distinctRows 0 (0, ()) + distinctRows 1 (0, ()) := by
  rw [reduceScatter_twoRanks]
  change (1 : ℝ) + 1 ≠ 0 + 0
  norm_num

/-- Dropping the second contraction term changes the matrix product. -/
example : gemm (M := 1) (K := 2) (N := 1) (fun _ => 1) (fun _ => 1)
    (0, 0, PUnit.unit) ≠ 1 := by
  rw [gemm_apply]
  norm_num

private def localB : RankTensor 2 (TileIndex [1, 1]) :=
  fun q _ => if q = 0 then 1 else 2

/-- The row from rank 0 must use destination 1's right operand. -/
example :
    allGatherGemm (m := 1) (fun _ _ => 1) localB 1
      (finProdFinEquiv ((0 : Fin 2), (0 : Fin 1)), 0, PUnit.unit) ≠
    gemm (allGather (numRanks := 2) (n := 1) (fun _ _ => 1) 1) (localB 0) (0, 0, PUnit.unit) := by
  rw [allGatherGemm_apply, gemm_apply]
  norm_num [allGather, localB]

private def bothRanks : ReduceOrder (Fin 2) := .add (.input 0) (.input 1)

/-- A covered tree sums both local products. -/
example :
    gemmReduceScatter (m := 1) (fun _ _ => bothRanks) (fun _ _ => 1) localB 0
      (0, 0, PUnit.unit) = 3 := by
  rw [gemmReduceScatter_eq_sum_of_covers _ _ _ _ _ _ (by decide)]
  norm_num [localB]

/-- Each local product uses its own right operand before the reduction. -/
example :
    gemmReduceScatter (m := 1) (fun _ _ => bothRanks) (fun _ _ => 1) localB 0
      (0, 0, PUnit.unit) ≠ bothRanks.eval (fun _ => localB 0 (0, 0, PUnit.unit)) := by
  rw [gemmReduceScatter_apply]
  norm_num [bothRanks, ReduceOrder.eval, localB]

/-- Dropping rank 1's nonzero product breaks the full-rank sum. -/
example :
    gemmReduceScatter (m := 1) (fun _ _ => .input 0) (fun _ _ => 1) localB 0
      (0, 0, PUnit.unit) ≠ ∑ q : Fin 2, localB q (0, 0, PUnit.unit) := by
  rw [gemmReduceScatter_apply]
  norm_num [ReduceOrder.eval, localB]

end ReduceScatterExamples
end VeriTile.Dist
