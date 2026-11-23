/-
VeriTile.Staging.Dist.SpecLibSpec

Interface and statements of the specification library, frozen by ticket S7.1.
Signed: `allGather_apply` and `allReduce_eq_of_leaves_perm` (2026-11-11) and
`moeCombine_of_moeDispatch` (2026-11-12), each with the definitions under it.
Everything else is UNSIGNED.

The library states what a collective computes, as a mathematical function or
relation over one tensor per rank. It is independent of any front end and of
any schedule. Tickets S7.2–S7.5 move each declaration to `VeriTile/Dist/Spec/`
under the same name and type, prove the theorems and delete the stubs here.

Ranks. A rank is an element of `Fin numRanks` for a parameter `numRanks : Nat`.
The location model (`VeriTile/Staging/Dist/LocationSpec.lean`, ticket S1.1)
keeps `Rank := Nat`. The bridge between the two is `Fin.val`. This file does
not import the location model.

Arithmetic. Collective values are real numbers. No floating-point type and
no rounding appears. `ReduceOrder.eval` is generic in the carrier and
requires only zero and addition.

Reduction order. A sum over ranks is the value of a `ReduceOrder`: a tree that
fixes which operands are added and in what nesting. The specifications use no
associativity or commutativity; `allReduce_eq_of_leaves_perm` is the only
statement that relates two orders, and it is a statement over `ℝ`. The
unsigned `ReduceOrder.CoversOn` contract requires exactly one leaf per
operand in a specified finite set. `ReduceOrder.Covers` specializes it to
the whole index type. The collective sum lemmas use these contracts over `ℝ`.

MoE source. The MoE declarations follow the deduplicated layout
(`do_expand=False`) of the DeepEP port in TileScale, branch
`deepep-v2-intranode` at commit `c0f80cc5a5e386ae77075af9574701d3e0a99b00`,
directory `examples/distributed/deepep_v2/`.

Layout. An axis that holds one chunk of `n` rows per rank has `numRanks * n`
rows, and row `q * n + i` is row `i` of the chunk of rank `q`
(`finProdFinEquiv (q, i)`).

Decisions that the tickets left open:
 1. `RankTensor numRanks ι` is `Fin numRanks → ι → ℝ` for any index type `ι`;
    `TileIndex shape` of the Triton core is one instance.
 2. Issue #17: the reduction order is the tree with `zero`, `input` and `add`;
    a left fold over a list of operands is `ReduceOrder.ofList`.
    `ReduceOrder.eval` is generic in the carrier of the sum.
 3. The order of a reduction may differ per destination rank and per element.
 4. Every reduction is a sum.
 5. `ReduceOrder` belongs to S7.2, the first ticket that needs it in a main
    target, not to S7.3.
 6. Chunks have the same number of rows on every rank.
 7. `allGatherGemm` and `gemmReduceScatter` take the upstream `gemmSum` as the
    matrix product, whose inner sum has no order, as S7.2 asks; the sum over
    ranks in `gemmReduceScatter` keeps its order.
 8. In `allGatherGemm` the left operand is gathered and the right operand is
    local to each rank; in `gemmReduceScatter` both operands are local.
 9. Variable-length all-to-all, MoE dispatch and MoE store-back are relations
    between buffers, because they do not fix every row. Their buffers are
    indexed by a row in `Nat`; capacity is left to the kernel contract.
10. `AllToAllLayout.WellFormed` asks only that no receive row gets rows from
    two sources.
11. An MoE routing table gives each token a set of destination ranks, which
    may be empty, and one weight per destination. A token is sent once to each
    destination, also when it selects several experts there.
12. The row that a token gets at a destination is not in the routing table,
    because it depends on the schedule. A row assignment `MoERows` says which
    token each receive row holds; `MoERouting.Assigns` says which assignments
    a table allows; `MoEDispatch` takes the assignment as an argument.
    Which rows of a buffer are used, and their grouping by source rank, are
    not specified.
13. MoE combine is two steps: the relation `MoEStoreBack` and the sum
    `moeCombine`. Neither applies a weight; the weight is applied by the
    expert step, between dispatch and combine. The expanded layout, the bias
    of the combine and the gate weights that a dispatch delivers next to a
    row are not specified.
14. Ranks are `Fin numRanks` here and `Nat` in the location model.
15. An attention partial result is the softmax denominator and the normalized
    output of one query row, with the denominator not in logarithmic form.
16. Negative examples are concrete instances; S7.2–S7.5 choose them.
-/
import VeriTile.Triton.KernelLemmas.Matmul
import VeriTile.Dist.Spec.AllReduce
import VeriTile.Dist.Spec.AllGather

namespace VeriTile.Dist

open VeriTile.Triton
open scoped BigOperators

/-! ## Rank-indexed tensors and reduction orders -/

/-- UNSIGNED. Owner: S7.2. The left fold from zero over a list of operands:
`ofList [a, b, c]` is `((0 + a) + b) + c`. -/
def ReduceOrder.ofList {ι : Type} (operands : List ι) : ReduceOrder ι :=
  operands.foldl (fun order i => .add order (.input i)) .zero

/-- UNSIGNED (#66). Owner: S7.2 (`RankTensor.lean`).
Each member of `operands` occurs exactly once, and every leaf is a member. -/
def ReduceOrder.CoversOn {ι : Type} (order : ReduceOrder ι)
    (operands : Finset ι) : Prop :=
  order.leaves.Nodup ∧ ∀ q, q ∈ order.leaves ↔ q ∈ operands

/-- Owner: S7.2 (`RankTensor.lean`). Convert the membership condition to
finite set equality when the operand type has decidable equality. -/
theorem ReduceOrder.coversOn_iff_toFinset {ι : Type} [DecidableEq ι] (order : ReduceOrder ι)
    (operands : Finset ι) :
    order.CoversOn operands ↔ order.leaves.Nodup ∧ order.leaves.toFinset = operands := by
  simp [ReduceOrder.CoversOn, Finset.ext_iff]

/-- Owner: S7.2 (`RankTensor.lean`). Decide coverage by testing the leaf list. -/
instance ReduceOrder.CoversOn.decidable {ι : Type} [DecidableEq ι]
    (order : ReduceOrder ι) (operands : Finset ι) : Decidable (order.CoversOn operands) :=
  decidable_of_iff _ (order.coversOn_iff_toFinset operands).symm

/-- UNSIGNED (#66). Owner: S7.2 (`RankTensor.lean`).
Full coverage means coverage of the universal finite set. -/
def ReduceOrder.Covers {ι : Type} [Fintype ι] (order : ReduceOrder ι) : Prop :=
  order.CoversOn Finset.univ

/-- Owner: S7.2 (`RankTensor.lean`). Decide coverage of the universal set. -/
instance ReduceOrder.Covers.decidable {ι : Type} [DecidableEq ι] [Fintype ι]
    (order : ReduceOrder ι) : Decidable order.Covers :=
  inferInstanceAs (Decidable (order.CoversOn Finset.univ))

/-- Owner: S7.2 (`RankTensor.lean`). For numbered ranks, full coverage
is the original permutation condition. -/
theorem ReduceOrder.covers_iff_perm_finRange {n : Nat} (order : ReduceOrder (Fin n)) :
    order.Covers ↔ order.leaves.Perm (List.finRange n) := by
  change order.CoversOn Finset.univ ↔ _
  rw [ReduceOrder.coversOn_iff_toFinset]
  constructor
  · intro h
    exact List.perm_of_nodup_nodup_toFinset_eq h.1 (List.nodup_finRange n)
      (h.2.trans (List.toFinset_finRange n).symm)
  · intro h
    exact ⟨h.nodup_iff.mpr (List.nodup_finRange n),
      (List.toFinset_eq_of_perm _ _ h).trans (List.toFinset_finRange n)⟩

/-- Owner: S7.2 (`RankTensor.lean`). The left fold preserves the order and
multiplicity of its operand list. -/
theorem ReduceOrder.leaves_ofList {ι : Type} (operands : List ι) :
    (ReduceOrder.ofList operands).leaves = operands := by
  suffices h : ∀ acc : ReduceOrder ι,
      (operands.foldl (fun order i => ReduceOrder.add order (.input i)) acc).leaves =
        acc.leaves ++ operands by
    simpa [ReduceOrder.ofList, ReduceOrder.leaves] using h .zero
  induction operands with
  | nil => intro acc; simp
  | cons i rest ih => intro acc; simp [ih, ReduceOrder.leaves]

/-- Owner: S7.2 (`RankTensor.lean`). A duplicate-free list that enumerates
the set gives a covering tree. -/
theorem ReduceOrder.ofList_coversOn {ι : Type} {indices : List ι}
    {operands : Finset ι} (hn : indices.Nodup) (hs : ∀ q, q ∈ indices ↔ q ∈ operands) :
    (ReduceOrder.ofList indices).CoversOn operands := by
  unfold ReduceOrder.CoversOn
  rw [ReduceOrder.leaves_ofList]
  exact ⟨hn, hs⟩

/-- Owner: S7.2 (`RankTensor.lean`). Every finite set admits a covering
tree, including the empty set. -/
theorem ReduceOrder.ofList_finset_coversOn {ι : Type} (operands : Finset ι) :
    (ReduceOrder.ofList operands.toList).CoversOn operands :=
  ReduceOrder.ofList_coversOn (Finset.nodup_toList operands) (fun _ => Finset.mem_toList)

/-- UNSIGNED (#66). Owner: S7.2 (`RankTensor.lean`).
A tree covering a finite set evaluates to the sum over that set. -/
theorem ReduceOrder.eval_eq_sum_of_coversOn {ι α : Type} [AddCommMonoid α]
    {order : ReduceOrder ι} {operands : Finset ι} (f : ι → α) (h : order.CoversOn operands) :
    order.eval f = ∑ q ∈ operands, f q := by
  classical
  obtain ⟨hn, hs⟩ := (order.coversOn_iff_toFinset operands).mp h
  rw [order.eval_eq_sum_leaves, ← hs, List.sum_toFinset f hn]

/-- UNSIGNED (#66). Owner: S7.2 (`RankTensor.lean`).
The subset sum theorem specializes to the sum over a finite index type. -/
theorem ReduceOrder.eval_eq_sum_of_covers {ι α : Type} [Fintype ι] [AddCommMonoid α]
    {order : ReduceOrder ι} (f : ι → α) (h : order.Covers) :
    order.eval f = ∑ q, f q :=
  ReduceOrder.eval_eq_sum_of_coversOn f (show order.CoversOn Finset.univ from h)

/-- UNSIGNED (#66). Owner: S7.3 (`AllReduce.lean`).
A covered output cell contains the sum over all ranks. -/
theorem allReduce_eq_sum_of_covers {numRanks : Nat} {ι : Type}
    (order : Fin numRanks → ι → ReduceOrder (Fin numRanks)) (x : RankTensor numRanks ι)
    (r : Fin numRanks) (i : ι) (h : (order r i).Covers) :
    allReduce order x r i = ∑ q, x q i :=
  ReduceOrder.eval_eq_sum_of_covers (fun q => x q i) h

example : (ReduceOrder.add (.input (1 : Fin 2)) (.input 0)).Covers := by decide

example : ¬ (ReduceOrder.input (0 : Fin 2)).Covers := by decide

example : ¬ (ReduceOrder.add (.input (0 : Fin 2)) (.input 0)).Covers := by decide

/-- A proof using classical equality can supply coverage to a concrete caller. -/
example (order : ReduceOrder (Fin 2)) (f : Fin 2 → Nat)
    (h : by classical exact order.Covers) : order.eval f = ∑ q, f q :=
  ReduceOrder.eval_eq_sum_of_covers f h

example (numRanks : Nat) : (ReduceOrder.ofList (List.finRange numRanks)).Covers := by
  rw [ReduceOrder.covers_iff_perm_finRange, ReduceOrder.leaves_ofList]

/-- Subset evaluation works even when the index type is infinite. -/
example (f : Nat → Nat) :
    (ReduceOrder.add (.input 3) (.input 1)).eval f = ∑ q ∈ ({1, 3} : Finset Nat), f q :=
  ReduceOrder.eval_eq_sum_of_coversOn f (by decide)

example : (ReduceOrder.zero : ReduceOrder Nat).CoversOn ∅ := by decide

example : ¬ (ReduceOrder.input (2 : Nat)).CoversOn {1} := by decide

example : ¬ (ReduceOrder.add (.input (1 : Nat)) (.input 1)).CoversOn {1} := by decide

/-- Omitting rank 1 changes the sum on two inputs of 1. -/
example : allReduce (numRanks := 2) (ι := Unit) (fun _ _ => .input 0) (fun _ _ => 1) 0 () ≠
    ∑ _q : Fin 2, (1 : ℝ) := by
  norm_num [allReduce, ReduceOrder.eval]

/-- Repeating rank 0 changes the sum even when the tree has two leaves. -/
example : allReduce (numRanks := 2) (ι := Unit) (fun _ _ => .add (.input 0) (.input 0))
    (fun q _ => if q = 0 then 1 else 0) 0 () ≠ ∑ q : Fin 2, (if q = 0 then (1 : ℝ) else 0) := by
  norm_num [allReduce, ReduceOrder.eval]

/-! ## Allgather and reduce-scatter (S7.2) -/

/-- UNSIGNED. Owner: S7.2. Each rank holds a full tensor of `numRanks * n`
rows. Afterwards rank `r` holds chunk `r` of the sum over ranks; the element at
index `i` of that chunk is added in the order `order r i`. -/
noncomputable def reduceScatter {numRanks n : Nat} {ι : Type}
    (order : Fin numRanks → Fin n × ι → ReduceOrder (Fin numRanks))
    (x : RankTensor numRanks (Fin (numRanks * n) × ι)) :
    RankTensor numRanks (Fin n × ι) :=
  fun r i => (order r i).eval fun q => x q (finProdFinEquiv (r, i.1), i.2)

/-- UNSIGNED (#66). Owner: S7.2 (`ReduceScatter.lean`).
With coverage, destination `r` receives its row chunk
of the sum across all source ranks. -/
theorem reduceScatter_eq_sum_of_covers {numRanks n : Nat} {ι : Type}
    (order : Fin numRanks → Fin n × ι → ReduceOrder (Fin numRanks))
    (x : RankTensor numRanks (Fin (numRanks * n) × ι))
    (r : Fin numRanks) (i : Fin n) (j : ι) (h : (order r (i, j)).Covers) :
    reduceScatter order x r (i, j) = ∑ q, x q (finProdFinEquiv (r, i), j) :=
  ReduceOrder.eval_eq_sum_of_covers (fun q => x q (finProdFinEquiv (r, i), j)) h

/-- S7.2 sanity check for the unsigned specification: rank `r` gets chunk
`r` of the sum, with rank 0 added before rank 1. -/
theorem reduceScatter_twoRanks {n : Nat} {ι : Type}
    (x : RankTensor 2 (Fin (2 * n) × ι)) (r : Fin 2) (i : Fin n) (j : ι) :
    reduceScatter (fun _ _ => .add (.input 0) (.input 1)) x r (i, j) =
      x 0 (finProdFinEquiv (r, i), j) + x 1 (finProdFinEquiv (r, i), j) := rfl

/-- The same interface preserves the reverse source order as well. -/
example {n : Nat} {ι : Type} (x : RankTensor 2 (Fin (2 * n) × ι))
    (r : Fin 2) (i : Fin n) (j : ι) :
    reduceScatter (fun _ _ => .add (.input 1) (.input 0)) x r (i, j) =
      x 1 (finProdFinEquiv (r, i), j) + x 0 (finProdFinEquiv (r, i), j) := rfl

/-- The unsigned interface permits an empty tree; full-rank coverage must
therefore be supplied by the eventual contract if a full sum is intended. -/
example :
    reduceScatter (numRanks := 2) (n := 1) (ι := Unit)
      (fun _ _ => .zero) (fun _ _ => 1) 0 (0, ()) ≠ (1 : ℝ) + 1 := by
  norm_num [reduceScatter, ReduceOrder.eval]

/-- UNSIGNED. Owner: S7.2. The matrix product of the upstream matmul
specification `gemmSum`, on tensors: entry `(i, j)` is `∑ k, A i k * B k j`. -/
noncomputable def gemm {M K N : Nat} (A : TileIndex [M, K] → ℝ) (B : TileIndex [K, N] → ℝ) :
    TileIndex [M, N] → ℝ :=
  fun i =>
    gemmSum (fun k => if h : k < K then A (i.1, ⟨k, h⟩, PUnit.unit) else 0)
      (fun k => if h : k < K then B (⟨k, h⟩, i.2.1, PUnit.unit) else 0) K

/-- S7.2 sanity check for the unsigned specification: the Nat-indexed zero
padding is never read by `gemmSum`, whose sum stops at `K`. -/
theorem gemm_apply {M K N : Nat} (A : TileIndex [M, K] → ℝ) (B : TileIndex [K, N] → ℝ)
    (i : Fin M) (j : Fin N) :
    gemm A B (i, j, PUnit.unit) =
      ∑ k : Fin K, A (i, k, PUnit.unit) * B (k, j, PUnit.unit) := by
  unfold gemm gemmSum
  rw [Finset.sum_range]
  simp

/-- UNSIGNED. Owner: S7.2. Allgather followed by a matrix product: rank `r`
holds the product of the gathered `A` with its own `B r`. -/
noncomputable def allGatherGemm {numRanks m K N : Nat}
    (A : RankTensor numRanks (TileIndex [m, K])) (B : RankTensor numRanks (TileIndex [K, N])) :
    RankTensor numRanks (TileIndex [numRanks * m, N]) :=
  fun r => gemm (allGather A r) (B r)

/-- S7.2 sanity check for the unsigned composition: the right operand is
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

/-- UNSIGNED. Owner: S7.2. A matrix product followed by reduce-scatter: rank
`r` holds chunk `r` of the sum over ranks `q` of the products `A q * B q`. -/
noncomputable def gemmReduceScatter {numRanks m K N : Nat}
    (order : Fin numRanks → TileIndex [m, N] → ReduceOrder (Fin numRanks))
    (A : RankTensor numRanks (TileIndex [numRanks * m, K]))
    (B : RankTensor numRanks (TileIndex [K, N])) :
    RankTensor numRanks (TileIndex [m, N]) :=
  reduceScatter order fun q => gemm (A q) (B q)

/-- S7.2 sanity check for the unsigned composition: destination `r` takes
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

/-- UNSIGNED (#66). Owner: S7.2 (`ReduceScatter.lean`).
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

/-! ## All-to-all (S7.4) -/

/-- UNSIGNED. Owner: S7.4. Fixed-size all-to-all. The buffer of each rank has
one chunk of `n` rows per peer. Afterwards chunk `s` of rank `d` is what chunk
`d` of rank `s` was. -/
def allToAll {numRanks n : Nat} {ι : Type} (x : RankTensor numRanks (Fin (numRanks * n) × ι)) :
    RankTensor numRanks (Fin (numRanks * n) × ι) :=
  fun d i => x i.1.divNat (finProdFinEquiv (d, i.1.modNat), i.2)

/-- UNSIGNED. Owner: S7.4. The tables of a variable-length all-to-all.
`count s d` is the number of rows that rank `s` sends to rank `d`;
`sendOffset s d` is the first of these rows in the send buffer of `s`;
`recvOffset d s` is the first row in the receive buffer of `d` that they
fill. -/
structure AllToAllLayout (numRanks : Nat) where
  count : Fin numRanks → Fin numRanks → Nat
  sendOffset : Fin numRanks → Fin numRanks → Nat
  recvOffset : Fin numRanks → Fin numRanks → Nat

/-- UNSIGNED. Owner: S7.4. Row `p` of the receive buffer of rank `d` is filled
from rank `s`. -/
def AllToAllLayout.Receives {numRanks : Nat} (L : AllToAllLayout numRanks)
    (d s : Fin numRanks) (p : Nat) : Prop :=
  L.recvOffset d s ≤ p ∧ p < L.recvOffset d s + L.count s d

/-- UNSIGNED. Owner: S7.4. The precondition of a variable-length all-to-all:
no row of a receive buffer is filled from two sources. -/
def AllToAllLayout.WellFormed {numRanks : Nat} (L : AllToAllLayout numRanks) : Prop :=
  ∀ d s₁ s₂ p, L.Receives d s₁ p → L.Receives d s₂ p → s₁ = s₂

/-- UNSIGNED. Owner: S7.4. Variable-length all-to-all. Row `i` of the rows
that rank `s` sends to rank `d` arrives at row `recvOffset d s + i` of the
receive buffer of `d`. Rows that no source fills are not constrained. -/
def AllToAllV {numRanks : Nat} {ι : Type} (L : AllToAllLayout numRanks)
    (send recv : RankTensor numRanks (Nat × ι)) : Prop :=
  ∀ s d i, i < L.count s d → ∀ j,
    recv d (L.recvOffset d s + i, j) = send s (L.sendOffset s d + i, j)

/-! ## MoE dispatch and combine, attention chunk merge (S7.5) -/

/-- Owner: S7.5. The routing table of an MoE dispatch. Each rank has
`numTokens` tokens. Token `t` of rank `s` is sent once to each rank in
`dest s t`: the ranks that own an expert the token selects. The set may be
empty. `weight s t d` is the sum of the gate weights of the experts on rank `d`
that the token selects. -/
structure MoERouting (numRanks numTokens : Nat) where
  dest : Fin numRanks → Fin numTokens → Finset (Fin numRanks)
  weight : Fin numRanks → Fin numTokens → Fin numRanks → ℝ

/-- Owner: S7.5. A row assignment of an MoE dispatch: which token
each row of each receive buffer holds. `rows d p = some (s, t)` says that row
`p` of rank `d` holds token `t` of rank `s`; `none` says that the row holds no
token. A row holds at most one token. The assignment is not fixed in advance:
it depends on the schedule. -/
abbrev MoERows (numRanks numTokens : Nat) : Type :=
  Fin numRanks → Nat → Option (Fin numRanks × Fin numTokens)

/-- Owner: S7.5. The row assignments that a routing table allows: a
token has exactly one row on each rank it is sent to, and no row on any other
rank. An assignment that holds one token in two rows of one rank is not
allowed. -/
structure MoERouting.Assigns {numRanks numTokens : Nat} (R : MoERouting numRanks numTokens)
    (rows : MoERows numRanks numTokens) : Prop where
  existsUnique_row : ∀ s t, ∀ d ∈ R.dest s t, ∃! p, rows d p = some (s, t)
  mem_dest : ∀ d p s t, rows d p = some (s, t) → d ∈ R.dest s t

/-- Owner: S7.5. MoE dispatch with the row assignment `rows`. The
routing table allows the assignment, and every row that holds a token holds
the values of that token. Rows that hold no token are not constrained. A
dispatch guarantees this for some `rows`, not for a given one. -/
def MoEDispatch {numRanks numTokens : Nat} {ι : Type} (R : MoERouting numRanks numTokens)
    (rows : MoERows numRanks numTokens) (tokens : RankTensor numRanks (Fin numTokens × ι))
    (recv : RankTensor numRanks (Nat × ι)) : Prop :=
  R.Assigns rows ∧ ∀ d p s t, rows d p = some (s, t) → ∀ j, recv d (p, j) = tokens s (t, j)

/-- Owner: S7.5. The first step of an MoE combine. Every rank
returns the result in each row that holds a token to the rank the token came
from: `back s d (t, j)` is what rank `d` returns for token `t` of rank `s`.
Entries for a rank that holds no row of the token are not constrained. -/
def MoEStoreBack {numRanks numTokens : Nat} {ι : Type} (rows : MoERows numRanks numTokens)
    (results : RankTensor numRanks (Nat × ι))
    (back : Fin numRanks → RankTensor numRanks (Fin numTokens × ι)) : Prop :=
  ∀ d p s t, rows d p = some (s, t) → ∀ j, back s d (t, j) = results d (p, j)

/-- Owner: S7.5. The second step of an MoE combine. Token `t` of
rank `s` becomes the sum of what the ranks returned for it, added in the order
`order s t`. The order names the ranks to add: those in `dest s t`. No weight
is applied here; a returned row already carries its weight. -/
noncomputable def moeCombine {numRanks numTokens : Nat} {ι : Type}
    (order : Fin numRanks → Fin numTokens → ReduceOrder (Fin numRanks))
    (back : Fin numRanks → RankTensor numRanks (Fin numTokens × ι)) :
    RankTensor numRanks (Fin numTokens × ι) :=
  fun s i => (order s i.1).eval fun d => back s d i

/-- The generic theorem can use the destination set of a token directly. -/
example {numRanks numTokens : Nat} {ι : Type} (R : MoERouting numRanks numTokens)
    (order : Fin numRanks → Fin numTokens → ReduceOrder (Fin numRanks))
    (back : Fin numRanks → RankTensor numRanks (Fin numTokens × ι))
    (s : Fin numRanks) (t : Fin numTokens) (j : ι) (h : (order s t).CoversOn (R.dest s t)) :
    moeCombine order back s (t, j) = ∑ d ∈ R.dest s t, back s d (t, j) :=
  ReduceOrder.eval_eq_sum_of_coversOn (fun d => back s d (t, j)) h

/-- Owner: S7.5. With identity experts, combine after dispatch gives
each token times its weights, added in the order of the combine, for every row
assignment of the dispatch. An identity expert returns a received row times
the weight of its token on that rank (`hexpert`). The order adds only ranks
that the token is sent to (`horder`). -/
theorem moeCombine_of_moeDispatch {numRanks numTokens : Nat} {ι : Type}
    (R : MoERouting numRanks numTokens) (rows : MoERows numRanks numTokens)
    (order : Fin numRanks → Fin numTokens → ReduceOrder (Fin numRanks))
    (tokens : RankTensor numRanks (Fin numTokens × ι))
    (recv results : RankTensor numRanks (Nat × ι))
    (back : Fin numRanks → RankTensor numRanks (Fin numTokens × ι))
    (hdispatch : MoEDispatch R rows tokens recv)
    (hexpert : ∀ d p s t, rows d p = some (s, t) → ∀ j,
      results d (p, j) = R.weight s t d * recv d (p, j))
    (hback : MoEStoreBack rows results back)
    (horder : ∀ s t, ∀ d ∈ (order s t).leaves, d ∈ R.dest s t) :
    moeCombine order back =
      fun s i => (order s i.1).eval fun d => R.weight s i.1 d * tokens s i := sorry

/-- UNSIGNED. Owner: S7.5. The attention result of one query row over one
chunk of keys: `weight` is the softmax denominator, the sum of the
exponentiated scores of the chunk; `out` is the output row, the average of the
chunk's values with these weights. -/
structure AttentionPartial (ι : Type) where
  weight : ℝ
  out : ι → ℝ

/-- UNSIGNED. Owner: S7.5. The merge of the partial results of
`numChunks` chunks: the denominators are added, and the outputs are averaged
with the denominators as weights. Both sums use the order `order`. -/
noncomputable def attentionMerge {numChunks : Nat} {ι : Type}
    (order : ReduceOrder (Fin numChunks)) (parts : Fin numChunks → AttentionPartial ι) :
    AttentionPartial ι where
  weight := order.eval fun c => (parts c).weight
  out := fun d =>
    (order.eval fun c => (parts c).weight * (parts c).out d) /
      order.eval fun c => (parts c).weight

end VeriTile.Dist
