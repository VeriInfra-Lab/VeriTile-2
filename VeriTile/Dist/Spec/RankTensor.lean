/-
Shared rank-indexed real tensors and reduction orders for the specification
library. Coverage specifies which operands occur exactly once. The evaluation
lemmas relate trees to finite sums in a commutative additive monoid.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace VeriTile.Dist

open scoped BigOperators

/-- Owner: S7.2. One real tensor per rank: `x r i` is the element at
index `i` of the tensor of rank `r`. -/
abbrev RankTensor (numRanks : Nat) (ι : Type) : Type := Fin numRanks → ι → ℝ

/-- Owner: S7.2. The order of a sum over operands named by `ι`:
`zero` is the empty sum, `input i` is operand `i`, `add l r` adds the value of
`l` and the value of `r`. -/
inductive ReduceOrder (ι : Type) where
  | zero : ReduceOrder ι
  | input : ι → ReduceOrder ι
  | add : ReduceOrder ι → ReduceOrder ι → ReduceOrder ι

/-- Owner: S7.2. The value of a sum in the given order, with `f i`
as operand `i`, in any carrier `α` that has a zero and an addition. -/
def ReduceOrder.eval {ι α : Type} [Zero α] [Add α] (f : ι → α) : ReduceOrder ι → α
  | .zero => 0
  | .input i => f i
  | .add l r => l.eval f + r.eval f

/-- Owner: S7.2. The operands of an order, from left to right, each
as often as it occurs. -/
def ReduceOrder.leaves {ι : Type} : ReduceOrder ι → List ι
  | .zero => []
  | .input i => [i]
  | .add l r => l.leaves ++ r.leaves

/-- Evaluation is the sum of the leaf values whenever addition satisfies
the commutative monoid laws. -/
theorem ReduceOrder.eval_eq_sum_leaves {ι α : Type} [AddCommMonoid α]
    (f : ι → α) (order : ReduceOrder ι) :
    order.eval f = (order.leaves.map f).sum := by
  induction order with
  | zero => simp [eval, leaves]
  | input i => simp [eval, leaves]
  | add l r ihl ihr => simp [eval, leaves, ihl, ihr]

/-- UNSIGNED. Owner: S7.2. The left fold from zero over a list of operands:
`ofList [a, b, c]` is `((0 + a) + b) + c`. -/
def ReduceOrder.ofList {ι : Type} (operands : List ι) : ReduceOrder ι :=
  operands.foldl (fun order i => .add order (.input i)) .zero

/-- Signed (#66). Owner: S7.2 (`RankTensor.lean`).
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

/-- Signed (#66). Owner: S7.2 (`RankTensor.lean`).
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

/-- Signed (#66). Owner: S7.2 (`RankTensor.lean`).
A tree covering a finite set evaluates to the sum over that set. -/
theorem ReduceOrder.eval_eq_sum_of_coversOn {ι α : Type} [AddCommMonoid α]
    {order : ReduceOrder ι} {operands : Finset ι} (f : ι → α) (h : order.CoversOn operands) :
    order.eval f = ∑ q ∈ operands, f q := by
  classical
  obtain ⟨hn, hs⟩ := (order.coversOn_iff_toFinset operands).mp h
  rw [order.eval_eq_sum_leaves, ← hs, List.sum_toFinset f hn]

/-- Signed (#66). Owner: S7.2 (`RankTensor.lean`).
The subset sum theorem specializes to the sum over a finite index type. -/
theorem ReduceOrder.eval_eq_sum_of_covers {ι α : Type} [Fintype ι] [AddCommMonoid α]
    {order : ReduceOrder ι} (f : ι → α) (h : order.Covers) :
    order.eval f = ∑ q, f q :=
  ReduceOrder.eval_eq_sum_of_coversOn f (show order.CoversOn Finset.univ from h)

namespace ReduceOrderExamples

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

/-- Omitting a member of the subset changes the sum of two ones. -/
example : (ReduceOrder.input (1 : Nat)).eval (fun _ => (1 : Nat)) ≠
    ∑ _q ∈ ({1, 3} : Finset Nat), (1 : Nat) := by decide

/-- Repeating rank 0 changes the sum of a function supported at that rank. -/
example : (ReduceOrder.add (.input (0 : Fin 2)) (.input 0)).eval
    (fun q => if q = 0 then (1 : Nat) else 0) ≠
    ∑ q : Fin 2, (if q = 0 then (1 : Nat) else 0) := by decide

end ReduceOrderExamples
end VeriTile.Dist
