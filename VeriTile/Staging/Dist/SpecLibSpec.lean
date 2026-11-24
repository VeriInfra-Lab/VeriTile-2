/-
VeriTile.Staging.Dist.SpecLibSpec

S7.1 records the signatures for the collective specification library.
`moeCombine_of_moeDispatch`, signed on 2026-11-12 with its dependencies,
remains here. All-to-all (S7.4) and the attention merge (S7.5) remain unsigned
here.

The 2026-11-11 statements `allGather_apply` and `allReduce_eq_of_leaves_perm`
now live in `VeriTile/Dist/Spec/AllGather.lean` and
`VeriTile/Dist/Spec/AllReduce.lean`, respectively.

The declarations signed on 2026-11-23 (#66) moved to `VeriTile/Dist/Spec/` in #500.
- `RankTensor.lean` contains `ReduceOrder.CoversOn`, `ReduceOrder.Covers`,
  `ReduceOrder.eval_eq_sum_of_coversOn` and `ReduceOrder.eval_eq_sum_of_covers`.
  `ReduceOrder.ofList` and the coverage helpers also live there and remain unsigned.
- `AllReduce.lean` contains `allReduce_eq_sum_of_covers`.
- `ReduceScatter.lean` contains `reduceScatter_eq_sum_of_covers`,
  `gemmReduceScatter_eq_sum_of_covers`, `reduceScatter_twoRanks`, `gemm_apply`,
  `allGatherGemm_eq`, `allGatherGemm_apply` and `gemmReduceScatter_apply`, with
  their frozen definitions `reduceScatter`, `gemm`, `allGatherGemm` and
  `gemmReduceScatter`.

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
signed `ReduceOrder.CoversOn` contract requires exactly one leaf per
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
import VeriTile.Dist.Spec.RankTensor
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace VeriTile.Dist

open scoped BigOperators

/-! ## All-to-all (S7.4) -/

/-- UNSIGNED. Owner: S7.4. Fixed-size all-to-all. The buffer of each rank has
one chunk of `n` rows per peer. Afterwards chunk `s` of rank `d` is what chunk
`d` of rank `s` was. -/
def allToAll {numRanks n : Nat} {ι : Type} (x : RankTensor numRanks (Fin (numRanks * n) × ι)) :
    RankTensor numRanks (Fin (numRanks * n) × ι) :=
  fun d i => x i.1.divNat (finProdFinEquiv (d, i.1.modNat), i.2)

/-- UNSIGNED. Owner: S7.4. Destination `d` receives source `s`'s chunk for `d`. -/
theorem allToAll_apply {numRanks n : Nat} {ι : Type}
    (x : RankTensor numRanks (Fin (numRanks * n) × ι))
    (d s : Fin numRanks) (i : Fin n) (j : ι) :
    allToAll x d (finProdFinEquiv (s, i), j) = x s (finProdFinEquiv (d, i), j) :=
  congrArg (fun p : Fin numRanks × Fin n => x p.1 (finProdFinEquiv (d, p.2), j))
    (finProdFinEquiv.symm_apply_apply (s, i))

/-- UNSIGNED. Owner: S7.4. Swapping source and destination chunks twice restores the input. -/
theorem allToAll_involutive {numRanks n : Nat} {ι : Type}
    (x : RankTensor numRanks (Fin (numRanks * n) × ι)) : allToAll (allToAll x) = x := by
  funext d index
  obtain ⟨row, j⟩ := index
  obtain ⟨⟨s, i⟩, rfl⟩ := finProdFinEquiv.surjective row
  rw [allToAll_apply, allToAll_apply]

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

/-- UNSIGNED. Owner: S7.4. The received row has an offset within the source's payload. -/
theorem AllToAllLayout.receives_iff {numRanks : Nat} (L : AllToAllLayout numRanks)
    (d s : Fin numRanks) (p : Nat) :
    L.Receives d s p ↔ ∃ i < L.count s d, p = L.recvOffset d s + i := by
  unfold AllToAllLayout.Receives
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨p - L.recvOffset d s, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    constructor <;> omega

/-- UNSIGNED. Owner: S7.4. If both receive buffers satisfy the relation,
they agree on every row that some source fills. -/
theorem allToAllV_recv_eq_of_receives {numRanks : Nat} {ι : Type}
    {L : AllToAllLayout numRanks} {send recv₁ recv₂ : RankTensor numRanks (Nat × ι)}
    (h₁ : AllToAllV L send recv₁) (h₂ : AllToAllV L send recv₂)
    {d s : Fin numRanks} {p : Nat} (hrow : L.Receives d s p) (j : ι) :
    recv₁ d (p, j) = recv₂ d (p, j) := by
  obtain ⟨i, hi, rfl⟩ := (L.receives_iff d s p).mp hrow
  exact (h₁ s d i hi j).trans (h₂ s d i hi j).symm

/-- UNSIGNED. Owner: S7.4. Disjoint receive intervals admit a receive buffer
for every send buffer. -/
theorem allToAllV_exists_of_wellFormed {numRanks : Nat} {ι : Type}
    {L : AllToAllLayout numRanks} (hL : L.WellFormed)
    (send : RankTensor numRanks (Nat × ι)) : ∃ recv, AllToAllV L send recv := by
  classical
  refine ⟨fun d row => if h : ∃ s, L.Receives d s row.1 then
    send h.choose (L.sendOffset h.choose d + (row.1 - L.recvOffset d h.choose), row.2)
    else 0, ?_⟩
  intro s d i hi j
  have hrow : L.Receives d s (L.recvOffset d s + i) :=
    (L.receives_iff d s _).mpr ⟨i, hi, rfl⟩
  have h : ∃ q, L.Receives d q (L.recvOffset d s + i) := ⟨s, hrow⟩
  dsimp only
  rw [dif_pos h, hL d h.choose s _ h.choose_spec hrow]
  simp

/-- UNSIGNED. Owner: S7.4. Equal-size chunks in rank order on both sides. -/
def AllToAllLayout.fixedSize (numRanks n : Nat) : AllToAllLayout numRanks where
  count := fun _ _ => n
  sendOffset := fun _ d => d.val * n
  recvOffset := fun _ s => s.val * n

private theorem allToAllRow_val {numRanks n : Nat} (s : Fin numRanks) (i : Fin n) :
    (finProdFinEquiv (s, i)).val = s.val * n + i.val := by
  change i.val + n * s.val = s.val * n + i.val
  ac_rfl

/-- UNSIGNED. Owner: S7.4. Fixed-size chunks have disjoint receive intervals. -/
theorem AllToAllLayout.fixedSize_wellFormed (numRanks n : Nat) :
    (fixedSize numRanks n).WellFormed := by
  intro d s₁ s₂ p h₁ h₂
  obtain ⟨i₁, hi₁, e₁⟩ := ((fixedSize numRanks n).receives_iff d s₁ p).mp h₁
  obtain ⟨i₂, hi₂, e₂⟩ := ((fixedSize numRanks n).receives_iff d s₂ p).mp h₂
  have he : finProdFinEquiv (s₁, (⟨i₁, hi₁⟩ : Fin n)) =
      finProdFinEquiv (s₂, (⟨i₂, hi₂⟩ : Fin n)) := by
    apply Fin.ext
    rw [allToAllRow_val, allToAllRow_val]
    exact e₁.symm.trans e₂
  exact congrArg Prod.fst (finProdFinEquiv.injective he)

/-- UNSIGNED. Owner: S7.4. Restricting the equal-size relation to its
`numRanks * n` rows gives the fixed-size function. -/
theorem allToAllV_fixedSize_iff {numRanks n : Nat} {ι : Type}
    (send recv : RankTensor numRanks (Nat × ι)) :
    AllToAllV (AllToAllLayout.fixedSize numRanks n) send recv ↔
      (fun (r : Fin numRanks) (ij : Fin (numRanks * n) × ι) => recv r (ij.1.val, ij.2)) =
        allToAll (fun r ij => send r (ij.1.val, ij.2)) := by
  constructor
  · intro h
    funext d index
    obtain ⟨row, j⟩ := index
    obtain ⟨⟨s, i⟩, rfl⟩ := finProdFinEquiv.surjective row
    rw [allToAll_apply]
    simpa only [allToAllRow_val, AllToAllLayout.fixedSize] using h s d i.val i.isLt j
  · intro h s d i hi j
    have he := congrFun (congrFun h d) (finProdFinEquiv (s, (⟨i, hi⟩ : Fin n)), j)
    rw [allToAll_apply] at he
    simpa only [allToAllRow_val, AllToAllLayout.fixedSize] using he

namespace AllToAllExamples

private def overlap : AllToAllLayout 2 where
  count := fun _ _ => 1
  sendOffset := fun _ _ => 0
  recvOffset := fun _ _ => 0

example : ¬ overlap.WellFormed := by
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1)
    (h 0 0 1 0 (by simp [overlap, AllToAllLayout.Receives])
      (by simp [overlap, AllToAllLayout.Receives]))

/-- Conflicting writes to the same covered row admit no receive buffer. -/
example : ¬ ∃ recv : RankTensor 2 (Nat × Unit),
    AllToAllV overlap (fun s _ => if s = 0 then 0 else 1) recv := by
  rintro ⟨recv, h⟩
  have h₀ := h 0 0 0 (by decide) ()
  have h₁ := h 1 0 0 (by decide) ()
  change recv 0 (0, ()) = 0 at h₀
  change recv 0 (0, ()) = 1 at h₁
  rw [h₀] at h₁
  norm_num at h₁

/-- With equal payloads, distinct solutions can differ at uncovered rows. -/
example : ∃ recv₀ recv₁ : RankTensor 2 (Nat × Unit), recv₀ ≠ recv₁ ∧
    AllToAllV overlap (fun _ _ => 0) recv₀ ∧ AllToAllV overlap (fun _ _ => 0) recv₁ := by
  refine ⟨fun _ _ => 0, fun _ row => if row.1 = 0 then 0 else 1, ?_, ?_, ?_⟩
  · intro h
    have he := congrFun (congrFun h 0) (1, ())
    change (0 : ℝ) = 1 at he
    norm_num at he
  · intro _ _ _ _ _
    rfl
  · intro s d i hi j
    change i < 1 at hi
    obtain rfl : i = 0 := by omega
    rfl

end AllToAllExamples

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
