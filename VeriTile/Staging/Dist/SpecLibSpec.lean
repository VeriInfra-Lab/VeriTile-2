/-
VeriTile.Staging.Dist.SpecLibSpec

S7.1 records the signatures for the collective specification library.
`moeCombine_of_moeDispatch`, signed on 2026-11-12 with its dependencies,
remains here. The attention merge (S7.5) remains unsigned here.

The all-to-all (S7.4) declarations signed on 2026-11-24 (#66, #69)
now live in `VeriTile/Dist/Spec/AllToAll.lean`. The seven signed statements
are `allToAll_apply`, `allToAll_involutive`,
`AllToAllLayout.receives_iff`, `allToAllV_recv_eq_of_receives`,
`allToAllV_exists_of_wellFormed`, `AllToAllLayout.fixedSize_wellFormed` and
`allToAllV_fixedSize_iff`, which freeze `allToAll`, `AllToAllLayout`,
`AllToAllLayout.Receives`, `AllToAllLayout.WellFormed`, `AllToAllV` and
`AllToAllLayout.fixedSize`. The additional step-2 lemmas live in the same
module and remain unsigned.

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
import VeriTile.Dist.Spec.AllToAll
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FinCases

namespace VeriTile.Dist

open scoped BigOperators

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
      fun s i => (order s i.1).eval fun d => R.weight s i.1 d * tokens s i := by
  funext s ⟨t, j⟩
  simp only [moeCombine, ReduceOrder.eval_eq_sum_leaves]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  obtain ⟨p, row, _⟩ := hdispatch.1.existsUnique_row s t d (horder s t d hd)
  rw [hback d p s t row j, hexpert d p s t row j, hdispatch.2 d p s t row j]

/-- With full coverage of the routed ranks and normalized gates, identity
experts reconstruct the original token, including all of its features. -/
theorem moeCombine_identity_of_normalized {n t : Nat} {ι : Type} (R : MoERouting n t)
    (rows : MoERows n t) (order : Fin n → Fin t → ReduceOrder (Fin n))
    (tokens : RankTensor n (Fin t × ι)) (recv results : RankTensor n (Nat × ι))
    (back : Fin n → RankTensor n (Fin t × ι)) (dispatch : MoEDispatch R rows tokens recv)
    (expert : ∀ d p s tok, rows d p = some (s,tok) → ∀ j,
      results d (p,j) = R.weight s tok d * recv d (p,j))
    (store : MoEStoreBack rows results back)
    (covers : ∀ s tok, (order s tok).CoversOn (R.dest s tok))
    (normalized : ∀ s tok, ∑ d ∈ R.dest s tok, R.weight s tok d = 1) :
    moeCombine order back = tokens := by
  rw [moeCombine_of_moeDispatch R rows order tokens recv results back dispatch expert store
    (fun s tok d hd => ((covers s tok).2 d).mp hd)]
  funext s i
  change (order s i.1).eval (fun d => R.weight s i.1 d * tokens s i) = tokens s i
  rw [ReduceOrder.eval_eq_sum_of_coversOn _ (covers s i.1), ← Finset.sum_mul, normalized, one_mul]

/-- UNSIGNED. Owner: S7.5. The attention result of one query row over one
chunk of keys: `weight` is the softmax denominator, the sum of the
exponentiated scores of the chunk; `out` is the output row, the average of the
chunk's values with these weights. -/
structure AttentionPartial (ι : Type) where
  weight : ℝ
  out : ι → ℝ

/-- UNSIGNED. Owner: S7.5. The merge of the partial results of
`numChunks` chunks: the denominators are added, and the outputs are averaged
with the denominators as weights. Both sums use the tree `order`. Claims about
all chunks use `order.Covers`. A zero total denominator gives zero coordinates
under the total division on exact reals. -/
noncomputable def attentionMerge {numChunks : Nat} {ι : Type}
    (order : ReduceOrder (Fin numChunks)) (parts : Fin numChunks → AttentionPartial ι) :
    AttentionPartial ι where
  weight := order.eval fun c => (parts c).weight
  out := fun d =>
    (order.eval fun c => (parts c).weight * (parts c).out d) /
      order.eval fun c => (parts c).weight

/-- UNSIGNED. Compute one chunk from the query row's unnormalized scores and
value rows. The same tree selects and orders keys in both reductions. The empty
tree has zero mass and returns zero in every coordinate by exact-real division. -/
noncomputable def AttentionPartial.ofScores {key ι : Type} (keys : ReduceOrder key)
    (score : key → ℝ) (value : key → ι → ℝ) : AttentionPartial ι :=
  let mass := keys.eval (fun k => Real.exp (score k))
  ⟨mass,fun j => keys.eval (fun k => Real.exp (score k) * value k j) / mass⟩

private theorem expMass {key : Type} (keys : ReduceOrder key) (score : key → ℝ) :
    0 ≤ keys.eval (fun k => Real.exp (score k)) ∧
      (keys.eval (fun k => Real.exp (score k)) = 0 → keys.leaves = []) := by
  induction keys with
  | zero => exact ⟨le_rfl,fun _ => rfl⟩
  | input k => exact ⟨(Real.exp_pos _).le,fun h => False.elim ((Real.exp_pos _).ne' h)⟩
  | add l r hl hr =>
    refine ⟨add_nonneg hl.1 hr.1,?_⟩
    intro zero
    change l.eval _ + r.eval _ = 0 at zero
    obtain ⟨a,b⟩ := (add_eq_zero_iff_of_nonneg hl.1 hr.1).mp zero
    simp [ReduceOrder.leaves,hl.2 a,hr.2 b]

/-- UNSIGNED. Recover the unnormalized numerator even for an empty chunk. -/
theorem AttentionPartial.ofScores_mass_out {key ι : Type} (keys : ReduceOrder key)
    (score : key → ℝ) (value : key → ι → ℝ) (j : ι) :
    (ofScores keys score value).weight * (ofScores keys score value).out j =
      keys.eval (fun k => Real.exp (score k) * value k j) := by
  unfold ofScores
  dsimp only
  by_cases h : keys.eval (fun k => Real.exp (score k)) = 0
  · rw [h,zero_mul,ReduceOrder.eval_eq_sum_leaves,(expMass keys score).2 h]
    simp
  · exact mul_div_cancel₀ _ h

/-- UNSIGNED. A merge of actual query chunks recovers the exact numerator and
denominator across all selected keys, with both levels of reduction explicit. -/
theorem attentionMerge_ofScores {n : Nat} {key ι : Type} (order : ReduceOrder (Fin n))
    (keys : Fin n → ReduceOrder key) (scores : Fin n → key → ℝ) (values : Fin n → key → ι → ℝ) :
    let parts := fun c => AttentionPartial.ofScores (keys c) (scores c) (values c)
    (attentionMerge order parts).weight = order.eval (fun c => (keys c).eval (fun k => Real.exp (scores c k))) ∧
    ∀ j, (attentionMerge order parts).out j =
      order.eval (fun c => (keys c).eval (fun k => Real.exp (scores c k) * values c k j)) /
      order.eval (fun c => (keys c).eval (fun k => Real.exp (scores c k))) := by
  refine ⟨rfl,?_⟩
  intro j
  simp only [attentionMerge,AttentionPartial.ofScores_mass_out]
  rfl

/-- UNSIGNED. An all-chunk claim must cover every chunk exactly once. Under
that condition the observable denominator and output have the finite-sum form. -/
theorem attentionMerge_of_covers {n : Nat} {ι : Type} (order : ReduceOrder (Fin n))
    (parts : Fin n → AttentionPartial ι) (covers : order.Covers) :
    (attentionMerge order parts).weight = ∑ c, (parts c).weight ∧
    ∀ j, (attentionMerge order parts).out j = (∑ c, (parts c).weight * (parts c).out j) / ∑ c, (parts c).weight := by
  refine ⟨ReduceOrder.eval_eq_sum_of_covers _ covers,fun j => ?_⟩
  simp only [attentionMerge,ReduceOrder.eval_eq_sum_of_covers _ covers]

namespace S75Examples

private def oneRoute : MoERouting 1 1 := ⟨fun _ _ => {0},fun _ _ _ => 1⟩
private def rows (duplicate : Bool) : MoERows 1 1 := fun _ p =>
  if p = 0 ∨ (duplicate = true ∧ p = 1) then some (0,0) else none

/-- Two rows of the same destination contain the same token. Even correct
payloads in both rows cannot make this a valid dispatch. -/
theorem duplicate_dispatch (tokens : RankTensor 1 (Fin 1 × Unit)) (recv : RankTensor 1 (Nat × Unit)) :
    ¬ MoEDispatch oneRoute (rows true) tokens recv := by
  intro h
  obtain ⟨p,_,unique⟩ := h.1.existsUnique_row 0 0 0 (by simp [oneRoute])
  have h0 := unique 0 (by decide)
  have h1 := unique 1 (by decide)
  omega

theorem single_route_readback :
    let tokens : RankTensor 1 (Fin 1 × Unit) := fun _ _ => 9
    let recv : RankTensor 1 (Nat × Unit) := fun _ _ => 9
    let back : Fin 1 → RankTensor 1 (Fin 1 × Unit) := fun _ _ _ => 9
    MoEDispatch oneRoute (rows false) tokens recv ∧
      MoEStoreBack (rows false) recv back ∧
      moeCombine (fun _ _ => .input 0) back (0 : Fin 1) (0,()) = 9 := by
  refine ⟨⟨⟨?_,?_⟩,by intros; rfl⟩,by intro d p s t row j; rfl,rfl⟩
  · intro s t d _
    fin_cases s; fin_cases t; fin_cases d
    refine ⟨0,rfl,?_⟩
    intro p h
    simpa [rows] using h
  · intro d p s t _
    fin_cases d; simp [oneRoute]

/-- One chunk contributes two zero-score keys valued 3 and 9; the other
contributes one key valued 18. The three keys have equal mass. -/
theorem chunk_readback :
    let ks : Fin 2 → ReduceOrder (Fin 2) := fun c =>
      if c = 0 then .add (.input 0) (.input 1) else .input 0
    let values : Fin 2 → Fin 2 → Unit → ℝ := fun c k _ =>
      if c = 0 then (if k = 0 then 3 else 9) else 18
    let merged := attentionMerge (.add (.input 1) (.input 0))
      (fun c => AttentionPartial.ofScores (ks c) (fun _ => 0) (values c))
    merged.weight = 3 ∧ merged.out () = 10 := by
  norm_num [attentionMerge,AttentionPartial.ofScores,ReduceOrder.eval]

theorem empty_merge : (attentionMerge (.zero : ReduceOrder (Fin 0))
    (fun c => Fin.elim0 c : Fin 0 → AttentionPartial Unit)).out () = 0 := by
  simp [attentionMerge,ReduceOrder.eval]

end S75Examples

end VeriTile.Dist
