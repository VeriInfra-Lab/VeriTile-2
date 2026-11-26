import VeriTile.Triton.Core.Reshape

/-! Executable row-major reshape indices. The equality used by the compiler
keeps the upstream specification and the interpreter's refinement proofs intact. -/
namespace VeriTile.Interp

open VeriTile.Triton

private theorem get_product {β γ : Type} (xs : List β) (ys : List γ)
    (i j : Nat) (hi : i < xs.length) (hj : j < ys.length) :
    (xs.flatMap fun x => ys.map (x, ·))[i * ys.length + j]? = some (xs[i], ys[j]) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp [List.flatMap_cons, List.getElem?_append_left (by simpa using hj : j < (ys.map (x, ·)).length),
        List.getElem?_eq_getElem hj]
    | succ i =>
      simp only [List.flatMap_cons, Nat.succ_mul, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by simp; omega), List.length_map]
      convert ih i (by simpa using hi) using 2; omega

/-- Looking up the row-major offset in the specification enumerates the original index. -/
theorem get_allIndices (sh : TileShape) (i : TileIndex sh) :
    (TileShape.allIndices sh)[TileShape.linearIndex sh i]? = some i := by
  induction sh with
  | nil => cases i; rfl
  | cons n sh ih =>
    rcases i with ⟨x, y⟩
    have hy := TileShape.linearIndex_lt sh y
    have he := get_product (List.finRange n) (TileShape.allIndices sh) x.val
      (TileShape.linearIndex sh y) (by simp) (by simpa using hy)
    simpa [TileShape.allIndices_cons, TileShape.linearIndex, List.getElem_finRange,
      (List.getElem?_eq_some_iff.mp (ih y)).2] using he

/-- Accumulate the offset from the outermost coordinate inward. -/
private def flatten : (sh : TileShape) → TileIndex sh → Nat → Nat
  | [], _, acc => acc
  | n :: sh, (j, js), acc => flatten sh js (acc * n + j.val)

private theorem flatten_eq (sh : TileShape) (i : TileIndex sh) (acc : Nat) :
    flatten sh i acc = acc * TileShape.product sh + TileShape.linearIndex sh i := by
  induction sh generalizing acc with
  | nil => simp [flatten, TileShape.product, TileShape.linearIndex]
  | cons n sh ih =>
    rcases i with ⟨j, js⟩
    rw [flatten, ih]
    simp [TileShape.product, TileShape.linearIndex, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

/-- Split a flat offset by the stride of each axis. Carrying the remaining
element count gives the next stride in one division, even for a high-rank tile. -/
private def unflatten : (sh : TileShape) → (size : Nat) → size = TileShape.product sh →
    Fin size → TileIndex sh
  | [], _, _, _ => ()
  | n :: sh, size, h, i =>
    have pos : 0 < n * TileShape.product sh := by
      simpa only [h, TileShape.product] using Nat.zero_lt_of_lt i.isLt
    let stride := size / n
    have hs : stride = TileShape.product sh := by
      simp [stride, h, TileShape.product, Nat.mul_div_cancel_left _ (Nat.pos_of_mul_pos_right pos)]
    have nonzero : 0 < stride := hs ▸ Nat.pos_of_mul_pos_left pos
    have hi : i.val < n * stride := by simpa only [hs, h, TileShape.product] using i.isLt
    (⟨i / stride, (Nat.div_lt_iff_lt_mul nonzero).2 hi⟩,
      unflatten sh stride hs ⟨i % stride, Nat.mod_lt _ nonzero⟩)

private theorem linearIndex_unflatten (sh : TileShape) (size : Nat)
    (h : size = TileShape.product sh) (i : Fin size) :
    TileShape.linearIndex sh (unflatten sh size h i) = i.val := by
  induction sh generalizing size with
  | nil =>
    have hi := i.isLt
    simp only [TileShape.product] at h
    simp only [TileShape.linearIndex]; omega
  | cons n sh ih =>
    have pos : 0 < n * TileShape.product sh := by
      simpa only [h, TileShape.product] using Nat.zero_lt_of_lt i.isLt
    have hs : size / n = TileShape.product sh := by
      simp [h, TileShape.product, Nat.mul_div_cancel_left _ (Nat.pos_of_mul_pos_right pos)]
    simp only [unflatten, TileShape.linearIndex, ih]
    rw [← hs]
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div i.val (size / n)

/-- Rank-linear mixed-radix lookup. Its cost is independent of the number of
tile elements at fixed rank; it constructs neither an index list nor an array. -/
def reshapeIndexFast {input output : TileShape} (h : TileShape.product input = TileShape.product output)
    (i : TileIndex output) : TileIndex input :=
  unflatten input (TileShape.product input) rfl ⟨flatten output i 0, by
    simpa [flatten_eq, h] using TileShape.linearIndex_lt output i⟩

/-- Compile the interpreter with the proved arithmetic lookup. -/
@[csimp] theorem reshapeIndex_eq_fast : @TileShape.reshapeIndex = @reshapeIndexFast := by
  funext input output h i
  have hi : TileShape.linearIndex input (reshapeIndexFast h i) = TileShape.linearIndex output i := by
    simp [reshapeIndexFast, linearIndex_unflatten, flatten_eq]
  have found := get_allIndices input (reshapeIndexFast h i)
  rw [hi] at found
  exact (List.getElem?_eq_some_iff.mp found).2

end VeriTile.Interp
