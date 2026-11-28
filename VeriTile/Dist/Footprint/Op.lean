/-
VeriTile.Dist.Footprint.Op

The cells that an upstream expression reads, computed from the state it is
evaluated in (S3.3, #45). `opReads e s` is the set of cells that `evalOp e s`
reads: the active lanes of every load in `e`, with addresses, masks and
`other` operands evaluated in `s`. `accessCells` is the set of cells a memory
operand addresses at given lanes; statements use it for their stores and
atomics (`VeriTile/Dist/Footprint/Stmt.lean`).

`opReads_congr`: on two states that agree on a set containing `opReads e s₁`
and on every field that is not memory, `e` evaluates the same and reads the
same cells.
-/
import VeriTile.Triton.Memory.Locality

namespace VeriTile.Dist

open VeriTile.Triton

/-- A memory cell of an upstream block state: a region name and an offset. -/
abbrev BlockCell := RegionName × Nat

/-- The two states agree on the cells of `Q` and on every field that is not
memory. -/
abbrev BlockAgree (Q : Set BlockCell) (s₁ s₂ : BlockState) : Prop :=
  s₁.AgreeOn (fun r o => (r, o) ∈ Q) s₂

/-- The cells that a memory operand addresses in state `s`, at the lanes where
`active` holds. A checked block pointer addresses only its in-bounds lanes. -/
def accessCells {d : TileDType} {sh : TileShape} (mem : MemAccess d sh) (s : BlockState)
    (active : TileIndex sh → Prop) : Set BlockCell :=
  match mem with
  | .region r off => {c | ∃ offs, evalOp off s = some offs ∧ ∃ i, active i ∧
      c = (Region.cast r, offs.data i)}
  | .ptr p => {c | ∃ ps, evalOp p s = some ps ∧ ∃ i, active i ∧
      c = ((ps.data i).1, (ps.data i).2)}
  | .blockPtr p bc => {c | ∃ ps, evalOp p s = some ps ∧ ∃ i, active i ∧
      (ps.data i).inBounds (TileShape.indexToList sh i) bc = true ∧
      c = ((ps.data i).region, (ps.data i).address (TileShape.indexToList sh i))}

set_option maxHeartbeats 1600000 in
/-- The cells that `evalOp e s` reads: the active lanes of each load in `e`,
with its address, mask and `other` operand evaluated in `s`. -/
def opReads : Op d sh → BlockState → Set BlockCell
  | .const _, _ => ∅
  | .constFloat _ _, _ => ∅
  | .constNat _, _ => ∅
  | .constInt _, _ => ∅
  | .constBool _, _ => ∅
  | .negInf, _ => ∅
  | .programId _, _ => ∅
  | .numPrograms _, _ => ∅
  | .ref _ _ _, _ => ∅
  | .arange _, _ => ∅
  | .philox4x32 _ _ _ seed c0 c1 c2 c3, s => opReads seed s ∪ (opReads c0 s ∪ (opReads c1 s ∪ (opReads c2 s ∪ opReads c3 s)))
  | .uniform32 word, s => opReads word s
  | .rand _ seed offsets, s => opReads seed s ∪ opReads offsets s
  | .randTensor _ seed offsets, s => opReads seed s ∪ opReads offsets s
  | .broadcast e _, s => opReads e s
  | .full _ e, s => opReads e s
  | .withPrecision _ _ e, s => opReads e s
  | .castFloat _ _ e, s => opReads e s
  | .castNatToInt e, s => opReads e s
  | .negFloat _ e, s => opReads e s
  | .absFloat _ e, s => opReads e s
  | .floatToInt _ _ _ e, s => opReads e s
  | .floatToNat _ _ _ e, s => opReads e s
  | .castIntToNat e, s => opReads e s
  | .castRealToInt8 e, s => opReads e s
  | .decodeFloat8E5 _ e, s => opReads e s
  | .add _ _ a b, s => opReads a s ∪ opReads b s
  | .sub _ _ a b, s => opReads a s ∪ opReads b s
  | .mul _ _ a b, s => opReads a s ∪ opReads b s
  | .div _ _ a b, s => opReads a s ∪ opReads b s
  | .divRN _ a b, s => opReads a s ∪ opReads b s
  | .floorDiv _ _ a b, s => opReads a s ∪ opReads b s
  | .mod _ _ a b, s => opReads a s ∪ opReads b s
  | .bitAnd _ a b, s => opReads a s ∪ opReads b s
  | .bitOr _ a b, s => opReads a s ∪ opReads b s
  | .bitXor _ a b, s => opReads a s ∪ opReads b s
  | .shiftLeft _ a b, s => opReads a s ∪ opReads b s
  | .shiftRight _ a b, s => opReads a s ∪ opReads b s
  | .exp a, s => opReads a s
  | .libdeviceExp a, s => opReads a s
  | .libdeviceLog a, s => opReads a s
  | .libdeviceExpm1 a, s => opReads a s
  | .libdeviceTanh a, s => opReads a s
  | .libdeviceLog1p a, s => opReads a s
  | .exp2 a, s => opReads a s
  | .log a, s => opReads a s
  | .log2 a, s => opReads a s
  | .sigmoid a, s => opReads a s
  | .sqrt a, s => opReads a s
  | .rsqrt a, s => opReads a s
  | .libdeviceRsqrt a, s => opReads a s
  | .tanh a, s => opReads a s
  | .sin a, s => opReads a s
  | .cos a, s => opReads a s
  | .tan a, s => opReads a s
  | .atan a, s => opReads a s
  | .cosh a, s => opReads a s
  | .sinh a, s => opReads a s
  | .erf a, s => opReads a s
  | .minPosInf a, s => opReads a s
  | .lt _ _ a b, s => opReads a s ∪ opReads b s
  | .le _ _ a b, s => opReads a s ∪ opReads b s
  | .eq _ _ a b, s => opReads a s ∪ opReads b s
  | .gt _ _ a b, s => opReads a s ∪ opReads b s
  | .ge _ _ a b, s => opReads a s ∪ opReads b s
  | .ne _ _ a b, s => opReads a s ∪ opReads b s
  | .boolAnd _ a b, s => opReads a s ∪ opReads b s
  | .boolOr _ a b, s => opReads a s ∪ opReads b s
  | .boolNot a, s => opReads a s
  | .max2 _ a b, s => opReads a s ∪ opReads b s
  | .maximumFloat _ _ a b, s => opReads a s ∪ opReads b s
  | .minimumFloat _ _ a b, s => opReads a s ∪ opReads b s
  | .pow _ a b, s => opReads a s ∪ opReads b s
  | .libdevicePowi _ a b, s => opReads a s ∪ opReads b s
  | .where c a b, s => opReads c s ∪ (opReads a s ∪ opReads b s)
  | .ite c a b, s => opReads c s ∪ (opReads a s ∪ opReads b s)
  | .reduceMin _ _ a, s => opReads a s
  | .reduceMax _ _ a, s => opReads a s
  | .reduceMaxNat _ _ a, s => opReads a s
  | .reduceMaxInt _ _ a, s => opReads a s
  | .reduceSum _ _ a, s => opReads a s
  | .reduceSumBool _ _ a, s => opReads a s
  | .reduceSumTyped _ _ _ a, s => opReads a s
  | .reduceMaxTyped _ _ _ a, s => opReads a s
  | .scan _ _ _ a, s => opReads a s
  | .argMax _ a, s => opReads a s
  | .argMaxInt _ a, s => opReads a s
  | .argMaxTyped _ _ a _, s => opReads a s
  | .indexedMaxValue _ _ a, s => opReads a s
  | .argMin _ a, s => opReads a s
  | .sort _ a, s => opReads a s
  | .dot a b _, s => opReads a s ∪ opReads b s
  | .dotAcc _ _ _ a b acc _, s => opReads a s ∪ (opReads b s ∪ opReads acc s)
  | .dotTyped _ _ _ a b _, s => opReads a s ∪ opReads b s
  | .dotInt a b _, s => opReads a s ∪ opReads b s
  | .transpose a, s => opReads a s
  | .reshape _ a, s => opReads a s
  | .remap _ _ a, s => opReads a s
  | .join a b, s => opReads a s ∪ opReads b s
  | .split _ a, s => opReads a s
  | .expandDim _ a, s => opReads a s
  | .ptrBase _, _ => ∅
  | .ptrAdd _ ptr off, s => opReads ptr s ∪ opReads off s
  | .ptrSub _ ptr off, s => opReads ptr s ∪ opReads off s
  | .makeBlockPtr _ _ _ _ _ _, _ => ∅
  | .makeBlockPtrDyn _ base _ _ _ _, s => opReads base s
  | .makeBlockPtrDynOffsets _ base _ _ _ offsets, s =>
      opReads base s ∪ {c | ∃ off, ∃ _ : off ∈ offsets, c ∈ opReads off s}
  | .makeBlockPtrDynMetadata _ base _ _ strides offsets, s =>
      opReads base s ∪ ({c | ∃ stride, ∃ _ : stride ∈ strides, c ∈ opReads stride s} ∪
        {c | ∃ off, ∃ _ : off ∈ offsets, c ∈ opReads off s})
  | .advanceBlockPtr ptr _, s => opReads ptr s
  | .advanceBlockPtrDyn ptr deltas, s =>
      opReads ptr s ∪ {c | ∃ delta, ∃ _ : delta ∈ deltas, c ∈ opReads delta s}
  | .load _ mem mask _, s =>
      (match mem with
        | .region _ off => opReads off s
        | .ptr ptr => opReads ptr s
        | .blockPtr ptr _ => opReads ptr s) ∪
      ((match mask with
        | .none => ∅
        | .mask m => opReads m s
        | .maskOther m other => opReads m s ∪ opReads other s) ∪
      accessCells mem s (mask.Active s))
  | .natToReal a, s => opReads a s
  | .intToReal a, s => opReads a s

/-- `mapM` over scalar operands agrees when each operand evaluates the same. -/
theorem mapM_data_congr {dtype : TileDType} (s₁ s₂ : BlockState) :
    ∀ (l : List (Op dtype [])),
      (∀ off ∈ l, evalOp off s₁ = evalOp off s₂) →
      l.mapM (fun off => do
          let v ← evalOp off s₁
          some (v.data PUnit.unit))
        = l.mapM (fun off => do
            let v ← evalOp off s₂
            some (v.data PUnit.unit))
  | [], _ => rfl
  | o :: rest, h => by
      simp only [List.mapM_cons]
      rw [h o (List.mem_cons_self ..)]
      cases evalOp o s₂ with
      | none => rfl
      | some v =>
          rw [mapM_data_congr s₁ s₂ rest
            (fun off hoff => h off (List.mem_cons_of_mem _ hoff))]

theorem listReads_congr {α : Type} (l : List α) {f g : α → Set BlockCell}
    (h : ∀ x ∈ l, f x = g x) :
    {c | ∃ x, ∃ _ : x ∈ l, c ∈ f x} = {c | ∃ x, ∃ _ : x ∈ l, c ∈ g x} := by
  ext c
  exact ⟨fun ⟨x, hx, hc⟩ => ⟨x, hx, h x hx ▸ hc⟩, fun ⟨x, hx, hc⟩ => ⟨x, hx, (h x hx).symm ▸ hc⟩⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 3200000 in
/-- Evaluation reads only `opReads`: on two states that agree on a set `Q`
containing it, an op evaluates the same, and reads the same cells. -/
theorem opReads_congr (Q : Set BlockCell) :
    ∀ {d : TileDType} {sh : TileShape} (e : Op d sh) (s₁ s₂ : BlockState),
      BlockAgree Q s₁ s₂ → opReads e s₁ ⊆ Q →
      evalOp e s₁ = evalOp e s₂ ∧ opReads e s₂ = opReads e s₁
  | _, _, .const _, s₁, s₂, hag, hms => by
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids], by simp only [opReads]⟩
  | _, _, .constFloat _ _, s₁, s₂, hag, hms => by
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids], by simp only [opReads]⟩
  | _, _, .constNat _, s₁, s₂, hag, hms => by
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids], by simp only [opReads]⟩
  | _, _, .constInt _, s₁, s₂, hag, hms => by
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids], by simp only [opReads]⟩
  | _, _, .constBool _, s₁, s₂, hag, hms => by
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids], by simp only [opReads]⟩
  | _, _, .negInf, s₁, s₂, hag, hms => by
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids], by simp only [opReads]⟩
  | _, _, .programId _, s₁, s₂, hag, hms => by
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids], by simp only [opReads]⟩
  | _, _, .numPrograms _, s₁, s₂, hag, hms => by
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids], by simp only [opReads]⟩
  | _, _, .ref _ _ _, s₁, s₂, hag, hms => by
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids], by simp only [opReads]⟩
  | _, _, .arange _, s₁, s₂, hag, hms => by
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids], by simp only [opReads]⟩
  | _, _, .philox4x32 _ _ _ seed c0 c1 c2 c3, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_seed := opReads_congr Q seed s₁ s₂ hag hms.1
      have ih_c0 := opReads_congr Q c0 s₁ s₂ hag hms.2.1
      have ih_c1 := opReads_congr Q c1 s₁ s₂ hag hms.2.2.1
      have ih_c2 := opReads_congr Q c2 s₁ s₂ hag hms.2.2.2.1
      have ih_c3 := opReads_congr Q c3 s₁ s₂ hag hms.2.2.2.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_seed.1, ih_c0.1, ih_c1.1, ih_c2.1, ih_c3.1], by simp only [opReads, ih_seed.2, ih_c0.2, ih_c1.2, ih_c2.2, ih_c3.2]⟩
  | _, _, .uniform32 word, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_word := opReads_congr Q word s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_word.1], by simp only [opReads, ih_word.2]⟩
  | _, _, .rand _ seed offsets, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_seed := opReads_congr Q seed s₁ s₂ hag hms.1
      have ih_offsets := opReads_congr Q offsets s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_seed.1, ih_offsets.1], by simp only [opReads, ih_seed.2, ih_offsets.2]⟩
  | _, _, .randTensor _ seed offsets, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_seed := opReads_congr Q seed s₁ s₂ hag hms.1
      have ih_offsets := opReads_congr Q offsets s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_seed.1, ih_offsets.1], by simp only [opReads, ih_seed.2, ih_offsets.2]⟩
  | _, _, .broadcast e _, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_e := opReads_congr Q e s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_e.1], by simp only [opReads, ih_e.2]⟩
  | _, _, .full _ e, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_e := opReads_congr Q e s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_e.1], by simp only [opReads, ih_e.2]⟩
  | _, _, .withPrecision _ _ e, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_e := opReads_congr Q e s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_e.1], by simp only [opReads, ih_e.2]⟩
  | _, _, .castFloat _ _ e, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_e := opReads_congr Q e s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_e.1], by simp only [opReads, ih_e.2]⟩
  | _, _, .castNatToInt e, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_e := opReads_congr Q e s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_e.1], by simp only [opReads, ih_e.2]⟩
  | _, _, .negFloat _ e, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_e := opReads_congr Q e s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_e.1], by simp only [opReads, ih_e.2]⟩
  | _, _, .absFloat _ e, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_e := opReads_congr Q e s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_e.1], by simp only [opReads, ih_e.2]⟩
  | _, _, .floatToInt _ _ _ e, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_e := opReads_congr Q e s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_e.1], by simp only [opReads, ih_e.2]⟩
  | _, _, .floatToNat _ _ _ e, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_e := opReads_congr Q e s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_e.1], by simp only [opReads, ih_e.2]⟩
  | _, _, .castIntToNat e, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_e := opReads_congr Q e s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_e.1], by simp only [opReads, ih_e.2]⟩
  | _, _, .castRealToInt8 e, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_e := opReads_congr Q e s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_e.1], by simp only [opReads, ih_e.2]⟩
  | _, _, .decodeFloat8E5 _ e, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_e := opReads_congr Q e s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_e.1], by simp only [opReads, ih_e.2]⟩
  | _, _, .add _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .sub _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .mul _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .div _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .divRN _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .floorDiv _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .mod _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .bitAnd _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .bitOr _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .bitXor _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .shiftLeft _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .shiftRight _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .exp a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .libdeviceExp a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .libdeviceLog a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .libdeviceExpm1 a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .libdeviceTanh a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .libdeviceLog1p a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .exp2 a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .log a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .log2 a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .sigmoid a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .sqrt a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .rsqrt a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .libdeviceRsqrt a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .tanh a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .sin a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .cos a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .tan a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .atan a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .cosh a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .sinh a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .erf a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .minPosInf a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .lt _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .le _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .eq _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .gt _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .ge _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .ne _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .boolAnd _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .boolOr _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .boolNot a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .max2 _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .maximumFloat _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .minimumFloat _ _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .pow _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .libdevicePowi _ a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .where c a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_c := opReads_congr Q c s₁ s₂ hag hms.1
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.2.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_c.1, ih_a.1, ih_b.1], by simp only [opReads, ih_c.2, ih_a.2, ih_b.2]⟩
  | _, _, .ite c a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_c := opReads_congr Q c s₁ s₂ hag hms.1
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.2.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_c.1, ih_a.1, ih_b.1], by simp only [opReads, ih_c.2, ih_a.2, ih_b.2]⟩
  | _, _, .reduceMin _ _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .reduceMax _ _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .reduceMaxNat _ _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .reduceMaxInt _ _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .reduceSum _ _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .reduceSumBool _ _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .reduceSumTyped _ _ _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .reduceMaxTyped _ _ _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .scan _ _ _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .argMax _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .argMaxInt _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .argMaxTyped _ _ a _, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .indexedMaxValue _ _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .argMin _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .sort _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .dot a b _, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .dotAcc _ _ _ a b acc _, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2.1
      have ih_acc := opReads_congr Q acc s₁ s₂ hag hms.2.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1, ih_acc.1], by simp only [opReads, ih_a.2, ih_b.2, ih_acc.2]⟩
  | _, _, .dotTyped _ _ _ a b _, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .dotInt a b _, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .transpose a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .reshape _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .remap _ _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .join a b, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms.1
      have ih_b := opReads_congr Q b s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1, ih_b.1], by simp only [opReads, ih_a.2, ih_b.2]⟩
  | _, _, .split _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .expandDim _ a, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .ptrBase _, s₁, s₂, hag, hms => by
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids], by simp only [opReads]⟩
  | _, _, .ptrAdd _ ptr off, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_ptr := opReads_congr Q ptr s₁ s₂ hag hms.1
      have ih_off := opReads_congr Q off s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_ptr.1, ih_off.1], by simp only [opReads, ih_ptr.2, ih_off.2]⟩
  | _, _, .ptrSub _ ptr off, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_ptr := opReads_congr Q ptr s₁ s₂ hag hms.1
      have ih_off := opReads_congr Q off s₁ s₂ hag hms.2
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_ptr.1, ih_off.1], by simp only [opReads, ih_ptr.2, ih_off.2]⟩
  | _, _, .makeBlockPtr _ _ _ _ _ _, s₁, s₂, hag, hms => by
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids], by simp only [opReads]⟩
  | _, _, .makeBlockPtrDyn _ base _ _ _ _, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_base := opReads_congr Q base s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_base.1], by simp only [opReads, ih_base.2]⟩
  | _, _, .makeBlockPtrDynOffsets r bo ps bs strides offs, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      obtain ⟨hmb, hmoffs⟩ := hms
      have ih_bo := opReads_congr Q bo s₁ s₂ hag hmb
      have ih_offs : ∀ off ∈ offs, evalOp off s₁ = evalOp off s₂ ∧ opReads off s₂ = opReads off s₁ :=
        fun off hoff => opReads_congr Q off s₁ s₂ hag (fun c hc => hmoffs ⟨off, hoff, hc⟩)
      exact ⟨by simp only [evalOp, ih_bo.1, mapM_data_congr s₁ s₂ offs fun o h => (ih_offs o h).1],
        by simp only [opReads, ih_bo.2, listReads_congr offs fun o h => (ih_offs o h).2]⟩
  | _, _, .makeBlockPtrDynMetadata r bo ps bs strides offs, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      obtain ⟨hmb, hmstrides, hmoffs⟩ := hms
      have ih_bo := opReads_congr Q bo s₁ s₂ hag hmb
      have ih_strides : ∀ st ∈ strides, evalOp st s₁ = evalOp st s₂ ∧ opReads st s₂ = opReads st s₁ :=
        fun st hst => opReads_congr Q st s₁ s₂ hag (fun c hc => hmstrides ⟨st, hst, hc⟩)
      have ih_offs : ∀ off ∈ offs, evalOp off s₁ = evalOp off s₂ ∧ opReads off s₂ = opReads off s₁ :=
        fun off hoff => opReads_congr Q off s₁ s₂ hag (fun c hc => hmoffs ⟨off, hoff, hc⟩)
      exact ⟨by simp only [evalOp, ih_bo.1, mapM_data_congr s₁ s₂ strides fun o h => (ih_strides o h).1,
          mapM_data_congr s₁ s₂ offs fun o h => (ih_offs o h).1],
        by simp only [opReads, ih_bo.2, listReads_congr strides fun o h => (ih_strides o h).2,
          listReads_congr offs fun o h => (ih_offs o h).2]⟩
  | _, _, .advanceBlockPtr ptr _, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      have ih_ptr := opReads_congr Q ptr s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, hag.regs, hag.pids, hag.numPids, ih_ptr.1], by simp only [opReads, ih_ptr.2]⟩
  | _, _, .advanceBlockPtrDyn p ds, s₁, s₂, hag, hms => by
      simp only [opReads, Set.union_subset_iff] at hms
      obtain ⟨hmp, hmd⟩ := hms
      have ih_p := opReads_congr Q p s₁ s₂ hag hmp
      have ih_ds : ∀ d ∈ ds, evalOp d s₁ = evalOp d s₂ ∧ opReads d s₂ = opReads d s₁ :=
        fun d hd => opReads_congr Q d s₁ s₂ hag (fun c hc => hmd ⟨d, hd, hc⟩)
      exact ⟨by simp only [evalOp, ih_p.1, mapM_data_congr s₁ s₂ ds fun o h => (ih_ds o h).1],
        by simp only [opReads, ih_p.2, listReads_congr ds fun o h => (ih_ds o h).2]⟩
  | _, _, .load d mem mask padding, s₁, s₂, hag, hms => by
      refine ⟨?_, ?_⟩
      ·
        have hpv (dt : TileDType) (r : RegionName) (o : Nat) :
            s₁.paddingValue dt padding r o = s₂.paddingValue dt padding r o :=
          BlockState.paddingValue_congr s₁ s₂ dt padding r o hag.undef
        cases mem with
        | region r off =>
            cases mask with
            | none =>
                simp only [opReads, Set.union_subset_iff] at hms
                obtain ⟨hmsmem, -, haddr⟩ := hms
                simp only [accessCells] at haddr
                have IHoff := (opReads_congr Q off s₁ s₂ hag hmsmem).1
                cases hoffs : evalOp off s₂ with
                | none => simp [evalOp, IHoff, hoffs]
                | some offs =>
                    simp only [evalOp, IHoff, hoffs]
                    refine congrArg some (Tile.ext fun i => ?_)
                    simp only [reduceIte]
                    exact BlockState.readMemValue_congr d
                      (hag.mem (haddr ⟨offs, IHoff.trans hoffs, i, trivial, rfl⟩))
            | mask m =>
                simp only [opReads, Set.union_subset_iff] at hms
                obtain ⟨hmsmem, hmsmask, haddr⟩ := hms
                simp only [accessCells] at haddr
                have IHoff := (opReads_congr Q off s₁ s₂ hag hmsmem).1
                have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
                cases hoffs : evalOp off s₂ with
                | none => simp [evalOp, IHoff, hoffs]
                | some offs =>
                    cases hm : evalOp m s₂ with
                    | none => simp [evalOp, IHoff, hoffs, IHm, hm]
                    | some ms =>
                        simp only [evalOp, IHoff, hoffs, IHm, hm]
                        refine congrArg some (Tile.ext fun i => ?_)
                        simp only [reduceIte]
                        by_cases hact : ms.data i = true
                        · simp only [hact, if_true]
                          exact BlockState.readMemValue_congr d
                            (hag.mem (haddr ⟨offs, IHoff.trans hoffs, i, ⟨ms, IHm.trans hm, hact⟩, rfl⟩))
                        · simp only [Bool.not_eq_true] at hact
                          simp only [hact, Bool.false_eq_true, if_false]
                          cases d <;> simp [hag.undef]
            | maskOther m other =>
                simp only [opReads, Set.union_subset_iff] at hms
                obtain ⟨hmsmem, ⟨hmm, hmo⟩, haddr⟩ := hms
                simp only [accessCells] at haddr
                have IHoff := (opReads_congr Q off s₁ s₂ hag hmsmem).1
                have IHm := (opReads_congr Q m s₁ s₂ hag hmm).1
                have IHo := (opReads_congr Q other s₁ s₂ hag hmo).1
                cases hoffs : evalOp off s₂ with
                | none => simp [evalOp, IHoff, hoffs]
                | some offs =>
                    cases hm : evalOp m s₂ with
                    | none => simp [evalOp, IHoff, hoffs, IHm, hm]
                    | some ms =>
                        cases ho : evalOp other s₂ with
                        | none =>
                            simp [evalOp, IHoff, hoffs, IHm, hm, IHo, ho]
                        | some os =>
                            simp [evalOp, IHoff, hoffs, IHm, hm, IHo, ho]
                            funext i
                            by_cases hact : ms.data i = true
                            · simp only [hact, if_true]
                              exact BlockState.readMemValue_congr d
                                (hag.mem (haddr ⟨offs, IHoff.trans hoffs, i, ⟨ms, IHm.trans hm, hact⟩, rfl⟩))
                            · simp only [Bool.not_eq_true] at hact
                              simp only [hact, Bool.false_eq_true, if_false]
        | ptr p =>
            cases mask with
            | none =>
                simp only [opReads, Set.union_subset_iff] at hms
                obtain ⟨hmsmem, -, haddr⟩ := hms
                simp only [accessCells] at haddr
                have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
                cases hps : evalOp p s₂ with
                | none => simp [evalOp, IHp, hps]
                | some ps =>
                    simp only [evalOp, IHp, hps]
                    refine congrArg some (Tile.ext fun i => ?_)
                    simp only [reduceIte]
                    exact BlockState.readMemValue_congr d
                      (hag.mem (haddr ⟨ps, IHp.trans hps, i, trivial, rfl⟩))
            | mask m =>
                simp only [opReads, Set.union_subset_iff] at hms
                obtain ⟨hmsmem, hmsmask, haddr⟩ := hms
                simp only [accessCells] at haddr
                have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
                have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
                cases hps : evalOp p s₂ with
                | none => simp [evalOp, IHp, hps]
                | some ps =>
                    cases hm : evalOp m s₂ with
                    | none => simp [evalOp, IHp, hps, IHm, hm]
                    | some ms =>
                        simp only [evalOp, IHp, hps, IHm, hm]
                        refine congrArg some (Tile.ext fun i => ?_)
                        simp only [reduceIte]
                        by_cases hact : ms.data i = true
                        · simp only [hact, if_true]
                          exact BlockState.readMemValue_congr d
                            (hag.mem (haddr ⟨ps, IHp.trans hps, i, ⟨ms, IHm.trans hm, hact⟩, rfl⟩))
                        · simp only [Bool.not_eq_true] at hact
                          simp only [hact, Bool.false_eq_true, if_false]
                          cases d <;> simp [hag.undef]
            | maskOther m other =>
                simp only [opReads, Set.union_subset_iff] at hms
                obtain ⟨hmsmem, ⟨hmm, hmo⟩, haddr⟩ := hms
                simp only [accessCells] at haddr
                have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
                have IHm := (opReads_congr Q m s₁ s₂ hag hmm).1
                have IHo := (opReads_congr Q other s₁ s₂ hag hmo).1
                cases hps : evalOp p s₂ with
                | none => simp [evalOp, IHp, hps]
                | some ps =>
                    cases hm : evalOp m s₂ with
                    | none => simp [evalOp, IHp, hps, IHm, hm]
                    | some ms =>
                        cases ho : evalOp other s₂ with
                        | none =>
                            simp [evalOp, IHp, hps, IHm, hm, IHo, ho]
                        | some os =>
                            simp [evalOp, IHp, hps, IHm, hm, IHo, ho]
                            funext i
                            by_cases hact : ms.data i = true
                            · simp only [hact, if_true]
                              exact BlockState.readMemValue_congr d
                                (hag.mem (haddr ⟨ps, IHp.trans hps, i, ⟨ms, IHm.trans hm, hact⟩, rfl⟩))
                            · simp only [Bool.not_eq_true] at hact
                              simp only [hact, Bool.false_eq_true, if_false]
        | blockPtr p bc =>
            cases mask with
            | none =>
                simp only [opReads, Set.union_subset_iff] at hms
                obtain ⟨hmsmem, -, haddr⟩ := hms
                simp only [accessCells] at haddr
                have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
                cases hps : evalOp p s₂ with
                | none => simp [evalOp, hpv, IHp, hps]
                | some ps =>
                    simp only [evalOp, hpv, IHp, hps]
                    refine congrArg some (Tile.ext fun i => ?_)
                    by_cases hib : (ps.data i).inBounds
                        (TileShape.indexToList _ i) bc = true
                    · simp only [hib, if_true]
                      exact BlockState.readMemValue_congr d
                        (hag.mem (haddr ⟨ps, IHp.trans hps, i, trivial, hib, rfl⟩))
                    · simp only [Bool.not_eq_true] at hib
                      simp only [hib, Bool.false_eq_true, if_false]
            | mask m =>
                simp only [opReads, Set.union_subset_iff] at hms
                obtain ⟨hmsmem, hmsmask, haddr⟩ := hms
                simp only [accessCells] at haddr
                have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
                have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
                cases hps : evalOp p s₂ with
                | none => simp [evalOp, hpv, IHp, hps]
                | some ps =>
                    cases hm : evalOp m s₂ with
                    | none => simp [evalOp, hpv, IHp, hps, IHm, hm]
                    | some ms =>
                        simp only [evalOp, hpv, IHp, hps, IHm, hm]
                        refine congrArg some (Tile.ext fun i => ?_)
                        by_cases hact : ms.data i = true
                        · simp only [hact, if_true]
                          by_cases hib : (ps.data i).inBounds
                              (TileShape.indexToList _ i) bc = true
                          · simp only [hib, if_true]
                            exact BlockState.readMemValue_congr d
                              (hag.mem (haddr ⟨ps, IHp.trans hps, i, ⟨ms, IHm.trans hm, hact⟩, hib, rfl⟩))
                          · simp only [Bool.not_eq_true] at hib
                            simp only [hib, Bool.false_eq_true, if_false]
                        · simp only [Bool.not_eq_true] at hact
                          simp only [hact, Bool.false_eq_true, if_false]
                          cases d <;> simp [hag.undef]
            | maskOther m other =>
                simp only [opReads, Set.union_subset_iff] at hms
                obtain ⟨hmsmem, ⟨hmm, hmo⟩, haddr⟩ := hms
                simp only [accessCells] at haddr
                have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
                have IHm := (opReads_congr Q m s₁ s₂ hag hmm).1
                have IHo := (opReads_congr Q other s₁ s₂ hag hmo).1
                cases hps : evalOp p s₂ with
                | none => simp [evalOp, hpv, IHp, hps]
                | some ps =>
                    cases hm : evalOp m s₂ with
                    | none => simp [evalOp, hpv, IHp, hps, IHm, hm]
                    | some ms =>
                        cases ho : evalOp other s₂ with
                        | none =>
                            simp [evalOp, hpv, IHp, hps, IHm, hm, IHo, ho]
                        | some os =>
                            simp [evalOp, hpv, IHp, hps, IHm, hm, IHo, ho]
                            funext i
                            by_cases hact : ms.data i = true
                            · simp only [hact, if_true]
                              by_cases hib : (ps.data i).inBounds
                                  (TileShape.indexToList _ i) bc = true
                              · simp only [hib, if_true]
                                exact BlockState.readMemValue_congr d
                                  (hag.mem (haddr ⟨ps, IHp.trans hps, i, ⟨ms, IHm.trans hm, hact⟩, hib, rfl⟩))
                              · simp only [Bool.not_eq_true] at hib
                                simp only [hib, Bool.false_eq_true, if_false]
                            · simp only [Bool.not_eq_true] at hact
                              simp only [hact, Bool.false_eq_true, if_false]

      · cases mem with
        | region r off =>
            cases mask with
            | none =>
                simp only [opReads, Set.union_subset_iff] at hms
                have ih_off := opReads_congr Q off s₁ s₂ hag hms.1
                simp only [opReads, accessCells, MaskOpt.Active, ← ih_off.1, ih_off.2]
            | mask m =>
                simp only [opReads, Set.union_subset_iff] at hms
                have ih_off := opReads_congr Q off s₁ s₂ hag hms.1
                have ih_m := opReads_congr Q m s₁ s₂ hag hms.2.1
                simp only [opReads, accessCells, MaskOpt.Active, ← ih_off.1, ih_off.2, ← ih_m.1, ih_m.2]
            | maskOther m o =>
                simp only [opReads, Set.union_subset_iff] at hms
                have ih_off := opReads_congr Q off s₁ s₂ hag hms.1
                have ih_m := opReads_congr Q m s₁ s₂ hag hms.2.1.1
                have ih_o := opReads_congr Q o s₁ s₂ hag hms.2.1.2
                simp only [opReads, accessCells, MaskOpt.Active, ← ih_off.1, ih_off.2, ← ih_m.1, ih_m.2,
                  ih_o.2]
        | ptr p =>
            cases mask with
            | none =>
                simp only [opReads, Set.union_subset_iff] at hms
                have ih_p := opReads_congr Q p s₁ s₂ hag hms.1
                simp only [opReads, accessCells, MaskOpt.Active, ← ih_p.1, ih_p.2]
            | mask m =>
                simp only [opReads, Set.union_subset_iff] at hms
                have ih_p := opReads_congr Q p s₁ s₂ hag hms.1
                have ih_m := opReads_congr Q m s₁ s₂ hag hms.2.1
                simp only [opReads, accessCells, MaskOpt.Active, ← ih_p.1, ih_p.2, ← ih_m.1, ih_m.2]
            | maskOther m o =>
                simp only [opReads, Set.union_subset_iff] at hms
                have ih_p := opReads_congr Q p s₁ s₂ hag hms.1
                have ih_m := opReads_congr Q m s₁ s₂ hag hms.2.1.1
                have ih_o := opReads_congr Q o s₁ s₂ hag hms.2.1.2
                simp only [opReads, accessCells, MaskOpt.Active, ← ih_p.1, ih_p.2, ← ih_m.1, ih_m.2,
                  ih_o.2]
        | blockPtr p bc =>
            cases mask with
            | none =>
                simp only [opReads, Set.union_subset_iff] at hms
                have ih_p := opReads_congr Q p s₁ s₂ hag hms.1
                simp only [opReads, accessCells, MaskOpt.Active, ← ih_p.1, ih_p.2]
            | mask m =>
                simp only [opReads, Set.union_subset_iff] at hms
                have ih_p := opReads_congr Q p s₁ s₂ hag hms.1
                have ih_m := opReads_congr Q m s₁ s₂ hag hms.2.1
                simp only [opReads, accessCells, MaskOpt.Active, ← ih_p.1, ih_p.2, ← ih_m.1, ih_m.2]
            | maskOther m o =>
                simp only [opReads, Set.union_subset_iff] at hms
                have ih_p := opReads_congr Q p s₁ s₂ hag hms.1
                have ih_m := opReads_congr Q m s₁ s₂ hag hms.2.1.1
                have ih_o := opReads_congr Q o s₁ s₂ hag hms.2.1.2
                simp only [opReads, accessCells, MaskOpt.Active, ← ih_p.1, ih_p.2, ← ih_m.1, ih_m.2,
                  ih_o.2]

  | _, _, .natToReal a, s₁, s₂, hag, hms => by
      simp only [opReads] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, ih_a.1], by simp only [opReads, ih_a.2]⟩
  | _, _, .intToReal a, s₁, s₂, hag, hms => by
      simp only [opReads] at hms
      have ih_a := opReads_congr Q a s₁ s₂ hag hms
      exact ⟨by simp only [evalOp, ih_a.1], by simp only [opReads, ih_a.2]⟩

end VeriTile.Dist
