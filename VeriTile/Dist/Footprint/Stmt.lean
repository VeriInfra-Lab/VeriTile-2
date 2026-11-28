/-
VeriTile.Dist.Footprint.Stmt

The cells that upstream statements read and write, computed along their
execution from the state they start in (S3.3, #45). `stmtsFoot code s` is a
pair: the cells that `stepStmts code s` reads, and the cells it writes. It
follows the actual execution: the branch taken, the loop iterations run, and
the state each statement runs in. Only active lanes count, and a statement
that fails contributes nothing after it.

- A plain store writes its active lanes and reads nothing there.
- An `atomic_add` and an `atomicRMW` read and write their active lanes.
- Every operand of a statement contributes its `opReads`
  (`VeriTile/Dist/Footprint/Op.lean`).

`stmtsFoot_congr` is the soundness of these sets: two states that agree on
the read set and on every field that is not memory have the same read and
write sets; both runs fail or both succeed; the results agree on the read
and write sets and on every field that is not memory; and each run changes
no cell outside the write set.
-/
import VeriTile.Dist.Footprint.Op

namespace VeriTile.Dist

open VeriTile.Triton

/-- The cells a run reads and the cells it writes. -/
abbrev Foot := Set BlockCell × Set BlockCell

/-- Run `f`, then `g`. -/
def Foot.seq (f g : Foot) : Foot := (f.1 ∪ g.1, f.2 ∪ g.2)

@[simp] theorem Foot.seq_fst (f g : Foot) : (Foot.seq f g).1 = f.1 ∪ g.1 := rfl
@[simp] theorem Foot.seq_snd (f g : Foot) : (Foot.seq f g).2 = f.2 ∪ g.2 := rfl

/-- The cells that the address operand of a memory access reads. -/
def memReads {d : TileDType} {sh : TileShape} (mem : MemAccess d sh) (s : BlockState) :
    Set BlockCell :=
  match mem with
  | .region _ off => opReads off s
  | .ptr p => opReads p s
  | .blockPtr p _ => opReads p s

/-- The cells that the mask of a store or an atomic reads. Its `other`
operand is not evaluated. -/
def maskReads {d : TileDType} {sh : TileShape} (mask : MaskOpt d sh) (s : BlockState) :
    Set BlockCell :=
  match mask with
  | .none => ∅
  | .mask m => opReads m s
  | .maskOther m _ => opReads m s

/-- The cells that the optional replacement operand of an `atomicRMW` reads. -/
def extraReads {d : TileDType} {sh : TileShape} (extra : Option (Op d sh)) (s : BlockState) :
    Set BlockCell :=
  match extra with
  | none => ∅
  | some x => opReads x s

mutual

/-- The cells that `stepStmt st s` reads and writes. -/
noncomputable def stmtFoot : Stmt → BlockState → Foot
  | .assign _ _ _ e, s => (opReads e s, ∅)
  | .store _ _ mem val mask, s =>
      (memReads mem s ∪ (opReads val s ∪ maskReads mask s), accessCells mem s (mask.Active s))
  | .atomicAdd _ _ mem val mask, s =>
      (memReads mem s ∪ (opReads val s ∪ (maskReads mask s ∪ accessCells mem s (mask.Active s))),
        accessCells mem s (mask.Active s))
  | .atomicRMW _ _ _ mem input extra mask _, s =>
      (memReads mem s ∪ (opReads input s ∪ (extraReads extra s ∪
          (maskReads mask s ∪ accessCells mem s (mask.Active s)))),
        accessCells mem s (mask.Active s))
  | .forLoop idx n body, s => loopFoot idx 0 n body s
  | .forRange idx start stop step body, s => rangeFoot idx start stop step body s
  | .forRangeDyn idx start stop step body, s =>
      Foot.seq (opReads start s ∪ (opReads stop s ∪ opReads step s), ∅)
        (match evalOp start s, evalOp stop s, evalOp step s with
          | some a, some b, some c =>
              rangeFoot idx (a.data PUnit.unit) (b.data PUnit.unit) (c.data PUnit.unit) body s
          | _, _, _ => (∅, ∅))
  | .forRangeInt idx start stop step body, s =>
      Foot.seq (opReads start s ∪ (opReads stop s ∪ opReads step s), ∅)
        (match evalOp start s, evalOp stop s, evalOp step s with
          | some a, some b, some c =>
              rangeIntFoot idx (a.data PUnit.unit) (b.data PUnit.unit) (c.data PUnit.unit) body s
          | _, _, _ => (∅, ∅))
  | .ifThen c body, s =>
      Foot.seq (opReads c s, ∅)
        (match evalOp c s with
          | some vc => if vc.data PUnit.unit then stmtsFoot body s else (∅, ∅)
          | none => (∅, ∅))
  | .ifThenElse c tb eb, s =>
      Foot.seq (opReads c s, ∅)
        (match evalOp c s with
          | some vc => if vc.data PUnit.unit then stmtsFoot tb s else stmtsFoot eb s
          | none => (∅, ∅))
  termination_by st _ => (sizeOf st, 0)
  decreasing_by
    all_goals simp_wf
    all_goals (try omega)
    all_goals (have : 0 < sizeOf idx := by cases idx; simp)
    all_goals omega

/-- The cells that `stepStmts code s` reads and writes. -/
noncomputable def stmtsFoot : List Stmt → BlockState → Foot
  | [], _ => (∅, ∅)
  | st :: rest, s =>
      Foot.seq (stmtFoot st s)
        (match stepStmt st s with
          | some s' => stmtsFoot rest s'
          | none => (∅, ∅))
  termination_by l _ => (sizeOf l, 0)
  decreasing_by all_goals (simp_wf; omega)

/-- The cells that `stepForLoopAux idx start n body s` reads and writes. -/
noncomputable def loopFoot (idx : RegName) (start n : Nat) (body : List Stmt) (s : BlockState) : Foot :=
  if start < n then
    Foot.seq (stmtsFoot body (s.setReg idx .nat [] (Tile.scalar start)))
      (match stepStmts body (s.setReg idx .nat [] (Tile.scalar start)) with
        | some s' => loopFoot idx (start + 1) n body s'
        | none => (∅, ∅))
  else (∅, ∅)
  termination_by (sizeOf body + 1, n - start)
  decreasing_by all_goals omega

/-- The cells that `stepForRangeAux idx cur stop step body s` reads and writes. -/
noncomputable def rangeFoot (idx : RegName) (cur stop step : Nat) (body : List Stmt) (s : BlockState) :
    Foot :=
  if step = 0 then (∅, ∅)
  else if cur < stop then
    Foot.seq (stmtsFoot body (s.setReg idx .nat [] (Tile.scalar cur)))
      (match stepStmts body (s.setReg idx .nat [] (Tile.scalar cur)) with
        | some s' => rangeFoot idx (cur + step) stop step body s'
        | none => (∅, ∅))
  else (∅, ∅)
  termination_by (sizeOf body + 1, stop - cur)
  decreasing_by all_goals omega

/-- The cells that `stepForRangeIntAux idx cur stop step body s` reads and writes. -/
noncomputable def rangeIntFoot (idx : RegName) (cur stop : Int) (step : Nat) (body : List Stmt)
    (s : BlockState) : Foot :=
  if step = 0 then (∅, ∅)
  else if cur < stop then
    Foot.seq (stmtsFoot body (s.setReg idx .int [] (Tile.scalar cur)))
      (match stepStmts body (s.setReg idx .int [] (Tile.scalar cur)) with
        | some s' => rangeIntFoot idx (cur + step) stop step body s'
        | none => (∅, ∅))
  else (∅, ∅)
  termination_by (sizeOf body + 1, (stop - cur).toNat)
  decreasing_by all_goals omega

end

/-! ## The simulation relation -/

/-- Two runs from `s₁` and `s₂` reached `t₁` and `t₂`: the results agree on
`Q ∪ W` and on every field that is not memory, and each run left every cell
outside `W` as it was. -/
def SimRel (Q W : Set BlockCell) (s₁ s₂ t₁ t₂ : BlockState) : Prop :=
  BlockAgree (Q ∪ W) t₁ t₂ ∧ (∀ c ∉ W, t₁.mem c.1 c.2 = s₁.mem c.1 c.2) ∧
    (∀ c ∉ W, t₂.mem c.1 c.2 = s₂.mem c.1 c.2)

/-- Both runs fail, or both succeed with results related by `SimRel`. -/
abbrev StepSim (Q W : Set BlockCell) (s₁ s₂ : BlockState) :
    Option BlockState → Option BlockState → Prop :=
  OptionRel (SimRel Q W s₁ s₂)

theorem BlockAgree.mono {Q Q' : Set BlockCell} {s₁ s₂ : BlockState} (h : Q' ⊆ Q)
    (hag : BlockAgree Q s₁ s₂) : BlockAgree Q' s₁ s₂ :=
  ⟨fun _ _ hp => hag.mem (h hp), hag.regs, hag.pids, hag.undef, hag.numPids⟩

theorem SimRel.congrW {Q W W' : Set BlockCell} {s₁ s₂ t₁ t₂ : BlockState} (hW : W = W')
    (h : SimRel Q W' s₁ s₂ t₁ t₂) : SimRel Q W s₁ s₂ t₁ t₂ := hW ▸ h

theorem StepSim.congrW {Q W W' : Set BlockCell} {s₁ s₂ : BlockState}
    {o₁ o₂ : Option BlockState} (hW : W = W') (h : StepSim Q W' s₁ s₂ o₁ o₂) :
    StepSim Q W s₁ s₂ o₁ o₂ := hW ▸ h

/-- A run that changes no memory. -/
theorem SimRel.of_mem {Q : Set BlockCell} {s₁ s₂ t₁ t₂ : BlockState}
    (hag : BlockAgree Q t₁ t₂) (h₁ : t₁.mem = s₁.mem) (h₂ : t₂.mem = s₂.mem) :
    SimRel Q ∅ s₁ s₂ t₁ t₂ :=
  ⟨hag.mono (by simp), fun c _ => by rw [h₁], fun c _ => by rw [h₂]⟩

theorem SimRel.refl {Q : Set BlockCell} {s₁ s₂ : BlockState} (hag : BlockAgree Q s₁ s₂) :
    SimRel Q ∅ s₁ s₂ s₁ s₂ := SimRel.of_mem hag rfl rfl

/-- Two runs one after the other. -/
theorem SimRel.trans {Q W₁ W₂ : Set BlockCell} {s₁ s₂ t₁ t₂ u₁ u₂ : BlockState}
    (h₁ : SimRel Q W₁ s₁ s₂ t₁ t₂) (h₂ : SimRel (Q ∪ W₁) W₂ t₁ t₂ u₁ u₂) :
    SimRel Q (W₁ ∪ W₂) s₁ s₂ u₁ u₂ := by
  refine ⟨h₂.1.mono (by intro c hc; simp only [Set.mem_union] at hc ⊢; tauto), ?_, ?_⟩
  · intro c hc
    simp only [Set.mem_union, not_or] at hc
    rw [h₂.2.1 c hc.2, h₁.2.1 c hc.1]
  · intro c hc
    simp only [Set.mem_union, not_or] at hc
    rw [h₂.2.2 c hc.2, h₁.2.2 c hc.1]

/-- A run started after a register write is related to the states before it. -/
theorem SimRel.setReg_base {Q W : Set BlockCell} {s₁ s₂ t₁ t₂ : BlockState} {n : RegName}
    {d : TileDType} {sh : TileShape} {v : Tile d sh}
    (h : SimRel Q W (s₁.setReg n d sh v) (s₂.setReg n d sh v) t₁ t₂) :
    SimRel Q W s₁ s₂ t₁ t₂ :=
  ⟨h.1, fun c hc => by rw [h.2.1 c hc]; rfl, fun c hc => by rw [h.2.2 c hc]; rfl⟩

/-- A register write preserves agreement on any set. -/
theorem BlockAgree.setReg {Q : Set BlockCell} {s₁ s₂ : BlockState} (hag : BlockAgree Q s₁ s₂)
    (n : RegName) (d : TileDType) (sh : TileShape) (v : Tile d sh) :
    BlockAgree Q (s₁.setReg n d sh v) (s₂.setReg n d sh v) :=
  BlockState.AgreeOn.setReg hag n d sh v

/-! ## Memory folds -/

theorem writeMemTyped_mem_ne (s : BlockState) (d : TileDType) (r : RegionName) (o : Nat)
    (v : TileCarrier d) {r' : RegionName} {o' : Nat} (h : ¬ (r' = r ∧ o' = o)) :
    (s.writeMemTyped d r o v).mem r' o' = s.mem r' o' := by
  cases d <;> simp only [BlockState.writeMemTyped, BlockState.writeMemAs, if_neg h]

theorem writeMemTyped_mem_same (s₁ s₂ : BlockState) (d : TileDType) (r : RegionName) (o : Nat)
    (v : TileCarrier d) :
    (s₁.writeMemTyped d r o v).mem r o = (s₂.writeMemTyped d r o v).mem r o := by
  cases d <;> simp only [BlockState.writeMemTyped, BlockState.writeMemAs, and_self, if_true]

/-- A masked scatter whose written value depends on the state it writes to
changes only its active cells. -/
theorem foldWrite_frame {α : Type} (d : TileDType) (rf : α → RegionName) (of : α → Nat)
    (vf : BlockState → α → TileCarrier d) (active : α → Bool) :
    ∀ (l : List α) (s : BlockState) (c : BlockCell),
      c ∉ {c | ∃ i ∈ l, active i = true ∧ c = (rf i, of i)} →
      (l.foldl (fun acc i => if active i then acc.writeMemTyped d (rf i) (of i) (vf acc i)
        else acc) s).mem c.1 c.2 = s.mem c.1 c.2
  | [], _, _, _ => rfl
  | i :: rest, s, c, hc => by
      rw [List.foldl_cons]
      have hrest : c ∉ {c | ∃ i ∈ rest, active i = true ∧ c = (rf i, of i)} :=
        fun ⟨j, hj, ha, he⟩ => hc ⟨j, List.mem_cons_of_mem _ hj, ha, he⟩
      rw [foldWrite_frame d rf of vf active rest _ c hrest]
      by_cases ha : active i = true
      · rw [if_pos ha]
        apply writeMemTyped_mem_ne
        rintro ⟨h1, h2⟩
        exact hc ⟨i, List.mem_cons_self, ha, Prod.ext h1 h2⟩
      · rw [if_neg ha]

/-- A masked scatter of the same values on both sides makes the results agree
on the written cells, and leaves agreement elsewhere as it was. -/
theorem foldWrite_agree {α : Type} (d : TileDType) (rf : α → RegionName) (of : α → Nat)
    (vf : α → TileCarrier d) (active : α → Bool) :
    ∀ (l : List α) (Q : Set BlockCell) (s₁ s₂ : BlockState), BlockAgree Q s₁ s₂ →
      BlockAgree (Q ∪ {c | ∃ i ∈ l, active i = true ∧ c = (rf i, of i)})
        (l.foldl (fun acc i => if active i then acc.writeMemTyped d (rf i) (of i) (vf i)
          else acc) s₁)
        (l.foldl (fun acc i => if active i then acc.writeMemTyped d (rf i) (of i) (vf i)
          else acc) s₂)
  | [], Q, s₁, s₂, hag => hag.mono (by intro c hc; simpa using hc)
  | i :: rest, Q, s₁, s₂, hag => by
      rw [List.foldl_cons, List.foldl_cons]
      by_cases ha : active i = true
      · rw [if_pos ha, if_pos ha]
        have h1 : BlockAgree (Q ∪ {(rf i, of i)}) (s₁.writeMemTyped d (rf i) (of i) (vf i))
            (s₂.writeMemTyped d (rf i) (of i) (vf i)) := by
          refine ⟨fun r o hp => ?_, ?_⟩
          · by_cases he : r = rf i ∧ o = of i
            · obtain ⟨rfl, rfl⟩ := he
              exact writeMemTyped_mem_same _ _ _ _ _ _
            · rw [writeMemTyped_mem_ne _ _ _ _ _ he, writeMemTyped_mem_ne _ _ _ _ _ he]
              rcases hp with hp | hp
              · exact hag.mem hp
              · exact absurd (Prod.ext_iff.mp hp) he
          · exact ((BlockState.AgreeOn.writeMemTyped hag d (rf i) (of i) (vf i))).2
        refine (foldWrite_agree d rf of vf active rest _ _ _ h1).mono ?_
        rintro c (hc | ⟨j, hj, hja, rfl⟩)
        · exact Or.inl (Or.inl hc)
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr ⟨j, hj, hja, rfl⟩
      · rw [if_neg ha, if_neg ha]
        refine (foldWrite_agree d rf of vf active rest _ _ _ hag).mono ?_
        rintro c (hc | ⟨j, hj, hja, rfl⟩)
        · exact Or.inl hc
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact absurd hja ha
          · exact Or.inr ⟨j, hj, hja, rfl⟩

/-- The set of cells written by a masked scatter over all lanes. -/
theorem scatterCells_allIndices {sh : TileShape} (rf : TileIndex sh → RegionName)
    (of : TileIndex sh → Nat) (active : TileIndex sh → Bool) :
    {c | ∃ i ∈ TileShape.allIndices sh, active i = true ∧ c = (rf i, of i)} =
      {c | ∃ i, active i = true ∧ c = (rf i, of i)} := by
  ext c; simp [TileShape.mem_allIndices]

/-- A plain masked store over all lanes. -/
theorem writeFold_sim (Q : Set BlockCell) {sh : TileShape} (d : TileDType)
    (rf : TileIndex sh → RegionName) (of : TileIndex sh → Nat) (vf : TileIndex sh → TileCarrier d)
    (active : TileIndex sh → Bool) (s₁ s₂ : BlockState) (hag : BlockAgree Q s₁ s₂)
    (W : Set BlockCell) (hW : ∀ c, c ∈ W ↔ ∃ i, active i = true ∧ c = (rf i, of i)) :
    SimRel Q W s₁ s₂
      ((TileShape.allIndices sh).foldl (fun acc i => if active i then
        acc.writeMemTyped d (rf i) (of i) (vf i) else acc) s₁)
      ((TileShape.allIndices sh).foldl (fun acc i => if active i then
        acc.writeMemTyped d (rf i) (of i) (vf i) else acc) s₂) := by
  have hW' : W = {c | ∃ i ∈ TileShape.allIndices sh, active i = true ∧ c = (rf i, of i)} := by
    rw [scatterCells_allIndices]; ext c; exact hW c
  subst hW'
  exact ⟨foldWrite_agree d rf of vf active _ Q s₁ s₂ hag,
    fun c hc => foldWrite_frame d rf of (fun _ i => vf i) active _ s₁ c hc,
    fun c hc => foldWrite_frame d rf of (fun _ i => vf i) active _ s₂ c hc⟩

/-- An `atomic_add` over all lanes: its cells are read, so they lie in `Q`. -/
theorem atomicFold_sim (Q : Set BlockCell) {sh : TileShape} {d : TileDType}
    (hnum : NumericDType d) (rf : TileIndex sh → RegionName) (of : TileIndex sh → Nat)
    (inf : TileIndex sh → TileCarrier d) (active : TileIndex sh → Bool) (s₁ s₂ : BlockState)
    (hag : BlockAgree Q s₁ s₂) (W : Set BlockCell) (hWQ : W ⊆ Q)
    (hW : ∀ c, c ∈ W ↔ ∃ i, active i = true ∧ c = (rf i, of i)) :
    SimRel Q W s₁ s₂
      ((TileShape.allIndices sh).foldl (fun acc i => if active i then
        acc.writeMemTyped d (rf i) (of i)
          (hnum.add (acc.readMemValue d (rf i) (of i)) (inf i)) else acc) s₁)
      ((TileShape.allIndices sh).foldl (fun acc i => if active i then
        acc.writeMemTyped d (rf i) (of i)
          (hnum.add (acc.readMemValue d (rf i) (of i)) (inf i)) else acc) s₂) := by
  have hW' : W = {c | ∃ i ∈ TileShape.allIndices sh, active i = true ∧ c = (rf i, of i)} := by
    rw [scatterCells_allIndices]; ext c; exact hW c
  have hag' := foldl_atomicAdd_agreeOn hnum rf of inf active (fun r o => (r, o) ∈ Q)
    (TileShape.allIndices sh) s₁ s₂ hag
    (fun i _ ha => hWQ ((hW _).mpr ⟨i, ha, rfl⟩))
  subst hW'
  exact ⟨BlockAgree.mono (Set.union_subset le_rfl hWQ) hag',
    fun c hc => foldWrite_frame d rf of
      (fun acc i => hnum.add (acc.readMemValue d (rf i) (of i)) (inf i)) active _ s₁ c hc,
    fun c hc => foldWrite_frame d rf of
      (fun acc i => hnum.add (acc.readMemValue d (rf i) (of i)) (inf i)) active _ s₂ c hc⟩

/-! ## Operands of a statement -/

theorem memReads_congr (Q : Set BlockCell) {d : TileDType} {sh : TileShape}
    (mem : MemAccess d sh) (s₁ s₂ : BlockState) (hag : BlockAgree Q s₁ s₂)
    (h : memReads mem s₁ ⊆ Q) :
    memReads mem s₂ = memReads mem s₁ ∧ ∀ act, accessCells mem s₂ act = accessCells mem s₁ act := by
  cases mem with
  | region r off =>
      have ih := opReads_congr Q off s₁ s₂ hag h
      exact ⟨by simp only [memReads, ih.2], fun act => by simp only [accessCells, ← ih.1]⟩
  | ptr p =>
      have ih := opReads_congr Q p s₁ s₂ hag h
      exact ⟨by simp only [memReads, ih.2], fun act => by simp only [accessCells, ← ih.1]⟩
  | blockPtr p bc =>
      have ih := opReads_congr Q p s₁ s₂ hag h
      exact ⟨by simp only [memReads, ih.2], fun act => by simp only [accessCells, ← ih.1]⟩

theorem maskReads_congr (Q : Set BlockCell) {d : TileDType} {sh : TileShape}
    (mask : MaskOpt d sh) (s₁ s₂ : BlockState) (hag : BlockAgree Q s₁ s₂)
    (h : maskReads mask s₁ ⊆ Q) :
    maskReads mask s₂ = maskReads mask s₁ ∧ mask.Active s₂ = mask.Active s₁ := by
  cases mask with
  | none => exact ⟨rfl, rfl⟩
  | mask m =>
      have ih := opReads_congr Q m s₁ s₂ hag h
      exact ⟨by simp only [maskReads, ih.2], by simp only [MaskOpt.Active, ← ih.1]⟩
  | maskOther m o =>
      have ih := opReads_congr Q m s₁ s₂ hag h
      exact ⟨by simp only [maskReads, ih.2], by simp only [MaskOpt.Active, ← ih.1]⟩

theorem extraReads_congr (Q : Set BlockCell) {d : TileDType} {sh : TileShape}
    (extra : Option (Op d sh)) (s₁ s₂ : BlockState) (hag : BlockAgree Q s₁ s₂)
    (h : extraReads extra s₁ ⊆ Q) :
    extraReads extra s₂ = extraReads extra s₁ ∧ rmwExtras extra s₁ = rmwExtras extra s₂ := by
  cases extra with
  | none => exact ⟨rfl, rfl⟩
  | some x =>
      have ih := opReads_congr Q x s₁ s₂ hag h
      exact ⟨by simp only [extraReads, ih.2], by simp only [rmwExtras, ih.1]⟩

/-! ## Optional results -/

theorem optionRel_mono {α β : Type} {R S : α → β → Prop} {o₁ : Option α} {o₂ : Option β}
    (h : OptionRel R o₁ o₂) (f : ∀ a b, R a b → S a b) : OptionRel S o₁ o₂ := by
  cases h with
  | none => exact .none
  | some hab => exact .some (f _ _ hab)

theorem optionRel_strengthen {α β : Type} {R S : α → β → Prop} {o₁ : Option α}
    {o₂ : Option β} (h : OptionRel R o₁ o₂)
    (f : ∀ a b, o₁ = some a → o₂ = some b → R a b → S a b) : OptionRel S o₁ o₂ := by
  cases h with
  | none => exact .none
  | some hab => exact .some (f _ _ rfl rfl hab)

theorem optionRel_bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {o₁ : Option α} {o₂ : Option β} {f₁ : α → Option γ} {f₂ : β → Option δ}
    (h : OptionRel R o₁ o₂) (hf : ∀ a b, R a b → OptionRel S (f₁ a) (f₂ b)) :
    OptionRel S (o₁.bind f₁) (o₂.bind f₂) := by
  cases h with
  | none => exact .none
  | some hab => exact hf _ _ hab

theorem optionRel_map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {o₁ : Option α} {o₂ : Option β} {f₁ : α → γ} {f₂ : β → δ}
    (h : OptionRel R o₁ o₂) (hf : ∀ a b, R a b → S (f₁ a) (f₂ b)) :
    OptionRel S (o₁.map f₁) (o₂.map f₂) := by
  cases h with
  | none => exact .none
  | some hab => exact .some (hf _ _ hab)

theorem SimRel.setReg {Q W : Set BlockCell} {s₁ s₂ t₁ t₂ : BlockState}
    (h : SimRel Q W s₁ s₂ t₁ t₂) (n : RegName) (d : TileDType) (sh : TileShape) (v : Tile d sh) :
    SimRel Q W s₁ s₂ (t₁.setReg n d sh v) (t₂.setReg n d sh v) :=
  ⟨h.1.setReg n d sh v, h.2.1, h.2.2⟩

theorem SimRel.withPids {Q W : Set BlockCell} {s₁ s₂ t₁ t₂ : BlockState}
    (h : SimRel Q W s₁ s₂ t₁ t₂) {p₁ p₂ : Nat → Nat} (hp : p₁ = p₂) :
    SimRel Q W s₁ s₂ { t₁ with pids := p₁ } { t₂ with pids := p₂ } :=
  ⟨BlockState.AgreeOn.withPids h.1 hp, h.2.1, h.2.2⟩

/-! ## The `atomicRMW` statement -/

theorem atomicRMWAt_mem_ne {s s' : BlockState} {op : RMWOp} {dtype : TileDType}
    {region : RegionName} {offset : Nat} {input : TileCarrier dtype}
    {extraInput : Option (TileCarrier dtype)} {ret : TileCarrier dtype} {event : RMWEvent}
    (h : s.atomicRMWAt op dtype region offset input extraInput = some (s', ret, event))
    {r : RegionName} {o : Nat} (hne : ¬ (r = region ∧ o = offset)) : s'.mem r o = s.mem r o := by
  unfold BlockState.atomicRMWAt at h
  cases hApply : RMWOp.apply op (s.mem region offset)
      { cell := (region, offset), op := op, input := MemCell.of dtype input,
        extraInput := extraInput.map (MemCell.of dtype) } with
  | none => simp [hApply] at h
  | some out =>
      rcases out with ⟨nextCell, event'⟩
      simp [hApply] at h
      rcases h with ⟨rfl, _, _⟩
      simp only [BlockState.writeCell, if_neg hne]

/-- An RMW fold changes only its active cells. -/
theorem rmwFold_frame {dtype : TileDType} {shape : TileShape} (op : RMWOp)
    (rf : TileIndex shape → RegionName) (of : TileIndex shape → Nat)
    (inf : TileIndex shape → TileCarrier dtype)
    (ext : Option (TileIndex shape → TileCarrier dtype)) (active : TileIndex shape → Bool) :
    ∀ (l : List (TileIndex shape)) (s : BlockState) (retFn : TileIndex shape → TileCarrier dtype)
      (p : BlockState × Tile dtype shape),
      foldAtomicRMWIndices op rf of inf ext active l s retFn = some p →
      ∀ c ∉ {c | ∃ i ∈ l, active i = true ∧ c = (rf i, of i)}, p.1.mem c.1 c.2 = s.mem c.1 c.2
  | [], s, retFn, p, h, c, _ => by
      simp only [foldAtomicRMWIndices, Option.some.injEq] at h
      rw [← h]
  | i :: rest, s, retFn, p, h, c, hc => by
      have hrest : c ∉ {c | ∃ i ∈ rest, active i = true ∧ c = (rf i, of i)} :=
        fun ⟨j, hj, ha, he⟩ => hc ⟨j, List.mem_cons_of_mem _ hj, ha, he⟩
      simp only [foldAtomicRMWIndices] at h
      by_cases ha : active i = true
      · rw [if_pos ha] at h
        cases hat : s.atomicRMWAt op dtype (rf i) (of i) (inf i) (ext.map fun f => f i) with
        | none => rw [hat] at h; cases h
        | some q =>
            obtain ⟨s₁, r₁, e₁⟩ := q
            rw [hat] at h
            rw [rmwFold_frame op rf of inf ext active rest _ _ p h c hrest]
            exact atomicRMWAt_mem_ne hat fun ⟨h1, h2⟩ => hc ⟨i, List.mem_cons_self, ha, Prod.ext h1 h2⟩
      · rw [if_neg ha] at h
        exact rmwFold_frame op rf of inf ext active rest _ _ p h c hrest

/-- An RMW fold over all lanes, from agreeing states. -/
theorem rmwFold_sim (Q : Set BlockCell) {dtype : TileDType} {shape : TileShape} (op : RMWOp)
    (rf : TileIndex shape → RegionName) (of : TileIndex shape → Nat)
    (inf : TileIndex shape → TileCarrier dtype)
    (ext : Option (TileIndex shape → TileCarrier dtype)) (active : TileIndex shape → Bool)
    (retFn : TileIndex shape → TileCarrier dtype) (s₁ s₂ : BlockState)
    (hag : BlockAgree Q s₁ s₂) (W : Set BlockCell) (hWQ : W ⊆ Q)
    (hW : ∀ c, c ∈ W ↔ ∃ i, active i = true ∧ c = (rf i, of i)) :
    OptionRel (fun p₁ p₂ : BlockState × Tile dtype shape => SimRel Q W s₁ s₂ p₁.1 p₂.1 ∧ p₁.2 = p₂.2)
      (foldAtomicRMWIndices op rf of inf ext active (TileShape.allIndices shape) s₁ retFn)
      (foldAtomicRMWIndices op rf of inf ext active (TileShape.allIndices shape) s₂ retFn) := by
  have hW' : W = {c | ∃ i ∈ TileShape.allIndices shape, active i = true ∧ c = (rf i, of i)} := by
    rw [scatterCells_allIndices]; ext c; exact hW c
  refine optionRel_strengthen (foldAtomicRMWIndices_agreeOn op rf of inf ext active
    (fun r o => (r, o) ∈ Q) (TileShape.allIndices shape) s₁ s₂ retFn hag
    (fun i _ ha => hWQ ((hW _).mpr ⟨i, ha, rfl⟩))) fun p₁ p₂ h₁ h₂ hr => ?_
  refine ⟨⟨BlockAgree.mono (Set.union_subset le_rfl hWQ) hr.1, fun c hc => ?_, fun c hc => ?_⟩, hr.2⟩
  · exact rmwFold_frame op rf of inf ext active _ s₁ retFn p₁ h₁ c (hW' ▸ hc)
  · exact rmwFold_frame op rf of inf ext active _ s₂ retFn p₂ h₂ c (hW' ▸ hc)

theorem rmwDispatch_sim (Q : Set BlockCell) (op : RMWOp) {dtype : TileDType}
    {shape : TileShape} (mem : MemAccess dtype shape) (inputs : Tile dtype shape)
    (extraFn : Option (TileIndex shape → TileCarrier dtype))
    (active : TileIndex shape → Bool) (s₁ s₂ : BlockState) (hag : BlockAgree Q s₁ s₂)
    (hmem : memReads mem s₁ ⊆ Q) (hWQ : accessCells mem s₁ (fun i => active i = true) ⊆ Q) :
    OptionRel (fun p₁ p₂ : BlockState × Tile dtype shape =>
        SimRel Q (accessCells mem s₁ (fun i => active i = true)) s₁ s₂ p₁.1 p₂.1 ∧ p₁.2 = p₂.2)
      (rmwDispatch op mem inputs extraFn active s₁)
      (rmwDispatch op mem inputs extraFn active s₂) := by
  cases mem with
  | region r off =>
      simp only [memReads] at hmem
      have IHoff := (opReads_congr Q off s₁ s₂ hag hmem).1
      simp only [rmwDispatch, IHoff]
      cases hoffs : evalOp off s₂ with
      | none => exact .none
      | some offs =>
          exact rmwFold_sim Q op _ _ _ _ _ _ s₁ s₂ hag _ hWQ
            (by intro c; simp [accessCells, IHoff.trans hoffs])
  | ptr p =>
      simp only [memReads] at hmem
      have IHp := (opReads_congr Q p s₁ s₂ hag hmem).1
      simp only [rmwDispatch, IHp]
      cases hps : evalOp p s₂ with
      | none => exact .none
      | some ps =>
          exact rmwFold_sim Q op _ _ _ _ _ _ s₁ s₂ hag _ hWQ
            (by intro c; simp [accessCells, IHp.trans hps])
  | blockPtr p bc =>
      simp only [memReads] at hmem
      have IHp := (opReads_congr Q p s₁ s₂ hag hmem).1
      simp only [rmwDispatch, IHp]
      cases hps : evalOp p s₂ with
      | none => exact .none
      | some ps =>
          exact rmwFold_sim Q op _ _ _ _ _ _ s₁ s₂ hag _ hWQ
            (by intro c; simp [accessCells, IHp.trans hps, and_assoc])

theorem rmwActive_congr (Q : Set BlockCell) {dtype : TileDType} {shape : TileShape}
    (mask : MaskOpt dtype shape) (s₁ s₂ : BlockState) (hag : BlockAgree Q s₁ s₂)
    (h : maskReads mask s₁ ⊆ Q) : rmwActive mask s₁ = rmwActive mask s₂ := by
  cases mask with
  | none => rfl
  | mask m => simp only [rmwActive, (opReads_congr Q m s₁ s₂ hag h).1]
  | maskOther m o => simp only [rmwActive, (opReads_congr Q m s₁ s₂ hag h).1]

theorem rmwActive_eq_active {dtype : TileDType} {shape : TileShape} {mask : MaskOpt dtype shape}
    {s : BlockState} {act : TileIndex shape → Bool} (h : rmwActive mask s = some act) :
    (fun i => act i = true) = mask.Active s := by
  funext i
  apply propext
  constructor
  · exact rmwActive_active h
  · intro hi
    cases mask with
    | none =>
        simp only [rmwActive, Option.some.injEq] at h
        rw [← h]
    | mask m =>
        obtain ⟨ms, hm, hmi⟩ := hi
        simp only [rmwActive, hm, Option.map_some, Option.some.injEq] at h
        rw [← h]; exact hmi
    | maskOther m o =>
        obtain ⟨ms, hm, hmi⟩ := hi
        simp only [rmwActive, hm, Option.map_some, Option.some.injEq] at h
        rw [← h]; exact hmi

theorem stepAtomicRMW_sim (Q : Set BlockCell) (op : RMWOp) {dtype : TileDType}
    {shape : TileShape} (mem : MemAccess dtype shape) (input : Op dtype shape)
    (extra : Option (Op dtype shape)) (mask : MaskOpt dtype shape) (dest : Option RegName)
    (s₁ s₂ : BlockState) (hag : BlockAgree Q s₁ s₂) (hmem : memReads mem s₁ ⊆ Q)
    (hin : opReads input s₁ ⊆ Q) (hex : extraReads extra s₁ ⊆ Q)
    (hmask : maskReads mask s₁ ⊆ Q) (hWQ : accessCells mem s₁ (mask.Active s₁) ⊆ Q) :
    StepSim Q (accessCells mem s₁ (mask.Active s₁)) s₁ s₂
      (stepAtomicRMW op dtype shape mem input extra mask dest s₁)
      (stepAtomicRMW op dtype shape mem input extra mask dest s₂) := by
  have IHin := (opReads_congr Q input s₁ s₂ hag hin).1
  have hex' := (extraReads_congr Q extra s₁ s₂ hag hex).2
  have hac := rmwActive_congr Q mask s₁ s₂ hag hmask
  unfold stepAtomicRMW stepAtomicRMWRaw
  simp only [IHin, hex', hac]
  cases hinv : evalOp input s₂ with
  | none => exact .none
  | some inputs =>
      cases hexv : rmwExtras extra s₂ with
      | none => exact .none
      | some extraFn =>
          cases hacv : rmwActive mask s₂ with
          | none => exact .none
          | some active =>
              have hAct := rmwActive_eq_active (hac.trans hacv)
              have hdisp := rmwDispatch_sim Q op mem inputs extraFn active s₁ s₂ hag hmem
                (hAct ▸ hWQ)
              rw [hAct] at hdisp
              show OptionRel _
                (((rmwDispatch op mem inputs extraFn active s₁).bind
                  fun p => rmwCommit dest p.1 p.2).map fun s' => { s' with pids := s₁.pids })
                (((rmwDispatch op mem inputs extraFn active s₂).bind
                  fun p => rmwCommit dest p.1 p.2).map fun s' => { s' with pids := s₂.pids })
              refine optionRel_map (optionRel_bind hdisp fun p₁ p₂ hp => ?_)
                fun t₁ t₂ ht => SimRel.withPids ht hag.pids
              obtain ⟨hs, hr⟩ := hp
              rw [← hr]
              cases dest with
              | none => exact .some hs
              | some name => exact .some (hs.setReg name dtype shape p₁.2)

/-! ## Loop equations -/

theorem loopFoot_lt {idx : RegName} {start n : Nat} {body : List Stmt} {s : BlockState}
    (h : start < n) : loopFoot idx start n body s =
      Foot.seq (stmtsFoot body (s.setReg idx .nat [] (Tile.scalar start)))
        (match stepStmts body (s.setReg idx .nat [] (Tile.scalar start)) with
          | some s' => loopFoot idx (start + 1) n body s'
          | none => (∅, ∅)) := by
  rw [loopFoot, if_pos h]

theorem loopFoot_ge {idx : RegName} {start n : Nat} {body : List Stmt} {s : BlockState}
    (h : ¬ start < n) : loopFoot idx start n body s = (∅, ∅) := by
  rw [loopFoot, if_neg h]

theorem rangeFoot_zero {idx : RegName} {cur stop : Nat} {body : List Stmt} {s : BlockState} :
    rangeFoot idx cur stop 0 body s = (∅, ∅) := by
  rw [rangeFoot, if_pos rfl]

theorem rangeFoot_lt {idx : RegName} {cur stop step : Nat} {body : List Stmt} {s : BlockState}
    (hz : step ≠ 0) (h : cur < stop) : rangeFoot idx cur stop step body s =
      Foot.seq (stmtsFoot body (s.setReg idx .nat [] (Tile.scalar cur)))
        (match stepStmts body (s.setReg idx .nat [] (Tile.scalar cur)) with
          | some s' => rangeFoot idx (cur + step) stop step body s'
          | none => (∅, ∅)) := by
  rw [rangeFoot, if_neg hz, if_pos h]

theorem rangeFoot_ge {idx : RegName} {cur stop step : Nat} {body : List Stmt} {s : BlockState}
    (hz : step ≠ 0) (h : ¬ cur < stop) : rangeFoot idx cur stop step body s = (∅, ∅) := by
  rw [rangeFoot, if_neg hz, if_neg h]

theorem rangeIntFoot_zero {idx : RegName} {cur stop : Int} {body : List Stmt} {s : BlockState} :
    rangeIntFoot idx cur stop 0 body s = (∅, ∅) := by
  rw [rangeIntFoot, if_pos rfl]

theorem rangeIntFoot_lt {idx : RegName} {cur stop : Int} {step : Nat} {body : List Stmt}
    {s : BlockState} (hz : step ≠ 0) (h : cur < stop) : rangeIntFoot idx cur stop step body s =
      Foot.seq (stmtsFoot body (s.setReg idx .int [] (Tile.scalar cur)))
        (match stepStmts body (s.setReg idx .int [] (Tile.scalar cur)) with
          | some s' => rangeIntFoot idx (cur + step) stop step body s'
          | none => (∅, ∅)) := by
  rw [rangeIntFoot, if_neg hz, if_pos h]

theorem rangeIntFoot_ge {idx : RegName} {cur stop : Int} {step : Nat} {body : List Stmt}
    {s : BlockState} (hz : step ≠ 0) (h : ¬ cur < stop) :
    rangeIntFoot idx cur stop step body s = (∅, ∅) := by
  rw [rangeIntFoot, if_neg hz, if_neg h]

/-! ## Soundness of the statement footprints -/

set_option maxHeartbeats 3200000 in
mutual

/-- One statement reads only its read set: from states that agree on a set `Q`
containing it, the footprints are the same, and the runs are related by
`StepSim`. -/
theorem stmtFoot_congr :
    ∀ (st : Stmt) (Q : Set BlockCell) (s₁ s₂ : BlockState), BlockAgree Q s₁ s₂ →
      (stmtFoot st s₁).1 ⊆ Q →
      stmtFoot st s₂ = stmtFoot st s₁ ∧
        StepSim Q (stmtFoot st s₁).2 s₁ s₂ (stepStmt st s₁) (stepStmt st s₂)
  | .assign d sh n e, Q, s₁, s₂, hag, hms => by
      simp only [stmtFoot] at hms
      have ih := opReads_congr Q e s₁ s₂ hag hms
      refine ⟨by simp only [stmtFoot, ih.2], ?_⟩
      rw [show (stmtFoot (.assign d sh n e) s₁).2 = ∅ by simp only [stmtFoot]]
      simp only [stepStmt, ih.1]
      cases hv : evalOp e s₂ with
      | none => exact .none
      | some v => exact .some (SimRel.of_mem (hag.setReg n d sh v) rfl rfl)
  | .store d sh mem val mask, Q, s₁, s₂, hag, hms => by
      simp only [stmtFoot, Set.union_subset_iff] at hms
      obtain ⟨hmsmem, hmsval, hmsmask⟩ := hms
      have hmemc := memReads_congr Q mem s₁ s₂ hag hmsmem
      have hmaskc := maskReads_congr Q mask s₁ s₂ hag hmsmask
      have ihval := opReads_congr Q val s₁ s₂ hag hmsval
      refine ⟨by simp only [stmtFoot, hmemc.1, hmemc.2, hmaskc.1, hmaskc.2, ihval.2], ?_⟩
      rw [show (stmtFoot (.store d sh mem val mask) s₁).2 = accessCells mem s₁ (mask.Active s₁) by
        simp only [stmtFoot]]
      rcases mask with _ | m | ⟨m, o⟩ <;> rcases mem with ⟨r, off⟩ | p | ⟨p, bc⟩
      · simp only [memReads] at hmsmem
        have IHval := ihval.1
        have IHoff := (opReads_congr Q off s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHoff]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hoffs : evalOp off s₂ with
            | none => exact .none
            | some offs =>
                exact .some (writeFold_sim Q d
                  (fun _ => Region.cast r) (fun i => offs.data i)
                  (fun i => values.data i) (fun _ => true) s₁ s₂ hag _
                      (by intro c; simp [accessCells, MaskOpt.Active, IHoff.trans hoffs]))
      · simp only [memReads] at hmsmem
        have IHval := ihval.1
        have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHp]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hps : evalOp p s₂ with
            | none => exact .none
            | some ps =>
                exact .some (writeFold_sim Q d
                  (fun i => (ps.data i).1) (fun i => (ps.data i).2)
                  (fun i => values.data i) (fun _ => true) s₁ s₂ hag _
                      (by intro c; simp [accessCells, MaskOpt.Active, IHp.trans hps]))
      · simp only [memReads] at hmsmem
        have IHval := ihval.1
        have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHp]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hps : evalOp p s₂ with
            | none => exact .none
            | some ps =>
                exact .some (writeFold_sim Q d
                  (fun i => (ps.data i).region) (fun i => (ps.data i).address (TileShape.indexToList sh i))
                  (fun i => values.data i) (fun i => true && (ps.data i).inBounds (TileShape.indexToList sh i) bc) s₁ s₂ hag _
                      (by intro c; simp [accessCells, MaskOpt.Active, IHp.trans hps]))
      · simp only [memReads] at hmsmem
        simp only [maskReads] at hmsmask
        have IHval := ihval.1
        have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
        have IHoff := (opReads_congr Q off s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHm, IHoff]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hm : evalOp m s₂ with
            | none => exact .none
            | some ms =>
                cases hoffs : evalOp off s₂ with
                | none => exact .none
                | some offs =>
                    exact .some (writeFold_sim Q d
                      (fun _ => Region.cast r) (fun i => offs.data i)
                      (fun i => values.data i) (fun i => ms.data i) s₁ s₂ hag _
                      (by intro c; simp [accessCells, MaskOpt.Active, IHoff.trans hoffs, IHm.trans hm]))
      · simp only [memReads] at hmsmem
        simp only [maskReads] at hmsmask
        have IHval := ihval.1
        have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
        have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHm, IHp]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hm : evalOp m s₂ with
            | none => exact .none
            | some ms =>
                cases hps : evalOp p s₂ with
                | none => exact .none
                | some ps =>
                    exact .some (writeFold_sim Q d
                      (fun i => (ps.data i).1) (fun i => (ps.data i).2)
                      (fun i => values.data i) (fun i => ms.data i) s₁ s₂ hag _
                      (by intro c; simp [accessCells, MaskOpt.Active, IHp.trans hps, IHm.trans hm]))
      · simp only [memReads] at hmsmem
        simp only [maskReads] at hmsmask
        have IHval := ihval.1
        have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
        have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHm, IHp]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hm : evalOp m s₂ with
            | none => exact .none
            | some ms =>
                cases hps : evalOp p s₂ with
                | none => exact .none
                | some ps =>
                    exact .some (writeFold_sim Q d
                      (fun i => (ps.data i).region) (fun i => (ps.data i).address (TileShape.indexToList sh i))
                      (fun i => values.data i) (fun i => ms.data i && (ps.data i).inBounds (TileShape.indexToList sh i) bc) s₁ s₂ hag _
                      (by intro c; simp [accessCells, MaskOpt.Active, and_assoc, IHp.trans hps, IHm.trans hm]))
      · simp only [memReads] at hmsmem
        simp only [maskReads] at hmsmask
        have IHval := ihval.1
        have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
        have IHoff := (opReads_congr Q off s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHm, IHoff]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hm : evalOp m s₂ with
            | none => exact .none
            | some ms =>
                cases hoffs : evalOp off s₂ with
                | none => exact .none
                | some offs =>
                    exact .some (writeFold_sim Q d
                      (fun _ => Region.cast r) (fun i => offs.data i)
                      (fun i => values.data i) (fun i => ms.data i) s₁ s₂ hag _
                      (by intro c; simp [accessCells, MaskOpt.Active, IHoff.trans hoffs, IHm.trans hm]))
      · simp only [memReads] at hmsmem
        simp only [maskReads] at hmsmask
        have IHval := ihval.1
        have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
        have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHm, IHp]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hm : evalOp m s₂ with
            | none => exact .none
            | some ms =>
                cases hps : evalOp p s₂ with
                | none => exact .none
                | some ps =>
                    exact .some (writeFold_sim Q d
                      (fun i => (ps.data i).1) (fun i => (ps.data i).2)
                      (fun i => values.data i) (fun i => ms.data i) s₁ s₂ hag _
                      (by intro c; simp [accessCells, MaskOpt.Active, IHp.trans hps, IHm.trans hm]))
      · simp only [memReads] at hmsmem
        simp only [maskReads] at hmsmask
        have IHval := ihval.1
        have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
        have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHm, IHp]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hm : evalOp m s₂ with
            | none => exact .none
            | some ms =>
                cases hps : evalOp p s₂ with
                | none => exact .none
                | some ps =>
                    exact .some (writeFold_sim Q d
                      (fun i => (ps.data i).region) (fun i => (ps.data i).address (TileShape.indexToList sh i))
                      (fun i => values.data i) (fun i => ms.data i && (ps.data i).inBounds (TileShape.indexToList sh i) bc) s₁ s₂ hag _
                      (by intro c; simp [accessCells, MaskOpt.Active, and_assoc, IHp.trans hps, IHm.trans hm]))
  | .atomicAdd hnum sh mem val mask, Q, s₁, s₂, hag, hms => by
      simp only [stmtFoot, Set.union_subset_iff] at hms
      obtain ⟨hmsmem, hmsval, hmsmask, haddr⟩ := hms
      have hmemc := memReads_congr Q mem s₁ s₂ hag hmsmem
      have hmaskc := maskReads_congr Q mask s₁ s₂ hag hmsmask
      have ihval := opReads_congr Q val s₁ s₂ hag hmsval
      refine ⟨by simp only [stmtFoot, hmemc.1, hmemc.2, hmaskc.1, hmaskc.2, ihval.2], ?_⟩
      rw [show (stmtFoot (.atomicAdd hnum sh mem val mask) s₁).2 =
        accessCells mem s₁ (mask.Active s₁) by simp only [stmtFoot]]
      rcases mask with _ | m | ⟨m, o⟩ <;> rcases mem with ⟨r, off⟩ | p | ⟨p, bc⟩
      · simp only [memReads] at hmsmem
        have IHval := ihval.1
        have IHoff := (opReads_congr Q off s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHoff]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hoffs : evalOp off s₂ with
            | none => exact .none
            | some offs =>
                refine .some (atomicFold_sim Q hnum
                  (fun _ => Region.cast r) (fun i => offs.data i)
                  (fun i => values.data i) (fun _ => true) s₁ s₂ hag _ haddr
                      (by intro c; simp [accessCells, MaskOpt.Active, IHoff.trans hoffs]))
      · simp only [memReads] at hmsmem
        have IHval := ihval.1
        have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHp]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hps : evalOp p s₂ with
            | none => exact .none
            | some ps =>
                refine .some (atomicFold_sim Q hnum
                  (fun i => (ps.data i).1) (fun i => (ps.data i).2)
                  (fun i => values.data i) (fun _ => true) s₁ s₂ hag _ haddr
                      (by intro c; simp [accessCells, MaskOpt.Active, IHp.trans hps]))
      · simp only [memReads] at hmsmem
        have IHval := ihval.1
        have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHp]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hps : evalOp p s₂ with
            | none => exact .none
            | some ps =>
                refine .some (atomicFold_sim Q hnum
                  (fun i => (ps.data i).region) (fun i => (ps.data i).address (TileShape.indexToList sh i))
                  (fun i => values.data i) (fun i => true && (ps.data i).inBounds (TileShape.indexToList sh i) bc) s₁ s₂ hag _ haddr
                      (by intro c; simp [accessCells, MaskOpt.Active, IHp.trans hps]))
      · simp only [memReads] at hmsmem
        simp only [maskReads] at hmsmask
        have IHval := ihval.1
        have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
        have IHoff := (opReads_congr Q off s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHm, IHoff]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hm : evalOp m s₂ with
            | none => exact .none
            | some ms =>
                cases hoffs : evalOp off s₂ with
                | none => exact .none
                | some offs =>
                    refine .some (atomicFold_sim Q hnum
                      (fun _ => Region.cast r) (fun i => offs.data i)
                      (fun i => values.data i) (fun i => ms.data i) s₁ s₂ hag _ haddr
                      (by intro c; simp [accessCells, MaskOpt.Active, IHoff.trans hoffs, IHm.trans hm]))
      · simp only [memReads] at hmsmem
        simp only [maskReads] at hmsmask
        have IHval := ihval.1
        have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
        have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHm, IHp]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hm : evalOp m s₂ with
            | none => exact .none
            | some ms =>
                cases hps : evalOp p s₂ with
                | none => exact .none
                | some ps =>
                    refine .some (atomicFold_sim Q hnum
                      (fun i => (ps.data i).1) (fun i => (ps.data i).2)
                      (fun i => values.data i) (fun i => ms.data i) s₁ s₂ hag _ haddr
                      (by intro c; simp [accessCells, MaskOpt.Active, IHp.trans hps, IHm.trans hm]))
      · simp only [memReads] at hmsmem
        simp only [maskReads] at hmsmask
        have IHval := ihval.1
        have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
        have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHm, IHp]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hm : evalOp m s₂ with
            | none => exact .none
            | some ms =>
                cases hps : evalOp p s₂ with
                | none => exact .none
                | some ps =>
                    refine .some (atomicFold_sim Q hnum
                      (fun i => (ps.data i).region) (fun i => (ps.data i).address (TileShape.indexToList sh i))
                      (fun i => values.data i) (fun i => ms.data i && (ps.data i).inBounds (TileShape.indexToList sh i) bc) s₁ s₂ hag _ haddr
                      (by intro c; simp [accessCells, MaskOpt.Active, and_assoc, IHp.trans hps, IHm.trans hm]))
      · simp only [memReads] at hmsmem
        simp only [maskReads] at hmsmask
        have IHval := ihval.1
        have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
        have IHoff := (opReads_congr Q off s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHm, IHoff]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hm : evalOp m s₂ with
            | none => exact .none
            | some ms =>
                cases hoffs : evalOp off s₂ with
                | none => exact .none
                | some offs =>
                    refine .some (atomicFold_sim Q hnum
                      (fun _ => Region.cast r) (fun i => offs.data i)
                      (fun i => values.data i) (fun i => ms.data i) s₁ s₂ hag _ haddr
                      (by intro c; simp [accessCells, MaskOpt.Active, IHoff.trans hoffs, IHm.trans hm]))
      · simp only [memReads] at hmsmem
        simp only [maskReads] at hmsmask
        have IHval := ihval.1
        have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
        have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHm, IHp]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hm : evalOp m s₂ with
            | none => exact .none
            | some ms =>
                cases hps : evalOp p s₂ with
                | none => exact .none
                | some ps =>
                    refine .some (atomicFold_sim Q hnum
                      (fun i => (ps.data i).1) (fun i => (ps.data i).2)
                      (fun i => values.data i) (fun i => ms.data i) s₁ s₂ hag _ haddr
                      (by intro c; simp [accessCells, MaskOpt.Active, IHp.trans hps, IHm.trans hm]))
      · simp only [memReads] at hmsmem
        simp only [maskReads] at hmsmask
        have IHval := ihval.1
        have IHm := (opReads_congr Q m s₁ s₂ hag hmsmask).1
        have IHp := (opReads_congr Q p s₁ s₂ hag hmsmem).1
        simp only [stepStmt, IHval, IHm, IHp]
        cases hv : evalOp val s₂ with
        | none => exact .none
        | some values =>
            cases hm : evalOp m s₂ with
            | none => exact .none
            | some ms =>
                cases hps : evalOp p s₂ with
                | none => exact .none
                | some ps =>
                    refine .some (atomicFold_sim Q hnum
                      (fun i => (ps.data i).region) (fun i => (ps.data i).address (TileShape.indexToList sh i))
                      (fun i => values.data i) (fun i => ms.data i && (ps.data i).inBounds (TileShape.indexToList sh i) bc) s₁ s₂ hag _ haddr
                      (by intro c; simp [accessCells, MaskOpt.Active, and_assoc, IHp.trans hps, IHm.trans hm]))
  | .atomicRMW op d sh mem input extra mask dest, Q, s₁, s₂, hag, hms => by
      simp only [stmtFoot, Set.union_subset_iff] at hms
      obtain ⟨hmsmem, hmsin, hmsex, hmsmask, haddr⟩ := hms
      have hmemc := memReads_congr Q mem s₁ s₂ hag hmsmem
      have hmaskc := maskReads_congr Q mask s₁ s₂ hag hmsmask
      have ihin := opReads_congr Q input s₁ s₂ hag hmsin
      have hexc := extraReads_congr Q extra s₁ s₂ hag hmsex
      refine ⟨by simp only [stmtFoot, hmemc.1, hmemc.2, hmaskc.1, hmaskc.2, ihin.2, hexc.1], ?_⟩
      rw [show (stmtFoot (.atomicRMW op d sh mem input extra mask dest) s₁).2 =
        accessCells mem s₁ (mask.Active s₁) by simp only [stmtFoot]]
      simp only [stepStmt]
      exact stepAtomicRMW_sim Q op mem input extra mask dest s₁ s₂ hag hmsmem hmsin hmsex
        hmsmask haddr
  | .forLoop idx n body, Q, s₁, s₂, hag, hms => by
      simp only [stmtFoot] at hms ⊢
      simp only [stepForLoopAux.forLoop_unfold]
      exact loopFoot_congr idx 0 n body Q s₁ s₂ hag hms
  | .forRange idx start stop step body, Q, s₁, s₂, hag, hms => by
      simp only [stmtFoot] at hms ⊢
      simp only [stepForRangeAux.forRange_unfold]
      exact rangeFoot_congr idx start stop step body Q s₁ s₂ hag hms
  | .forRangeDyn idx start stop step body, Q, s₁, s₂, hag, hms => by
      simp only [stmtFoot, Foot.seq_fst, Set.union_subset_iff] at hms
      obtain ⟨⟨hmstart, hmstop, hmstep⟩, hnext⟩ := hms
      have ihstart := opReads_congr Q start s₁ s₂ hag hmstart
      have ihstop := opReads_congr Q stop s₁ s₂ hag hmstop
      have ihstep := opReads_congr Q step s₁ s₂ hag hmstep
      simp only [stepForRangeAux.forRangeDyn_unfold, ← ihstart.1, ← ihstop.1, ← ihstep.1]
      cases hstart : evalOp start s₁ with
      | none =>
          refine ⟨by simp only [stmtFoot, ← ihstart.1, ← ihstop.1, ← ihstep.1, ihstart.2,
            ihstop.2, ihstep.2, hstart], .none⟩
      | some a =>
          cases hstop : evalOp stop s₁ with
          | none =>
              refine ⟨by simp only [stmtFoot, ← ihstart.1, ← ihstop.1, ← ihstep.1, ihstart.2,
                ihstop.2, ihstep.2, hstart, hstop], .none⟩
          | some b =>
              cases hstep : evalOp step s₁ with
              | none =>
                  refine ⟨by simp only [stmtFoot, ← ihstart.1, ← ihstop.1, ← ihstep.1,
                    ihstart.2, ihstop.2, ihstep.2, hstart, hstop, hstep], .none⟩
              | some c =>
                  simp only [hstart, hstop, hstep] at hnext
                  have ih := rangeFoot_congr idx _ _ _ body Q s₁ s₂ hag hnext
                  refine ⟨by simp only [stmtFoot, ← ihstart.1, ← ihstop.1, ← ihstep.1,
                    ihstart.2, ihstop.2, ihstep.2, hstart, hstop, hstep, ih.1], ?_⟩
                  rw [show (stmtFoot (.forRangeDyn idx start stop step body) s₁).2 =
                      (rangeFoot idx (a.data PUnit.unit) (b.data PUnit.unit)
                        (c.data PUnit.unit) body s₁).2 by
                    simp [stmtFoot, hstart, hstop, hstep]]
                  exact ih.2
  | .forRangeInt idx start stop step body, Q, s₁, s₂, hag, hms => by
      simp only [stmtFoot, Foot.seq_fst, Set.union_subset_iff] at hms
      obtain ⟨⟨hmstart, hmstop, hmstep⟩, hnext⟩ := hms
      have ihstart := opReads_congr Q start s₁ s₂ hag hmstart
      have ihstop := opReads_congr Q stop s₁ s₂ hag hmstop
      have ihstep := opReads_congr Q step s₁ s₂ hag hmstep
      simp only [stepForRangeIntAux.forRangeInt_unfold, ← ihstart.1, ← ihstop.1, ← ihstep.1]
      cases hstart : evalOp start s₁ with
      | none =>
          refine ⟨by simp only [stmtFoot, ← ihstart.1, ← ihstop.1, ← ihstep.1, ihstart.2,
            ihstop.2, ihstep.2, hstart], .none⟩
      | some a =>
          cases hstop : evalOp stop s₁ with
          | none =>
              refine ⟨by simp only [stmtFoot, ← ihstart.1, ← ihstop.1, ← ihstep.1, ihstart.2,
                ihstop.2, ihstep.2, hstart, hstop], .none⟩
          | some b =>
              cases hstep : evalOp step s₁ with
              | none =>
                  refine ⟨by simp only [stmtFoot, ← ihstart.1, ← ihstop.1, ← ihstep.1,
                    ihstart.2, ihstop.2, ihstep.2, hstart, hstop, hstep], .none⟩
              | some c =>
                  simp only [hstart, hstop, hstep] at hnext
                  have ih := rangeIntFoot_congr idx _ _ _ body Q s₁ s₂ hag hnext
                  refine ⟨by simp only [stmtFoot, ← ihstart.1, ← ihstop.1, ← ihstep.1,
                    ihstart.2, ihstop.2, ihstep.2, hstart, hstop, hstep, ih.1], ?_⟩
                  rw [show (stmtFoot (.forRangeInt idx start stop step body) s₁).2 =
                      (rangeIntFoot idx (a.data PUnit.unit) (b.data PUnit.unit)
                        (c.data PUnit.unit) body s₁).2 by
                    simp [stmtFoot, hstart, hstop, hstep]]
                  exact ih.2
  | .ifThen c body, Q, s₁, s₂, hag, hms => by
      simp only [stmtFoot, Foot.seq_fst, Set.union_subset_iff] at hms
      obtain ⟨hmc, hbody⟩ := hms
      have ihc := opReads_congr Q c s₁ s₂ hag hmc
      simp only [stepStmt, ← ihc.1]
      cases hc : evalOp c s₁ with
      | none =>
          exact ⟨by simp only [stmtFoot, ← ihc.1, ihc.2, hc], .none⟩
      | some vc =>
          simp only [hc] at hbody
          by_cases hb : vc.data PUnit.unit = true
          · simp only [hb, if_true] at hbody
            have ih := stmtsFoot_congr body Q s₁ s₂ hag hbody
            refine ⟨by simp only [stmtFoot, ← ihc.1, ihc.2, hc, hb, if_true, ih.1], ?_⟩
            rw [show (stmtFoot (.ifThen c body) s₁).2 = (stmtsFoot body s₁).2 by
              simp [stmtFoot, hc, hb]]
            simpa only [Option.bind_eq_bind, Option.bind_some, hb, ↓reduceIte] using ih.2
          · refine ⟨by simp only [stmtFoot, ← ihc.1, ihc.2, hc, hb, if_false, Bool.false_eq_true],
              ?_⟩
            rw [show (stmtFoot (.ifThen c body) s₁).2 = ∅ by simp [stmtFoot, hc, hb]]
            simpa only [Option.bind_eq_bind, Option.bind_some, hb, Bool.false_eq_true, ↓reduceIte] using
              (OptionRel.some (SimRel.refl hag) : StepSim Q ∅ s₁ s₂ (some s₁) (some s₂))
  | .ifThenElse c tb eb, Q, s₁, s₂, hag, hms => by
      simp only [stmtFoot, Foot.seq_fst, Set.union_subset_iff] at hms
      obtain ⟨hmc, hbody⟩ := hms
      have ihc := opReads_congr Q c s₁ s₂ hag hmc
      simp only [stepStmt, ← ihc.1]
      cases hc : evalOp c s₁ with
      | none =>
          exact ⟨by simp only [stmtFoot, ← ihc.1, ihc.2, hc], .none⟩
      | some vc =>
          simp only [hc] at hbody
          by_cases hb : vc.data PUnit.unit = true
          · simp only [hb, if_true] at hbody
            have ih := stmtsFoot_congr tb Q s₁ s₂ hag hbody
            refine ⟨by simp only [stmtFoot, ← ihc.1, ihc.2, hc, hb, if_true, ih.1], ?_⟩
            rw [show (stmtFoot (.ifThenElse c tb eb) s₁).2 = (stmtsFoot tb s₁).2 by
              simp [stmtFoot, hc, hb]]
            simpa only [Option.bind_eq_bind, Option.bind_some, hb, ↓reduceIte] using ih.2
          · simp only [hb, if_false, Bool.false_eq_true] at hbody
            have ih := stmtsFoot_congr eb Q s₁ s₂ hag hbody
            refine ⟨by simp only [stmtFoot, ← ihc.1, ihc.2, hc, hb, if_false, Bool.false_eq_true,
              ih.1], ?_⟩
            rw [show (stmtFoot (.ifThenElse c tb eb) s₁).2 = (stmtsFoot eb s₁).2 by
              simp [stmtFoot, hc, hb]]
            simpa only [Option.bind_eq_bind, Option.bind_some, hb, Bool.false_eq_true, ↓reduceIte] using ih.2
  termination_by st _ _ _ _ _ => (sizeOf st, 0)
  decreasing_by
    all_goals simp_wf
    all_goals (try omega)
    all_goals (have : 0 < sizeOf idx := by cases idx; simp)
    all_goals omega

/-- A statement list reads only its read set. -/
theorem stmtsFoot_congr :
    ∀ (l : List Stmt) (Q : Set BlockCell) (s₁ s₂ : BlockState), BlockAgree Q s₁ s₂ →
      (stmtsFoot l s₁).1 ⊆ Q →
      stmtsFoot l s₂ = stmtsFoot l s₁ ∧
        StepSim Q (stmtsFoot l s₁).2 s₁ s₂ (stepStmts l s₁) (stepStmts l s₂)
  | [], Q, s₁, s₂, hag, _ => by
      refine ⟨by simp only [stmtsFoot], ?_⟩
      rw [show (stmtsFoot [] s₁).2 = ∅ by simp only [stmtsFoot]]
      simp only [stepStmts.nil]
      exact .some (SimRel.refl hag)
  | st :: rest, Q, s₁, s₂, hag, hms => by
      simp only [stmtsFoot, Foot.seq_fst, Set.union_subset_iff] at hms
      obtain ⟨hst, hrest⟩ := hms
      obtain ⟨hfoot, hsim⟩ := stmtFoot_congr st Q s₁ s₂ hag hst
      cases h1 : stepStmt st s₁ with
      | none =>
          cases h2 : stepStmt st s₂ with
          | some t2 => rw [h1, h2] at hsim; cases hsim
          | none =>
              refine ⟨by simp only [stmtsFoot, hfoot, h1, h2], ?_⟩
              rw [stepStmts.cons_none h1, stepStmts.cons_none h2]
              exact .none
      | some t1 =>
          cases h2 : stepStmt st s₂ with
          | none => rw [h1, h2] at hsim; cases hsim
          | some t2 =>
              rw [h1, h2] at hsim
              cases hsim with
              | some hrel =>
                  simp only [h1] at hrest
                  obtain ⟨hf2, hsim2⟩ := stmtsFoot_congr rest (Q ∪ (stmtFoot st s₁).2) t1 t2
                    hrel.1 (fun c hc => Or.inl (hrest hc))
                  refine ⟨by simp only [stmtsFoot, hfoot, h1, h2, hf2], ?_⟩
                  rw [show (stmtsFoot (st :: rest) s₁).2 =
                      (stmtFoot st s₁).2 ∪ (stmtsFoot rest t1).2 by simp [stmtsFoot, h1]]
                  rw [stepStmts.cons_some h1, stepStmts.cons_some h2]
                  exact optionRel_mono hsim2 fun _ _ h => hrel.trans h
  termination_by l _ _ _ _ _ => (sizeOf l, 0)
  decreasing_by all_goals (simp_wf; omega)

/-- The `forLoop` iterations read only their read set. -/
theorem loopFoot_congr :
    ∀ (idx : RegName) (start n : Nat) (body : List Stmt) (Q : Set BlockCell)
      (s₁ s₂ : BlockState), BlockAgree Q s₁ s₂ → (loopFoot idx start n body s₁).1 ⊆ Q →
      loopFoot idx start n body s₂ = loopFoot idx start n body s₁ ∧
        StepSim Q (loopFoot idx start n body s₁).2 s₁ s₂
          (stepForLoopAux idx start n body s₁) (stepForLoopAux idx start n body s₂)
  | idx, start, n, body, Q, s₁, s₂, hag, hms => by
      by_cases hlt : start < n
      · rw [loopFoot_lt hlt] at hms
        simp only [Foot.seq_fst, Set.union_subset_iff] at hms
        obtain ⟨hbody, hnext⟩ := hms
        obtain ⟨hfb, hsb⟩ := stmtsFoot_congr body Q _ _
          (hag.setReg idx .nat [] (Tile.scalar start)) hbody
        rw [stepForLoopAux.step_lt hlt, stepForLoopAux.step_lt hlt]
        cases h1 : stepStmts body (s₁.setReg idx .nat [] (Tile.scalar start)) with
        | none =>
            cases h2 : stepStmts body (s₂.setReg idx .nat [] (Tile.scalar start)) with
            | some _ => rw [h1, h2] at hsb; cases hsb
            | none => exact ⟨by simp only [loopFoot_lt hlt, hfb, h1, h2], .none⟩
        | some t1 =>
            cases h2 : stepStmts body (s₂.setReg idx .nat [] (Tile.scalar start)) with
            | none => rw [h1, h2] at hsb; cases hsb
            | some t2 =>
                rw [h1, h2] at hsb
                cases hsb with
                | some hrel =>
                    simp only [h1] at hnext
                    obtain ⟨hf2, hs2⟩ := loopFoot_congr idx (start + 1) n body
                      (Q ∪ (stmtsFoot body (s₁.setReg idx .nat [] (Tile.scalar start))).2) t1 t2
                      hrel.1 (fun c hc => Or.inl (hnext hc))
                    refine ⟨by simp only [loopFoot_lt hlt, hfb, h1, h2, hf2], ?_⟩
                    rw [show (loopFoot idx start n body s₁).2 =
                        (stmtsFoot body (s₁.setReg idx .nat [] (Tile.scalar start))).2 ∪
                          (loopFoot idx (start + 1) n body t1).2 by simp [loopFoot_lt hlt, h1]]
                    simp only [Option.bind_some]
                    exact optionRel_mono hs2 fun _ _ h => hrel.setReg_base.trans h
      · refine ⟨by simp only [loopFoot_ge hlt], ?_⟩
        rw [show (loopFoot idx start n body s₁).2 = ∅ by simp [loopFoot_ge hlt]]
        rw [stepForLoopAux.step_ge (Nat.le_of_not_lt hlt),
          stepForLoopAux.step_ge (Nat.le_of_not_lt hlt)]
        exact .some (SimRel.refl hag)
  termination_by idx start n body _ _ _ _ _ => (sizeOf body + 1, n - start)
  decreasing_by all_goals omega

/-- The `forRange` iterations read only their read set. -/
theorem rangeFoot_congr :
    ∀ (idx : RegName) (cur stop step : Nat) (body : List Stmt) (Q : Set BlockCell)
      (s₁ s₂ : BlockState), BlockAgree Q s₁ s₂ → (rangeFoot idx cur stop step body s₁).1 ⊆ Q →
      rangeFoot idx cur stop step body s₂ = rangeFoot idx cur stop step body s₁ ∧
        StepSim Q (rangeFoot idx cur stop step body s₁).2 s₁ s₂
          (stepForRangeAux idx cur stop step body s₁) (stepForRangeAux idx cur stop step body s₂)
  | idx, cur, stop, step, body, Q, s₁, s₂, hag, hms => by
      by_cases hz : step = 0
      · subst hz
        refine ⟨by simp only [rangeFoot_zero], ?_⟩
        rw [show (rangeFoot idx cur stop 0 body s₁).2 = ∅ by simp [rangeFoot_zero]]
        rw [stepForRangeAux.step_zero_step, stepForRangeAux.step_zero_step]
        exact .some (SimRel.refl hag)
      by_cases hlt : cur < stop
      · rw [rangeFoot_lt hz hlt] at hms
        simp only [Foot.seq_fst, Set.union_subset_iff] at hms
        obtain ⟨hbody, hnext⟩ := hms
        obtain ⟨hfb, hsb⟩ := stmtsFoot_congr body Q _ _
          (hag.setReg idx .nat [] (Tile.scalar cur)) hbody
        rw [stepForRangeAux.step_lt hz hlt, stepForRangeAux.step_lt hz hlt]
        cases h1 : stepStmts body (s₁.setReg idx .nat [] (Tile.scalar cur)) with
        | none =>
            cases h2 : stepStmts body (s₂.setReg idx .nat [] (Tile.scalar cur)) with
            | some _ => rw [h1, h2] at hsb; cases hsb
            | none => exact ⟨by simp only [rangeFoot_lt hz hlt, hfb, h1, h2], .none⟩
        | some t1 =>
            cases h2 : stepStmts body (s₂.setReg idx .nat [] (Tile.scalar cur)) with
            | none => rw [h1, h2] at hsb; cases hsb
            | some t2 =>
                rw [h1, h2] at hsb
                cases hsb with
                | some hrel =>
                    simp only [h1] at hnext
                    obtain ⟨hf2, hs2⟩ := rangeFoot_congr idx (cur + step) stop step body
                      (Q ∪ (stmtsFoot body (s₁.setReg idx .nat [] (Tile.scalar cur))).2) t1 t2
                      hrel.1 (fun c hc => Or.inl (hnext hc))
                    refine ⟨by simp only [rangeFoot_lt hz hlt, hfb, h1, h2, hf2], ?_⟩
                    rw [show (rangeFoot idx cur stop step body s₁).2 =
                        (stmtsFoot body (s₁.setReg idx .nat [] (Tile.scalar cur))).2 ∪
                          (rangeFoot idx (cur + step) stop step body t1).2 by
                      simp [rangeFoot_lt hz hlt, h1]]
                    simp only [Option.bind_some]
                    exact optionRel_mono hs2 fun _ _ h => hrel.setReg_base.trans h
      · refine ⟨by simp only [rangeFoot_ge hz hlt], ?_⟩
        rw [show (rangeFoot idx cur stop step body s₁).2 = ∅ by simp [rangeFoot_ge hz hlt]]
        rw [stepForRangeAux.step_ge hz (Nat.le_of_not_lt hlt),
          stepForRangeAux.step_ge hz (Nat.le_of_not_lt hlt)]
        exact .some (SimRel.refl hag)
  termination_by idx cur stop step body _ _ _ _ _ => (sizeOf body + 1, stop - cur)
  decreasing_by all_goals omega

/-- The `forRange` iterations over integers read only their read set. -/
theorem rangeIntFoot_congr :
    ∀ (idx : RegName) (cur stop : Int) (step : Nat) (body : List Stmt) (Q : Set BlockCell)
      (s₁ s₂ : BlockState), BlockAgree Q s₁ s₂ →
      (rangeIntFoot idx cur stop step body s₁).1 ⊆ Q →
      rangeIntFoot idx cur stop step body s₂ = rangeIntFoot idx cur stop step body s₁ ∧
        StepSim Q (rangeIntFoot idx cur stop step body s₁).2 s₁ s₂
          (stepForRangeIntAux idx cur stop step body s₁)
          (stepForRangeIntAux idx cur stop step body s₂)
  | idx, cur, stop, step, body, Q, s₁, s₂, hag, hms => by
      by_cases hz : step = 0
      · subst hz
        refine ⟨by simp only [rangeIntFoot_zero], ?_⟩
        rw [show (rangeIntFoot idx cur stop 0 body s₁).2 = ∅ by simp [rangeIntFoot_zero]]
        rw [stepForRangeIntAux.step_zero_step, stepForRangeIntAux.step_zero_step]
        exact .some (SimRel.refl hag)
      by_cases hlt : cur < stop
      · rw [rangeIntFoot_lt hz hlt] at hms
        simp only [Foot.seq_fst, Set.union_subset_iff] at hms
        obtain ⟨hbody, hnext⟩ := hms
        obtain ⟨hfb, hsb⟩ := stmtsFoot_congr body Q _ _
          (hag.setReg idx .int [] (Tile.scalar cur)) hbody
        rw [stepForRangeIntAux.step_lt hz hlt, stepForRangeIntAux.step_lt hz hlt]
        cases h1 : stepStmts body (s₁.setReg idx .int [] (Tile.scalar cur)) with
        | none =>
            cases h2 : stepStmts body (s₂.setReg idx .int [] (Tile.scalar cur)) with
            | some _ => rw [h1, h2] at hsb; cases hsb
            | none => exact ⟨by simp only [rangeIntFoot_lt hz hlt, hfb, h1, h2], .none⟩
        | some t1 =>
            cases h2 : stepStmts body (s₂.setReg idx .int [] (Tile.scalar cur)) with
            | none => rw [h1, h2] at hsb; cases hsb
            | some t2 =>
                rw [h1, h2] at hsb
                cases hsb with
                | some hrel =>
                    simp only [h1] at hnext
                    obtain ⟨hf2, hs2⟩ := rangeIntFoot_congr idx (cur + step) stop step body
                      (Q ∪ (stmtsFoot body (s₁.setReg idx .int [] (Tile.scalar cur))).2) t1 t2
                      hrel.1 (fun c hc => Or.inl (hnext hc))
                    refine ⟨by simp only [rangeIntFoot_lt hz hlt, hfb, h1, h2, hf2], ?_⟩
                    rw [show (rangeIntFoot idx cur stop step body s₁).2 =
                        (stmtsFoot body (s₁.setReg idx .int [] (Tile.scalar cur))).2 ∪
                          (rangeIntFoot idx (cur + step) stop step body t1).2 by
                      simp [rangeIntFoot_lt hz hlt, h1]]
                    simp only [Option.bind_some]
                    exact optionRel_mono hs2 fun _ _ h => hrel.setReg_base.trans h
      · refine ⟨by simp only [rangeIntFoot_ge hz hlt], ?_⟩
        rw [show (rangeIntFoot idx cur stop step body s₁).2 = ∅ by simp [rangeIntFoot_ge hz hlt]]
        rw [stepForRangeIntAux.step_ge hz (Int.not_lt.mp hlt),
          stepForRangeIntAux.step_ge hz (Int.not_lt.mp hlt)]
        exact .some (SimRel.refl hag)
  termination_by idx cur stop step body _ _ _ _ _ => (sizeOf body + 1, (stop - cur).toNat)
  decreasing_by all_goals omega

end

/-- A one-statement list has the footprint of its statement. -/
@[simp] theorem stmtsFoot_singleton (st : Stmt) (s : BlockState) :
    stmtsFoot [st] s = stmtFoot st s := by
  rw [stmtsFoot]
  cases stepStmt st s <;> simp [stmtsFoot, Foot.seq]

end VeriTile.Dist
