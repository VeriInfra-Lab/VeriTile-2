import VeriTile.Interp.Bridge.Exec

namespace VeriTile.Interp
open VeriTile.Triton VeriTile.Triton.FP

namespace FiniteBridge
local notation "S" => Structural.State (WithBot ℝ)
local notation "SE" => Structural.evalOp realAlgebra

/-- A region may be read only at its declared tag. Byte regions are read-only
inputs to float8 decoding. All offsets are covered, including symbolic ones. -/
structure Layout where
  reads : RegionName → TileDType → Prop
  bytes : RegionName → Prop

def FiniteValue : (d : TileDType) → Structural.Value (WithBot ℝ) d → Prop
  | .real, v | .fp32, v | .fp16, v | .bf16, v | .f8e4, v | .f8e5, v => ∃ x : ℝ, v = ↑x
  | _, _ => True

structure Invariant (L : Layout) (s : S) : Prop where
  cells : ∀ r d, L.reads r d → ∀ o, ∃ v, s.mem r o = .mk d v ∧ FiniteValue d v
  registers : ∀ d sh n v, s.regs d sh n = some v → ∀ i, FiniteValue d (v i)
  undefined : ∀ d masked r o, UndefAgrees s d masked r o
  bytes : ∀ r, L.bytes r → ∀ o, let b := (s.mem r o).read .int
    Float8E5Bits.isInt8 b = true → (Float8E5Bits.ofInt b).decodeRat.isSome = true

private theorem undef_of_eq {s t : S} (h : t.undef = s.undef)
    (hu : ∀ d m r o, UndefAgrees s d m r o) : ∀ d m r o, UndefAgrees t d m r o := by
  intro d m r o
  specialize hu d m r o
  cases d <;> simpa only [UndefAgrees, BlockState.unspecifiedValue, erase_undef, h] using hu

theorem Invariant.setReg {L s} (hs : Invariant L s) (n d sh v)
    (hv : ∀ i, FiniteValue d (v i)) : Invariant L (s.setReg n d sh v) := by
  refine ⟨hs.cells, ?_, undef_of_eq rfl hs.undefined, hs.bytes⟩
  intro d' sh' n' v' h i
  by_cases hn : n' = n
  · subst n'
    by_cases hd : d = d'
    · subst d'
      by_cases hh : sh = sh'
      · subst sh'; simp only [Structural.State.setReg_same, Option.some.injEq] at h
        exact h ▸ hv i
      · simp [Structural.State.setReg, hh] at h
    · simp [Structural.State.setReg, hd] at h
  · exact hs.registers _ _ _ _ (by simpa [Structural.State.setReg, hn] using h) i

def Writable (L : Layout) (r : RegionName) (d : TileDType) : Prop :=
  (∀ d', L.reads r d' → d' = d) ∧ ¬ L.bytes r

theorem Invariant.write {L s} (hs : Invariant L s) {r d} (hw : Writable L r d)
    (o v) (hv : FiniteValue d v) : Invariant L (s.write r o (.mk d v)) := by
  refine ⟨?_, hs.registers, undef_of_eq rfl hs.undefined, ?_⟩
  · intro r' d' hr o'
    by_cases h : r' = r ∧ o' = o
    · obtain ⟨rfl, rfl⟩ := h
      obtain rfl := hw.1 d' hr
      exact ⟨_, Structural.State.write_same .., hv⟩
    · rw [Structural.State.write_other _ _ _ _ _ _ (by tauto)]
      exact hs.cells _ _ hr _
  · intro r' hb o'
    have h : r' ≠ r := fun e => hw.2 (e ▸ hb)
    simpa only [Structural.State.write_other _ _ _ _ _ _ (Or.inl h)] using hs.bytes r' hb o'

theorem Invariant.loadOk {L s} (hs : Invariant L s) {d sh} {r : Region d}
    (hr : L.reads (Region.cast r) d) (off : Op .nat sh) (mask : MaskOpt d sh) (pad) :
    LoadOk s (.load d (.region r off) mask pad) := by
  intro p addr active ha _ i
  simp only [laneAddrs] at ha
  cases he : SE p off s with
  | none => simp [he] at ha
  | some offsets =>
    simp only [he, Option.map_some, Option.some.injEq] at ha
    subst addr
    refine ⟨fun _ _ => ?_, fun _ _ _ => hs.undefined .., fun _ _ _ => hs.undefined ..⟩
    obtain ⟨v, hc, hv⟩ := hs.cells _ _ hr (offsets i)
    refine ⟨?_, fun _ => ⟨v,hc⟩⟩
    intro v' hv'
    rw [hc] at hv'
    cases hv'
    cases d <;> first | rfl | (obtain ⟨x,rfl⟩ := hv; rfl)

private theorem readRegion {d sh} (r : Region d) (off : Op .nat sh) (pad) (s : S) (p)
    (v) (h : SE p (.load d (.region r off) .none pad) s = some v) :
    ∃ offsets : Structural.Values (WithBot ℝ) .nat sh,
      v = fun i => (s.mem (Region.cast r) (offsets i)).read d := by
  rw [Structural.evalOp_unfold] at h
  cases he : SE p off s with
  | none => simp [he] at h
  | some offsets => exact ⟨offsets, by simpa [he] using h.symm⟩

theorem Invariant.decode {L s} (hs : Invariant L s) {sh} (r : Region .int)
    (hr : L.bytes (Region.cast r)) (off : Op .nat sh) (pad dst) :
    DecodesFinite s (.decodeFloat8E5 dst (.load .int (.region r off) .none pad)) := by
  intro p v h i
  obtain ⟨offsets, rfl⟩ := readRegion _ _ _ _ _ _ h
  exact hs.bytes _ hr (offsets i)

/-- A conservative syntactic grammar of finite right-hand sides. In particular
there is no constructor for a floating negative infinity. Discrete results
are always finite; their nested operations still have to satisfy the bridge. -/
inductive FiniteOp (L : Layout) : {d : TileDType} → {sh : TileShape} → Op d sh → Prop
  | nat (e : Op .nat sh) : FiniteOp L e
  | literal (c) : FiniteOp L (.const c)
  | reg (d sh n) : FiniteOp L (.ref d sh n)
  | fromNat (e : Op .nat sh) : FiniteOp L (.natToReal e)
  | precision {e : Op .real sh} (p) : FiniteOp L e → FiniteOp L (.withPrecision .real p e)
  | bf16 {e : Op .real sh} : FiniteOp L e → FiniteOp L (.castFloat .real .bf16 e)
  | add (bc : Broadcast a b sh) {x y} : FiniteOp L x → FiniteOp L y → FiniteOp L (.add .real bc x y)
  | sub (bc : Broadcast a b sh) {x y} : FiniteOp L x → FiniteOp L y → FiniteOp L (.sub .real bc x y)
  | mul (bc : Broadcast a b sh) {x y} : FiniteOp L x → FiniteOp L y → FiniteOp L (.mul .real bc x y)
  | div (bc : Broadcast a b sh) {x y} : FiniteOp L x → FiniteOp L y → FiniteOp L (.div .real bc x y)
  | load (r : Region d) (off : Op .nat sh) (pad) : L.reads (Region.cast r) d →
      FiniteOp L (.load d (.region r off) .none pad)
  | decode (r : Region .int) (off : Op .nat sh) (pad) : L.bytes (Region.cast r) →
      FiniteOp L (.decodeFloat8E5 .real (.load .int (.region r off) .none pad))

theorem FiniteOp.finite {L s} (hs : Invariant L s) {d sh} {e : Op d sh} (he : FiniteOp L e)
    (p v) (h : SE p e s = some v) (i) : FiniteValue d (v i) := by
  induction he generalizing p with
  | nat => trivial
  | literal => rw [Structural.evalOp_unfold] at h; cases h; exact ⟨_, rfl⟩
  | reg => rw [Structural.evalOp_unfold] at h; exact hs.registers _ _ _ _ h _
  | fromNat e =>
    rw [Structural.evalOp_unfold] at h
    cases ha : SE p e s <;> simp [ha] at h
    subst v; exact ⟨_, rfl⟩
  | precision p' _ ih => rw [Structural.evalOp_unfold] at h; exact ih _ _ h i
  | bf16 ha ih =>
    rw [Structural.evalOp_unfold] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨a, ea, ht⟩ := h
    cases ht
    exact ih p a ea i
  | load r off pad hr =>
    obtain ⟨offsets,rfl⟩ := readRegion _ _ _ _ _ _ h
    obtain ⟨x,hx,hf⟩ := hs.cells _ _ hr (offsets i)
    simpa [hx] using hf
  | decode r off pad hr =>
    rw [Structural.evalOp_unfold] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨f,hf,b,hb,hret⟩ := h
    change some _ = some f at hf
    cases hf
    split at hret
    · cases hret; exact ⟨_,rfl⟩
    · contradiction
  | add bc _ _ ihx ihy | sub bc _ _ ihx ihy | mul bc _ _ ihx ihy | div bc _ _ ihx ihy =>
    rw [Structural.evalOp_unfold] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, ht⟩ := h
    cases ht
    obtain ⟨u,hu⟩ := ihx p a ha (bc.leftIndex i)
    obtain ⟨v,hv⟩ := ihy p b hb (bc.rightIndex i)
    simp only [FiniteValue, Structural.bop, Structural.numeric, realAlgebra, hu, hv,
      WithBot.realAdd_coe_coe, WithBot.realSub_coe_coe, WithBot.realMul_coe_coe, WithBot.realDiv_coe_coe]
    exact ⟨_,rfl⟩

inductive FiniteExpr (L : Layout) : {d : TileDType} → {sh : TileShape} → ComputeExpr d sh → Prop
  | alg {e : Op d sh} : FiniteOp L e → FiniteExpr L (.alg e)
  | typed (cd) {e : Op cd.eraseDType sh} : FiniteOp L e → FiniteExpr L (.compute (.alg cd e))
  | load (r : Region .real) (off : Op .nat sh) (pad) : L.reads (Region.cast r) .real →
      FiniteExpr L (.compute (.load .fp32 (.region r off) .none pad))

theorem FiniteExpr.finite {L s} (hs : Invariant L s) {d sh} {e : ComputeExpr d sh} (he : FiniteExpr L e)
    (v) (h : Structural.evalExpr realAlgebra e s = some v) (i) : FiniteValue d (v i) := by
  cases he with
  | alg he => exact he.finite hs none v h i
  | typed cd he => exact he.finite hs (some cd) v h i
  | load r off pad hr =>
    simp only [Structural.evalExpr, Structural.evalComputeOp, bind, Option.bind_eq_some_iff] at h
    obtain ⟨a,ha,ht⟩ := h
    cases ht
    exact (FiniteOp.load r off pad hr).finite hs (some .fp32) a ha i

/-- The operand of a certified decode reads a byte from a declared input. -/
inductive ByteInput (L : Layout) : {sh : TileShape} → Op .int sh → Prop
  | load (r : Region .int) (off : Op .nat sh) (pad) : L.bytes (Region.cast r) →
      ByteInput L (.load .int (.region r off) .none pad)

def ReadSite (L : Layout) : {d : TileDType} → {sh : TileShape} → Op d sh → Prop
  | _, _, .load d (.region r _) _ _ => L.reads (Region.cast r) d
  | _, _, .load .. => False
  | _, _, _ => True

def DecodeSite (L : Layout) : {d : TileDType} → {sh : TileShape} → Op d sh → Prop
  | _, _, .decodeFloat8E5 _ e => ByteInput L e
  | _, _, _ => True

def StaticSite (L : Layout) {d sh} (e : Op d sh) : Prop :=
  StructuralNode e ∧ NonEmptyArgMax e ∧ ReshapeSameSize e ∧ DecodeSite L e ∧ ReadSite L e

private theorem StaticSite.sound {L s} (hs : Invariant L s) {d sh} (e : Op d sh)
    (h : StaticSite L e) : BridgeSite s e := by
  obtain ⟨structural, argmax, reshape, bytes, read⟩ := h
  refine ⟨structural, argmax, reshape, ?_, ?_⟩
  · cases e <;> try trivial
    case decodeFloat8E5 =>
      cases bytes with
      | load r off pad hr => exact hs.decode r hr off pad _
  · cases e <;> try trivial
    case load =>
      cases ‹MemAccess _ _› with
      | region r off => exact hs.loadOk read off _ _
      | ptr | blockPtr => exact False.elim read

/-- A syntax tree all of whose nodes meet the layout's site rules. Quantifying
over consequences lets a client use the existing heterogeneous traversal
`AllNodes` both to build the certificate and to specialize it to a state. -/
def CheckedNodes (L : Layout) {d sh} (e : Op d sh) : Prop :=
  ∀ P : ∀ {d sh}, Op d sh → Prop, (∀ {d sh} (x : Op d sh), StaticSite L x → P x) → AllNodes P e

theorem CheckedNodes.sound {L s d sh} {e : Op d sh} (h : CheckedNodes L e) (hs : Invariant L s) :
    AllNodes (BridgeSite s) e := h (BridgeSite s) (StaticSite.sound hs)

def CheckedExpr (L : Layout) {d sh} (e : ComputeExpr d sh) : Prop :=
  ∀ op, e.toAlgorithm? = .ok op → CheckedNodes L op

theorem CheckedExpr.sound {L d sh s} {e : ComputeExpr d sh} (h : CheckedExpr L e)
    (hs : Invariant L s) : ExprSite s e := fun op hp => (h op hp).sound hs

/-- A certificate follows the syntax once. Site obligations inspect each
projected expression independently of the path or loop count. The finite-value grammar and write permissions are checked at stores. -/
inductive Code (L : Layout) : List ComputeStmt → Prop
  | nil : Code L []
  | assign {d sh n e tail} : FiniteExpr L e →
      CheckedExpr L e → Code L tail → Code L (.assign d sh n e :: tail)
  | store {d sh e tail} (r : Region d) (off : Op .nat sh) :
      Writable L (Region.cast r) d → FiniteExpr L e →
      (CheckedExpr L e ∧ CheckedNodes L off) →
      Code L tail → Code L (.store d sh (.region r off) e .none :: tail)
  | loop {idx n body tail} : Code L body → Code L tail → Code L (.forLoop idx n body :: tail)

private def Good (L : Layout) (body : List ComputeStmt) : Prop :=
  ∀ s, Invariant L s → StmtsPre body s ∧
    ∀ t, Structural.run realAlgebra body s = some t → Invariant L t

private theorem goodLoop {L idx stop body} (hg : Good L body) (start : Nat) (s : S)
    (hs : Invariant L s) : LoopPre idx start stop body s ∧
      ∀ t, Structural.loop realAlgebra idx start stop body s = some t → Invariant L t := by
  rw [LoopPre, Structural.loop]
  split
  · let u := s.setReg idx .nat [] fun _ => start
    obtain ⟨pre, preserved⟩ := hg u (hs.setReg _ _ _ _ (fun _ => trivial))
    refine ⟨⟨pre, fun t ht => (goodLoop hg (start + 1) t (preserved t ht)).1⟩, ?_⟩
    intro t ht
    obtain ⟨a, ha, ht⟩ := Option.bind_eq_some_iff.mp ht
    exact (goodLoop hg (start + 1) a (preserved a ha)).2 t ht
  · exact ⟨trivial, fun _ ht => Option.some.inj ht ▸ hs⟩
termination_by stop - start
decreasing_by all_goals omega

private theorem goodCons {L st body} (htail : Good L body)
    (head : ∀ s, Invariant L s → StmtPre st s ∧ ∀ t, Structural.step realAlgebra st s = some t → Invariant L t) :
    Good L (st :: body) := by
  intro s hs
  obtain ⟨hp,hkeep⟩ := head s hs
  rw [StmtsPre, Structural.run]
  refine ⟨⟨hp,fun t ht => (htail t (hkeep t ht)).1⟩, ?_⟩
  intro t ht
  obtain ⟨u, hu, ht⟩ := Option.bind_eq_some_iff.mp ht
  exact (htail u (hkeep u hu)).2 t ht

private theorem store_preserves {L d sh} {r : Region d} {off : Op .nat sh}
    (hw : Writable L (Region.cast r) d) {s t : S} (hs : Invariant L s) {v}
    (hv : ∀ i, FiniteValue d (v i))
    (h : Structural.store realAlgebra (.region r off) .none v s = some t) : Invariant L t := by
  simp only [Structural.store] at h
  cases ho : SE none off s with
  | none => simp [ho] at h
  | some offsets =>
    simp [ho] at h
    subst t
    clear ho
    induction TileShape.allIndices sh generalizing s with
    | nil => exact hs
    | cons i rest ih =>
      exact ih (hs.write hw _ _ (hv i))

private theorem Code.good {L body} (hc : Code L body) : Good L body := by
  induction hc with
  | nil =>
    intro s hs
    rw [StmtsPre, Structural.run]
    exact ⟨trivial,fun _ ht => Option.some.inj ht ▸ hs⟩
  | assign hf site _ ih =>
    apply goodCons ih
    intro s hs
    refine ⟨by rw [StmtPre]; exact site.sound hs, ?_⟩
    intro t ht
    rw [Structural.step] at ht
    obtain ⟨v,hv,ht⟩ := Option.bind_eq_some_iff.mp ht
    cases ht
    exact hs.setReg _ _ _ _ (hf.finite hs v hv)
  | store r off hw hf site _ ih =>
    apply goodCons ih
    intro s hs
    obtain ⟨he,ho⟩ := site
    refine ⟨by rw [StmtPre]; exact ⟨he.sound hs,ho.sound hs,trivial⟩, ?_⟩
    intro t ht
    rw [Structural.step] at ht
    obtain ⟨v,hv,ht⟩ := Option.bind_eq_some_iff.mp ht
    exact store_preserves hw hs (hf.finite hs v hv) ht
  | loop _ _ ihBody ihTail =>
    apply goodCons ihTail
    intro s hs
    rw [StmtPre, Structural.step]
    exact goodLoop ihBody 0 s hs

theorem Code.preserves {L body} (hc : Code L body) {s t} (hs : Invariant L s)
    (h : Structural.run realAlgebra body s = some t) : Invariant L t := (hc.good s hs).2 t h

theorem Code.stmtsPre {L body s} (hc : Code L body) (hs : Invariant L s) : StmtsPre body s :=
  (hc.good s hs).1

theorem Code.supported {L body} (hc : Code L body) : SupportedStmts body := by
  induction hc with
  | nil => trivial
  | assign hf _ _ ih | store _ _ _ hf _ _ ih =>
    refine ⟨?_, ih⟩
    cases hf <;> simp [SupportedStmt, SupportedExpr, SupportedCompute]
  | loop _ _ ihb iht => exact ⟨ihb,iht⟩

theorem bridgePre {L body s} (inputs outputs) (hc : Code L body) (hs : Invariant L s) :
    BridgePre (.mk inputs outputs body) s := ⟨hc.supported, hc.stmtsPre hs⟩

end FiniteBridge
end VeriTile.Interp
