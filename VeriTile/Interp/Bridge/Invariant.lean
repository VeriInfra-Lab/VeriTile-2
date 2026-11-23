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
  finiteReg : RegName → Prop := fun _ => True

def FiniteValue : (d : TileDType) → Structural.Value (WithBot ℝ) d → Prop
  | .real, v | .fp32, v | .fp16, v | .bf16, v | .f8e4, v | .f8e5, v => ∃ x : ℝ, v = ↑x
  | _, _ => True

structure Invariant (L : Layout) (s : S) : Prop where
  cells : ∀ r d, L.reads r d → ∀ o, ∃ v, s.mem r o = .mk d v ∧ FiniteValue d v
  registers : ∀ d sh n v, L.finiteReg n → s.regs d sh n = some v → ∀ i, FiniteValue d (v i)
  undefined : ∀ r d, L.reads r d → ∀ o, UndefAgrees s d true r o
  bytes : ∀ r, L.bytes r → ∀ o, let b := (s.mem r o).read .int
    Float8E5Bits.isInt8 b = true → (Float8E5Bits.ofInt b).decodeRat.isSome = true

private theorem undef_of_eq {L : Layout} {s t : S} (h : t.undef = s.undef)
    (hu : ∀ r d, L.reads r d → ∀ o, UndefAgrees s d true r o) :
    ∀ r d, L.reads r d → ∀ o, UndefAgrees t d true r o := by
  intro r d hr o
  specialize hu r d hr o
  cases d <;> simpa only [UndefAgrees, BlockState.unspecifiedValue, erase_undef, h] using hu

theorem Invariant.setReg {L s} (hs : Invariant L s) (n d sh v)
    (hv : L.finiteReg n → ∀ i, FiniteValue d (v i)) : Invariant L (s.setReg n d sh v) := by
  refine ⟨hs.cells, ?_, undef_of_eq rfl hs.undefined, hs.bytes⟩
  intro d' sh' n' v' hnReg h i
  by_cases hn : n' = n
  · subst n'
    by_cases hd : d = d'
    · subst d'
      by_cases hh : sh = sh'
      · subst sh'; simp only [Structural.State.setReg_same, Option.some.injEq] at h
        exact h ▸ hv hnReg i
      · simp [Structural.State.setReg, hh] at h
    · simp [Structural.State.setReg, hd] at h
  · exact hs.registers _ _ _ _ hnReg (by simpa [Structural.State.setReg, hn] using h) i

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

private theorem Invariant.readable {L s} (hs : Invariant L s) {r d} (hr : L.reads r d) (o) :
    CellFinite d (s.mem r o) ∧ CellTagged d (s.mem r o) := by
  obtain ⟨v, hc, hv⟩ := hs.cells _ _ hr o
  refine ⟨?_, fun _ => ⟨v,hc⟩⟩
  intro v' hv'
  rw [hc] at hv'
  cases hv'
  cases d <;> first | rfl | (obtain ⟨x,rfl⟩ := hv; rfl)

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
    refine ⟨fun _ _ => ?_, fun _ h _ => by contradiction, fun _ _ _ => hs.undefined _ _ hr _⟩
    exact hs.readable hr (offsets i)

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

private theorem undefReal {L s} (hs : Invariant L s) (r o) (hr : L.reads r .real) :
    FiniteValue .real (s.undef .real r o) := by
  have hu := hs.undefined r .real hr o
  have fl : ¬ (∀ f : FloatDType, f.toTileDType ≠ .real) := fun h => h .real rfl
  exact ⟨(erase s).undef r o, by simpa [UndefAgrees, fl, toCarrier, BlockState.unspecifiedValue] using hu⟩

private theorem finiteRead {L s d} (hs : Invariant L s) (r o) (hr : L.reads r d) :
    FiniteValue d ((s.mem r o).read d) := by
  obtain ⟨x, eq, hf⟩ := hs.cells r d hr o
  simpa [eq] using hf

/-- A conservative syntactic grammar of finite right-hand sides. In particular
there is no constructor for a floating negative infinity. Discrete results
are always finite; their nested operations still have to satisfy the bridge. -/
inductive FiniteOp (L : Layout) : {d : TileDType} → {sh : TileShape} → Op d sh → Prop
  | nat (e : Op .nat sh) : FiniteOp L e
  | literal (c) : FiniteOp L (.const c)
  | reg (d sh n) : L.finiteReg n → FiniteOp L (.ref d sh n)
  | broadcast {e : Op d []} (sh) : FiniteOp L e → FiniteOp L (.broadcast e sh)
  | full {e : Op d []} (sh) : FiniteOp L e → FiniteOp L (.full sh e)
  | bool (e : Op .bool sh) : FiniteOp L e
  | int (e : Op .int sh) : FiniteOp L e
  | sum {e : Op .real sh} (axis keep) : FiniteOp L e → FiniteOp L (.reduceSum axis keep e)
  | select (c : Op .bool sh) {a b : Op d sh} : FiniteOp L a → FiniteOp L b → FiniteOp L (.where c a b)
  | fromNat (e : Op .nat sh) : FiniteOp L (.natToReal e)
  | precision {e : Op .real sh} (p) : FiniteOp L e → FiniteOp L (.withPrecision .real p e)
  | bf16 {e : Op .real sh} : FiniteOp L e → FiniteOp L (.castFloat .real .bf16 e)
  | add (bc : Broadcast a b sh) {x y} : FiniteOp L x → FiniteOp L y → FiniteOp L (.add .real bc x y)
  | sub (bc : Broadcast a b sh) {x y} : FiniteOp L x → FiniteOp L y → FiniteOp L (.sub .real bc x y)
  | mul (bc : Broadcast a b sh) {x y} : FiniteOp L x → FiniteOp L y → FiniteOp L (.mul .real bc x y)
  | div (bc : Broadcast a b sh) {x y} : FiniteOp L x → FiniteOp L y → FiniteOp L (.div .real bc x y)
  | load (r : Region d) (off : Op .nat sh) (pad) : L.reads (Region.cast r) d →
      FiniteOp L (.load d (.region r off) .none pad)
  | masked (r : Region .real) (off : Op .nat sh) (m pad) : L.reads (Region.cast r) .real →
      FiniteOp L (.load .real (.region r off) (.mask m) pad)
  | maskedOther (r : Region d) (off : Op .nat sh) (m pad) {other} : L.reads (Region.cast r) d →
      FiniteOp L other → FiniteOp L (.load d (.region r off) (.maskOther m other) pad)
  | maximum (bc : Broadcast a b sh) {x y} : FiniteOp L x → FiniteOp L y → FiniteOp L (.max2 bc x y)
  | minFloat (bc : Broadcast a b sh) {x y} : FiniteOp L x → FiniteOp L y → FiniteOp L (.minimumFloat .real bc x y)
  | maxFloat (bc : Broadcast a b sh) {x y} : FiniteOp L x → FiniteOp L y → FiniteOp L (.maximumFloat .real bc x y)
  | exp {e : Op .real sh} : FiniteOp L e → FiniteOp L (.exp e)
  | log {e : Op .real sh} : FiniteOp L e → FiniteOp L (.log e)
  | libdeviceExp {e : Op .real sh} : FiniteOp L e → FiniteOp L (.libdeviceExp e)
  | libdeviceLog {e : Op .real sh} : FiniteOp L e → FiniteOp L (.libdeviceLog e)
  | sigmoid {e : Op .real sh} : FiniteOp L e → FiniteOp L (.sigmoid e)
  | sqrt {e : Op .real sh} : FiniteOp L e → FiniteOp L (.sqrt e)
  | reduceMax {e : Op .real sh} (axis keep) : FiniteOp L e → FiniteOp L (.reduceMax axis keep e)
  | cast {e : Op src.toTileDType sh} (dst) : FiniteOp L e → FiniteOp L (.castFloat src dst e)
  | decode (r : Region .int) (off : Op .nat sh) (pad) : L.bytes (Region.cast r) →
      FiniteOp L (.decodeFloat8E5 .real (.load .int (.region r off) .none pad))

private theorem finiteSup {ι} (xs : Finset ι) (hn : xs.Nonempty) (f : ι → WithBot ℝ)
    (hf : ∀ j, FiniteValue .real (f j)) : FiniteValue .real (xs.sup' hn f) := by
  obtain ⟨k, _, eq⟩ := Finset.exists_mem_eq_sup' hn f
  rw [eq]
  exact hf k

theorem FiniteOp.finite {L s} (hs : Invariant L s) {d sh} {e : Op d sh} (he : FiniteOp L e)
    (p v) (h : SE p e s = some v) (i) : FiniteValue d (v i) := by
  induction he generalizing p with
  | nat | bool | int => trivial
  | literal => rw [Structural.evalOp_unfold] at h; cases h; exact ⟨_, rfl⟩
  | reg _ _ _ hn => rw [Structural.evalOp_unfold] at h; exact hs.registers _ _ _ _ hn h _
  | broadcast _ _ ih | full _ _ ih =>
    rw [Structural.evalOp_unfold] at h
    obtain ⟨a, ha, ht⟩ := Option.bind_eq_some_iff.mp h
    cases ht
    exact ih p a ha PUnit.unit
  | sum axis keep _ ih =>
    rw [Structural.evalOp_unfold] at h
    obtain ⟨a, ha, ht⟩ := Option.bind_eq_some_iff.mp h
    cases ht
    choose f hf using ih p a ha
    have he : a = fun j => (f j : WithBot ℝ) := funext hf
    subst a
    cases keep <;> simp [realAlgebra, FiniteValue, ofTile, toTile, toCarrier, ofCarrier,
      Tile.reduceSumDrop, Tile.reduceSumKeep, ← WithBot.coe_sum]
  | select c _ _ iha ihb =>
    rw [Structural.evalOp_unfold] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨vc, _, a, ha, b, hb, ht⟩ := h
    cases ht
    change FiniteValue _ (if vc i then a i else b i)
    split <;> first | exact iha p a ha i | exact ihb p b hb i
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
  | masked r off m pad hr =>
    rw [Structural.evalOp_unfold] at h
    cases ho : SE p off s <;> simp [ho] at h
    cases hm : SE p m s <;> simp [hm] at h
    subst v
    dsimp only
    split <;> first | exact finiteRead hs _ _ hr | exact undefReal hs _ _ hr
  | @maskedOther d sh r off m pad other hr hf ih =>
    rw [Structural.evalOp_unfold] at h
    cases ho : SE p off s <;> simp [ho] at h
    cases hm : SE p m s <;> simp [hm] at h
    cases hb : SE p other s <;> simp [hb] at h
    subst v
    dsimp only
    split <;> first | exact finiteRead hs _ _ hr | exact ih _ _ hb i
  | reduceMax axis keep _ ih =>
    rw [Structural.evalOp_unfold] at h
    obtain ⟨a, ha, ht⟩ := Option.bind_eq_some_iff.mp h
    split at ht
    · rename_i pos
      cases ht
      cases keep <;>
        simp [realAlgebra, Tile.reduceMax, Tile.reduceMaxDrop, Tile.reduceMaxKeep, pos, ofTile, toTile, ofCarrier, toCarrier]
      all_goals
        apply finiteSup
        intro k
        exact ih p a ha _
    · contradiction
  | exp _ ih | log _ ih | libdeviceExp _ ih | libdeviceLog _ ih | sigmoid _ ih | sqrt _ ih =>
    rw [Structural.evalOp_unfold] at h
    obtain ⟨a, ha, ht⟩ := Option.bind_eq_some_iff.mp h
    cases ht
    obtain ⟨x, hx⟩ := ih p a ha i
    simp [FiniteValue, realAlgebra, hx]
  | @cast sh src e dst hf ih =>
    rw [Structural.evalOp_unfold] at h
    obtain ⟨f, ha, ht⟩ := Option.bind_eq_some_iff.mp h
    cases ht
    have hx := ih p f ha i
    cases src <;> cases dst <;> exact hx
  | maximum bc _ _ ihx ihy | minFloat bc _ _ ihx ihy | maxFloat bc _ _ ihx ihy =>
    rw [Structural.evalOp_unfold] at h
    simp only [realAlgebra, bind, Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, ht⟩ := h
    cases ht
    have hx := ihx p a ha (bc.leftIndex i)
    have hy := ihy p b hb (bc.rightIndex i)
    simp only [Structural.bop, Structural.toFloat, Structural.ofFloat, max_def, min_def]
    split <;> assumption
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
  | fp32 {r : Region .real} {off : Op .nat sh} {mask pad} :
      FiniteOp L (.load .real (.region r off) mask pad) →
      FiniteExpr L (.compute (.load .fp32 (.region r off) mask pad))
  | load (r : Region .real) (off : Op .nat sh) (pad) : L.reads (Region.cast r) .real →
      FiniteExpr L (.compute (.load .fp32 (.region r off) .none pad))

theorem FiniteExpr.finite {L s} (hs : Invariant L s) {d sh} {e : ComputeExpr d sh} (he : FiniteExpr L e)
    (v) (h : Structural.evalExpr realAlgebra e s = some v) (i) : FiniteValue d (v i) := by
  cases he with
  | alg he => exact he.finite hs none v h i
  | fp32 he =>
    simp only [Structural.evalExpr, Structural.evalComputeOp, bind, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, ht⟩ := h
    cases ht
    exact he.finite hs (some .fp32) a ha i
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

def CheckedMask (L : Layout) {d sh} : MaskOpt d sh → Prop
  | .none => True
  | .mask m | .maskOther m _ => CheckedNodes L m

private theorem CheckedMask.sound {L s d sh} (hs : Invariant L s) {mask : MaskOpt d sh}
    (h : CheckedMask L mask) : MaskSite s mask := by
  cases mask <;> first | trivial | exact CheckedNodes.sound h hs

/-- A certificate follows the syntax once. Site obligations inspect each
projected expression independently of the path or loop count. The finite-value grammar and write permissions are checked at stores. -/
inductive Code (L : Layout) : List ComputeStmt → Prop
  | nil : Code L []
  | assign {d sh n e tail} : FiniteExpr L e →
      CheckedExpr L e → Code L tail → Code L (.assign d sh n e :: tail)
  | assignUntracked {d sh n e tail} : ¬ L.finiteReg n → SupportedExpr e →
      CheckedExpr L e → Code L tail → Code L (.assign d sh n e :: tail)
  | store {d sh e mask tail} (r : Region d) (off : Op .nat sh) :
      Writable L (Region.cast r) d → FiniteExpr L e →
      (CheckedExpr L e ∧ CheckedNodes L off ∧ CheckedMask L mask) →
      Code L tail → Code L (.store d sh (.region r off) e mask :: tail)
  | atomic {d sh e mask tail} (nd : NumericDType d) (r : Region d) (off : Op .nat sh) :
      L.reads (Region.cast r) d → Writable L (Region.cast r) d → FiniteExpr L e →
      (CheckedExpr L e ∧ CheckedNodes L off ∧ CheckedMask L mask) → Code L tail →
      Code L (.atomicAdd nd sh (.region r off) e mask :: tail)
  | cond {c yes tail} : CheckedNodes L c → Code L yes → Code L tail → Code L (.ifThen c yes :: tail)
  | branches {c yes no tail} : CheckedNodes L c → Code L yes → Code L no → Code L tail →
      Code L (.ifThenElse c yes no :: tail)
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
    obtain ⟨pre, preserved⟩ := hg u (hs.setReg _ _ _ _ (fun _ _ => trivial))
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

private theorem store_preserves {L d sh} {r : Region d} {off : Op .nat sh} {mask}
    (hw : Writable L (Region.cast r) d) {s t : S} (hs : Invariant L s) {v}
    (hv : ∀ i, FiniteValue d (v i))
    (h : Structural.store realAlgebra (.region r off) mask v s = some t) : Invariant L t := by
  have fold (offsets : TileIndex sh → Nat) (active : TileIndex sh → Bool) (lanes : List (TileIndex sh)) :
      ∀ u, Invariant L u → Invariant L (lanes.foldl (fun a i => if active i then
        a.write (Region.cast r) (offsets i) (.mk d (v i)) else a) u) := by
    induction lanes with
    | nil => exact fun _ hu => hu
    | cons i rest ih =>
      intro u hu
      apply ih
      dsimp only
      split <;> first | exact hu.write hw _ _ (hv i) | exact hu
  cases ho : SE none off s <;> simp [Structural.store, ho] at h
  rename_i offsets
  cases mask with
  | none =>
    simp at h
    subst t
    simpa using fold offsets (fun _ => true) _ s hs
  | mask m | maskOther m _ =>
    cases hm : SE none m s <;> simp [hm] at h
    subst t
    exact fold offsets _ _ s hs

private theorem atomicFinite {d} (nd : NumericDType d) (combine)
    (hc : Structural.atomicAddition realAlgebra nd = some combine) {a b}
    (ha : FiniteValue d a) (hb : FiniteValue d b) : FiniteValue d (combine a b) := by
  cases nd <;> simp only [Structural.atomicAddition, realAlgebra, Option.some.injEq] at hc <;> subst combine
  all_goals first | trivial | (obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨_, rfl⟩)

private theorem atomicFold {L d sh} {r : RegionName} (hr : L.reads r d) (hw : Writable L r d)
    (nd : NumericDType d) (combine) (hc : Structural.atomicAddition realAlgebra nd = some combine)
    (offsets : TileIndex sh → Nat) (active : TileIndex sh → Bool) (v : Structural.Values (WithBot ℝ) d sh)
    (hv : ∀ i, FiniteValue d (v i)) (lanes : List (TileIndex sh)) (s : S) (hs : Invariant L s) :
    let step := atomicLane d combine (fun i => (r, offsets i, true)) active v
    AlongFold step (fun t i => active i = true → true = true →
      CellFinite d (t.mem r (offsets i)) ∧ CellTagged d (t.mem r (offsets i))) lanes s ∧
      Invariant L (lanes.foldl step s) := by
  induction lanes generalizing s with
  | nil => exact ⟨trivial,hs⟩
  | cons i rest ih =>
    have next : Invariant L (atomicLane d combine (fun j => (r, offsets j, true)) active v s i) := by
      unfold atomicLane
      split
      · exact hs.write hw _ _ (atomicFinite nd combine hc (finiteRead hs r _ hr) (hv i))
      · exact hs
    obtain ⟨checks, final⟩ := ih _ next
    exact ⟨⟨fun _ _ => hs.readable hr _, checks⟩,final⟩

private theorem atomicReadsRegion {L s d sh} (hs : Invariant L s) (nd : NumericDType d)
    (r : Region d) (off : Op .nat sh) (mask) (hr : L.reads (Region.cast r) d)
    (hw : Writable L (Region.cast r) d) {v} (hv : ∀ i, FiniteValue d (v i)) :
    AtomicReads nd (.region r off) mask v s := by
  intro combine addr active hc ha _
  cases ho : SE none off s <;> simp [laneAddrs, ho] at ha
  subst addr
  exact (atomicFold hr hw nd combine hc _ active v hv _ s hs).1

private theorem atomicPreserves {L s t d sh} (hs : Invariant L s) (nd : NumericDType d)
    (r : Region d) (off : Op .nat sh) (mask) (hr : L.reads (Region.cast r) d)
    (hw : Writable L (Region.cast r) d) {v} (hv : ∀ i, FiniteValue d (v i))
    (h : Structural.atomicAdd realAlgebra nd (.region r off) mask v s = some t) : Invariant L t := by
  cases hc : Structural.atomicAddition realAlgebra nd <;> simp [Structural.atomicAdd, hc] at h
  rename_i combine
  cases ho : SE none off s <;> simp [ho] at h
  rename_i offsets
  cases mask with
  | none =>
    simp at h
    subst t
    simpa [atomicLane] using (atomicFold hr hw nd _ hc offsets (fun _ => true) v hv _ s hs).2
  | mask m | maskOther m _ =>
    cases hm : SE none m s <;> simp [hm] at h
    subst t
    rename_i active
    have eq : atomicLane d combine (fun j => (Region.cast r, offsets j, true)) active v =
        (fun u i => if active i then u.write (Region.cast r) (offsets i)
          (.mk d (combine ((u.mem (Region.cast r) (offsets i)).read d) (v i))) else u) := by
      funext u i
      simp [atomicLane]
    have fin := (atomicFold hr hw nd _ hc offsets active v hv sh.allIndices s hs).2
    rwa [eq] at fin

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
    exact hs.setReg _ _ _ _ (fun _ => hf.finite hs v hv)
  | assignUntracked hn _ site _ tail =>
    apply goodCons tail
    intro s hs
    refine ⟨by rw [StmtPre]; exact site.sound hs, ?_⟩
    intro t ht
    rw [Structural.step] at ht
    obtain ⟨v, _, ht⟩ := Option.bind_eq_some_iff.mp ht
    cases ht
    exact hs.setReg _ _ _ _ (fun h => (hn h).elim)
  | store r off hw hf site _ ih =>
    apply goodCons ih
    intro s hs
    obtain ⟨he,ho,hm⟩ := site
    refine ⟨by rw [StmtPre]; exact ⟨he.sound hs,ho.sound hs,hm.sound hs⟩, ?_⟩
    intro t ht
    rw [Structural.step] at ht
    obtain ⟨v,hv,ht⟩ := Option.bind_eq_some_iff.mp ht
    exact store_preserves hw hs (hf.finite hs v hv) ht
  | atomic nd r off hr hw hf site _ tail =>
    apply goodCons tail
    intro s hs
    obtain ⟨he,ho,hm⟩ := site
    rw [StmtPre]
    refine ⟨⟨he.sound hs, ho.sound hs, hm.sound hs, fun v hv =>
      atomicReadsRegion hs nd r off _ hr hw (hf.finite hs v hv)⟩, ?_⟩
    intro t ht
    rw [Structural.step] at ht
    obtain ⟨v,hv,ht⟩ := Option.bind_eq_some_iff.mp ht
    exact atomicPreserves hs nd r off _ hr hw (hf.finite hs v hv) ht
  | cond site _ _ yes tail =>
    apply goodCons tail
    intro s hs
    rw [StmtPre]
    refine ⟨⟨site.sound hs, fun _ _ _ => (yes s hs).1⟩, ?_⟩
    intro t ht
    rw [Structural.step] at ht
    obtain ⟨vc, _, ht⟩ := Option.bind_eq_some_iff.mp ht
    split at ht
    · exact (yes s hs).2 t ht
    · exact Option.some.inj ht ▸ hs
  | branches site _ _ _ yes no tail =>
    apply goodCons tail
    intro s hs
    rw [StmtPre]
    refine ⟨⟨site.sound hs, fun c _ => ?_⟩, ?_⟩
    · split <;> first | exact (yes s hs).1 | exact (no s hs).1
    · intro t ht
      rw [Structural.step] at ht
      obtain ⟨vc, _, ht⟩ := Option.bind_eq_some_iff.mp ht
      split at ht <;> first | exact (yes s hs).2 t ht | exact (no s hs).2 t ht
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
  | assign hf _ _ ih | store _ _ _ hf _ _ ih | atomic _ _ _ _ _ hf _ _ ih =>
    refine ⟨?_, ih⟩
    cases hf <;> simp [SupportedStmt, SupportedExpr, SupportedCompute]
  | assignUntracked _ supported _ _ iht => exact ⟨supported,iht⟩
  | cond _ _ _ ihb iht => exact ⟨ihb,iht⟩
  | branches _ _ _ _ ihy ihn iht => exact ⟨⟨ihy,ihn⟩,iht⟩
  | loop _ _ ihb iht => exact ⟨ihb,iht⟩

theorem bridgePre {L body s} (inputs outputs) (hc : Code L body) (hs : Invariant L s) :
    BridgePre (.mk inputs outputs body) s := ⟨hc.supported, hc.stmtsPre hs⟩

end FiniteBridge
end VeriTile.Interp
