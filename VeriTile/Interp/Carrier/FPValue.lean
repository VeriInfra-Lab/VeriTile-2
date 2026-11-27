import VeriTile.Interp.Exec
import VeriTile.Triton.Float.ScalarBackend

/-! Computable extension of the format-indexed scalar backend. The caller
supplies the remainder of the algebra, as for `FP.Software.scalarFP32`.
It owns mandatory operations outside the selected format, including
transcendentals and reductions. No default result for those fields is inferred.
Same-format casts and fp32 loads preserve every bit, including NaN payloads.
A bf16 backend requires explicit bf16 operations; an erased fp32 compute
expression remains fp32. Typed bf16 FMA rounds the exact product plus addend
once to bf16. Hardware that computes an fp32 FMA and then converts to bf16
rounds twice and can give a different result. -/
namespace VeriTile.Interp.FPValue
open VeriTile.Triton VeriTile.Triton.FP

private def accepts (f : Format) (p : Option ComputeDType) (d : FloatDType) : Bool :=
  match f with
  | .fp32 => Software.fp32Context p d
  | .bf16 => p.isNone && d == .bf16

private def storage : Format → FloatDType
  | .fp32 => .fp32
  | .bf16 => .bf16

-- The same scalar operations serve raw bit patterns and the checked runner's
-- optional words. An unavailable word has no IEEE bit pattern, including NaN.
private def operations {α : Type} (f : Format) (pack : FP.Value f → α)
    (unpack : α → Option (FP.Value f)) (rest : CAlgebra α) (cfg : Config) : CAlgebra α :=
  let unary (g : FP.Value f → FP.Value f) (otherwise : α → α) (x : α) :=
    match unpack x with | some a => pack (g a) | none => otherwise x
  let binary (g : FP.Value f → FP.Value f → FP.Value f) (otherwise : α → α → α) (x y : α) :=
    match unpack x, unpack y with | some a, some b => pack (g a b) | _, _ => otherwise x y
  let fused (x y z : α) := match unpack x, unpack y, unpack z with
    | some a, some b, some c => pack (FP.fma cfg a b c)
    | none, _, _ => x | _, none, _ => y | _, _, none => z
  let cmp (g : FP.Value f → FP.Value f → Bool) (x y : α) :=
    match unpack x, unpack y with | some a, some b => g a b | _, _ => false
  { rest with
    literal := fun p d q => if accepts f p d then pack (FP.round f cfg q) else rest.literal p d q
    negInf := pack (FP.Value.infinity f true)
    binary := fun p d op x y =>
      let otherwise := rest.binary p d op
      if accepts f p d then
        match op with
        | .add => binary (FP.add cfg) otherwise x y | .sub => binary (FP.sub cfg) otherwise x y
        | .mul => binary (FP.mul cfg) otherwise x y | .div => binary (FP.div cfg) otherwise x y
        | _ => otherwise x y
      else otherwise x y
    fma := fun p => if f == .fp32 && p == .fp32 then some fused else rest.fma p
    fmaTyped := fun d => if d == storage f then some fused else rest.fmaTyped d
    unary := fun p op x =>
      match op with
      | .neg d => if accepts f p d then unary FP.Value.neg (rest.unary p op) x else rest.unary p op x
      | .abs d => if accepts f p d then unary FP.Value.abs (rest.unary p op) x else rest.unary p op x
      | _ => rest.unary p op x
    cast := fun p src dst x =>
      if src == dst && (src == storage f || accepts f p src) then x else rest.cast p src dst x
    compareEq := fun p d => if accepts f p d then some (cmp (FP.eq cfg)) else rest.compareEq p d
    compareLt := fun p d => if accepts f p d then some (cmp (FP.lt cfg)) else rest.compareLt p d
    compareLe := fun p d => if accepts f p d then some (cmp (fun x y => FP.lt cfg x y || FP.eq cfg x y))
      else rest.compareLe p d
    fromNat := fun p n => if accepts f p .real then pack (FP.round f cfg n) else rest.fromNat p n
    fromInt := fun p i => if accepts f p .real then pack (FP.round f cfg i) else rest.fromInt p i
    fp32Bits := fun b => if h : f = .fp32 then pack (h ▸ (⟨b.bits⟩ : FP.Value .fp32)) else rest.fp32Bits b
    fp32Load := fun x => if f == .fp32 then x else rest.fp32Load x }

/-- Extend an existing bit algebra on the admitted format, just as
`Software.scalarFP32` extends a structural backend. -/
def algebra (f : Format) (rest : CAlgebra (FP.Value f)) (cfg : Config := .ieeeValue) :
    CAlgebra (FP.Value f) := operations f id some rest cfg

private def unavailable (f : Format) : CAlgebra (Option (FP.Value f)) where
  literal := fun _ _ _ => none
  negInf := none
  binary := fun _ _ _ _ _ => none
  unary := fun _ _ _ => none
  cast := fun _ _ _ _ => none
  fromNat := fun _ _ => none
  fromInt := fun _ _ => none
  fp32Bits := fun _ => none
  fp32Load := fun _ => none
  reduceMax := fun _ {_} _ _ _ _ => none
  reduceSum := fun _ {_} _ _ _ _ => none

/-- On optional words each missing total arithmetic operation returns no word.
Use `run` for fragment selection before comparisons or control flow. -/
def partialAlgebra (f : Format) (cfg : Config := .ieeeValue) : CAlgebra (Option (FP.Value f)) :=
  operations f some id (unavailable f) cfg

private def dtype (f : Format) (p : Option ComputeDType) : TileDType → Bool
  | .real => accepts f p .real
  | .fp32 => accepts f p .fp32
  | .bf16 => accepts f p .bf16
  | .nat | .int | .bool => true
  | _ => false

mutual
private def opOK (f : Format) (p : Option ComputeDType) : {d : TileDType} → {sh : TileShape} → QOp d sh → Bool
  | _, _, .const _ => accepts f p .real
  | _, _, .constFloat d _ => accepts f p d
  | _, _, .constNat _ | _, _, .constInt _ | _, _, .constBool _
  | _, _, .programId _ | _, _, .numPrograms _ | _, _, .arange _ => true
  | d, _, .ref .. => dtype f p d
  | _, _, .negInf => accepts f p .real
  | _, _, .broadcast a _ | _, _, .full _ a | _, _, .boolNot a => opOK f p a
  | _, _, .withPrecision _ .fp32 a => f == .fp32 && opOK f (some .fp32) a
  | _, _, .castFloat src dst a => src == dst && (src == storage f || accepts f p src) && opOK f p a
  | _, _, .negFloat d a | _, _, .absFloat d a => accepts f p d && opOK f p a
  | d, _, .add _ _ a b | d, _, .sub _ _ a b | d, _, .mul _ _ a b | d, _, .div _ _ a b =>
    dtype f p d && opOK f p a && opOK f p b
  | _, _, @QOp.lt d _ _ _ _ _ a b | _, _, @QOp.le d _ _ _ _ _ a b
  | _, _, @QOp.gt d _ _ _ _ _ a b | _, _, @QOp.ge d _ _ _ _ _ a b
  | _, _, @QOp.eq d _ _ _ _ _ a b | _, _, @QOp.ne d _ _ _ _ _ a b =>
    dtype f p d && opOK f p a && opOK f p b
  | _, _, .boolAnd _ a b | _, _, .boolOr _ a b => opOK f p a && opOK f p b
  | _, _, .where c a b => opOK f p c && opOK f p a && opOK f p b
  | _, _, .natToReal a | _, _, .intToReal a => accepts f p .real && opOK f p a
  | d, _, .load _ (.region _ off) m _ => dtype f p d && opOK f p off && maskOK f p m
  | _, _, _ => false

private def maskOK (f : Format) (p : Option ComputeDType) : {d : TileDType} → {sh : TileShape} → QMaskOpt d sh → Bool
  | _, _, .none => true
  | _, _, .mask a => opOK f p a
  | _, _, .maskOther a b => opOK f p a && opOK f p b
end

private def computeOK (f : Format) : {d : ComputeDType} → {sh : TileShape} → QComputeOp d sh → Bool
  | _, _, .alg d a => d != .fp64 && opOK f (some d) a
  | .fp32, _, .const _ => f == .fp32
  | .int32, _, .const _ | .uint32, _, .const _ => true
  | _, _, .full _ a => computeOK f a
  | _, _, .load d (.region _ off) m _ => d != .fp64 && (d != .fp32 || f == .fp32) &&
      opOK f (some d) off && maskOK f (some d) m
  | _, _, _ => false

private def exprOK (f : Format) : {d : TileDType} → {sh : TileShape} → QExpr d sh → Bool
  | _, _, .alg a => opOK f none a
  | _, _, .compute a => computeOK f a
  | _, _, .fma .fp32 _ _ a b c => f == .fp32 && exprOK f a && exprOK f b && exprOK f c
  | _, _, .fmaTyped d _ _ a b c => d == storage f && exprOK f a && exprOK f b && exprOK f c
  | _, _, _ => false

mutual
private def stmtOK (f : Format) : QStmt → Bool
  | .alg (.assign _ _ _ a) => opOK f none a
  | .alg (.store _ _ (.region _ off) a m) => opOK f none off && opOK f none a && maskOK f none m
  | .assign _ _ _ a => exprOK f a
  | .store _ _ (.region _ off) a m => opOK f none off && exprOK f a && maskOK f none m
  | .forLoop _ _ b | .forRange _ _ _ _ b => bodyOK f b
  | .forRangeDyn _ lo hi step b | .forRangeInt _ lo hi step b =>
    opOK f none lo && opOK f none hi && opOK f none step && bodyOK f b
  | .ifThen c b => opOK f none c && bodyOK f b
  | .ifThenElse c a b => opOK f none c && bodyOK f a && bodyOK f b
  | _ => false

private def bodyOK (f : Format) : List QStmt → Bool
  | [] => true
  | a :: tail => stmtOK f a && bodyOK f tail
end

/-- The checked interpreter admits arithmetic and control flow at the selected
format. A rejected operation in any branch is detected before execution. -/
def admits (f : Format) : QKernel → Bool
  | .mk _ _ b => bodyOK f b

private def word {f} : (d : TileDType) → Structural.Value (FP.Value f) d → Structural.Value (Option (FP.Value f)) d
  | .real, a | .fp32, a | .fp16, a | .bf16, a | .f8e4, a | .f8e5, a => some a
  | .nat, a | .int, a | .bool, a | .ptr, a | .blockPtr, a => a

private def wordCell {f} : Structural.Cell (FP.Value f) → Structural.Cell (Option (FP.Value f))
  | .mk d v => .mk d (word d v)

private def checkedWord {f} : (d : TileDType) → Structural.Value (Option (FP.Value f)) d →
    Option (Structural.Value (FP.Value f) d)
  | .real, a | .fp32, a | .fp16, a | .bf16, a | .f8e4, a | .f8e5, a => a
  | .nat, a | .int, a | .bool, a | .ptr, a | .blockPtr, a => some a

/-- Execute a program on actual bit patterns. The returned sparse state can
be passed to the next program. Every changed cell and register lane has an
encoding; a missing word is never exported as NaN or as zero. -/
def run (f : Format) (cfg : Config) (k : QKernel) (s : State (FP.Value f)) :
    Option (State (FP.Value f)) := do
  guard (admits f k)
  -- Structural reads of a differently tagged cell use the carrier default.
  let t ← @interp _ ⟨some (FP.Value.zero f)⟩ (partialAlgebra f cfg) k {
    init := fun r o => wordCell (s.init r o)
    cells := s.cells.map (fun _ cell => wordCell cell)
    regs := s.regs.map fun _ reg => ⟨reg.dtype, reg.shape, fun i => word reg.dtype (reg.values i)⟩
    pids := s.pids, numPids := s.numPids
    undef := fun d r o => word d (s.undef d r o) }
  let cells ← t.cells.toList.mapM fun (addr, .mk d v) => do
    return (addr, Structural.Cell.mk d (← checkedWord d v))
  let regs ← t.regs.toList.mapM fun (n, r) => do
    let v ← collectValues? fun i => checkedWord r.dtype (r.values i)
    return (n, Reg.mk r.dtype r.shape v)
  return { s with cells := .ofList cells, regs := .ofList regs }

end VeriTile.Interp.FPValue
