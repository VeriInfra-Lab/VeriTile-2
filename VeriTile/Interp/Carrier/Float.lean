import Batteries.Data.Rat.Float
import VeriTile.Interp.Algebra
import VeriTile.Interp.Run.Grid
import VeriTile.Triton.Float.BitValue

namespace VeriTile.Interp.Binary64
open VeriTile.Triton FP

-- Lean exposes exp and log via libm. Correct for the rounding of exp x or 1+x
-- near the origin without routing interpreted kernels through a native plugin.
private def expm1 (x : Float) : Float :=
  let u := x.exp
  if u == 1 then x else if x.abs < 0.5 then (u - 1) * (x / u.log) else u - 1

private def log1p (x : Float) : Float :=
  let u := 1 + x
  if u == 1 then x else if x.abs < 0.5 then u.log * (x / (u - 1)) else u.log

-- Positive-term expansion of exp(x²) * erf(x). At |x| >= 6 the omitted
-- tail of erf is below half a binary64 ulp at 1.
private def erf (x : Float) : Float := Id.run do
  if x.isNaN || x == 0 then return x
  if x.abs >= 6 then return if x < 0 then -1 else 1
  let xx := x * x
  let mut term := x
  let mut total := x
  for n in [1:160] do
    term := term * (2 * xx / (2 * n + 1).toFloat)
    let next := total + term
    if next == total then break
    total := next
  let result := ((2 / Float.sqrt (Float.acos (-1))) * (-xx).exp) * total
  return max (-1) (min 1 result)

private def unary (op : Structural.Unary) (x : Float) : Float :=
  match op with
  | .neg _ => -x | .abs _ => x.abs
  | .exp | .libdeviceExp => x.exp | .exp2 => x.exp2
  | .log | .libdeviceLog => x.log | .log2 => x.log2
  | .sqrt => x.sqrt | .rsqrt | .libdeviceRsqrt => 1 / x.sqrt
  | .sigmoid =>
    if x >= 0 then 1 / (1 + (-x).exp) else let e := x.exp; e / (1 + e)
  | .tanh | .libdeviceTanh => x.tanh | .sinh => x.sinh | .cosh => x.cosh
  | .sin => x.sin | .cos => x.cos | .tan => x.tan | .atan => x.atan
  | .erf => erf x | .libdeviceLog1p => log1p x | .libdeviceExpm1 => expm1 x
  | .minPosInf => min x Float.inf

-- Subnormals round on a fixed grid. Rounding a significand first and then
-- scaling it into this range can round twice near a half-ulp boundary.
private def roundRat (q : ℚ) : Float := Id.run do
  let mag := q.num.natAbs
  if mag <<< 1022 ≥ q.den then return q.toFloat
  let scaled := mag <<< 1074
  let leading := scaled / q.den
  let twiceRem := 2 * (scaled % q.den)
  let bits := if twiceRem > q.den || (twiceRem == q.den && leading % 2 == 1) then leading + 1 else leading
  return Float.ofBits ((if q.num < 0 then (1 : UInt64) <<< 63 else 0) ||| bits.toUInt64)

private def fused (x y z : Float) : Float :=
  if !x.isFinite || !y.isFinite || x == 0 || y == 0 then x * y + z
  else if !z.isFinite then z
  else roundRat (x.toRat0 * y.toRat0 + z.toRat0)

private def reduce {shape : TileShape} (f : Float → Float → Float) (seed : Float)
    (axis : Fin shape.length) (keep : Bool) (values : TileIndex shape → Float) :
    TileIndex (TileShape.reduceShape shape axis keep) → Float :=
  match keep with
  | false => fun i => (List.finRange _).foldl (fun v k => f v (values (TileShape.insertAxisIndex shape axis i k))) seed
  | true => fun i => (List.finRange _).foldl (fun v k => f v (values (TileShape.replaceAxisIndex shape axis i k))) seed

private def dot {m k n : Nat} : (batch : TileShape) →
    (TileIndex (batch ++ [m,k]) → Float) → (TileIndex (batch ++ [k,n]) → Float) →
    (TileIndex (batch ++ [m,n]) → Float) → TileIndex (batch ++ [m,n]) → Float
  | [], a, b, acc, (row,col,_) =>
    (List.finRange k).foldl (fun v j => v + a (row,j,()) * b (j,col,())) (acc (row,col,()))
  | _ :: tail, a, b, acc, (h,i) =>
    dot tail (fun j => a (h,j)) (fun j => b (h,j)) (fun j => acc (h,j)) i

private def ieeeDot (o : DotOptions) : Bool :=
  (o.inputPrecision.isNone || o.inputPrecision == some "ieee") &&
  o.allowTF32 != some true && o.maxNumImpreciseAcc.isNone && o.outDType.isNone

/-- Host binary64 approximation. All floating channels use the same precision.
Reductions accumulate in ascending lane order. Optional operations outside
this carrier's fragment retain their failing CAlgebra defaults. -/
def algebra : CAlgebra Float where
  literal := fun _ _ => roundRat
  negInf := -Float.inf
  binary := fun _ _ op x y => match op with
    | .add => x + y | .sub => x - y | .mul => x * y | .div => x / y | .max => max x y | .pow => x ^ y
  unary := fun _ => unary
  cast := fun _ _ _ => id
  fp32Load := id
  fromNat := fun _ n => n.toFloat
  fromInt := fun _ => Float.ofInt
  fp32Bits := fun b => (Float32.ofBits b.bits.toNat.toUInt32).toFloat
  isFinite := fun _ => some Float.isFinite
  compareLt := fun _ _ => some fun x y => decide (x < y)
  compareLe := fun _ _ => some fun x y => decide (x ≤ y)
  compareEq := fun _ _ => some (· == ·)
  fma := fun _ => some fused
  fmaTyped := fun _ => some fused
  atomicAdd := fun _ => some (· + ·)
  minimum := fun _ _ => some min
  divRN := some (· / ·)
  reduceMin := fun _ _ axis keep xs => some (reduce min Float.inf axis keep xs)
  reduceMax := fun _ _ => reduce max (-Float.inf)
  reduceSum := fun _ _ => reduce (· + ·) 0
  reduceSumTyped := fun _ d _ axis keep xs => some fun i =>
    Structural.ofFloat d (reduce (· + ·) 0 axis keep (fun j => Structural.toFloat d (xs j)) i)
  reduceMaxTyped := fun _ d _ axis keep xs => some fun i =>
    Structural.ofFloat d (reduce max (-Float.inf) axis keep (fun j => Structural.toFloat d (xs j)) i)
  dot := fun _ {batch} {_} {_} {_} a b => some (dot batch a b (fun _ => 0))
  dotWithOptions := fun _ o {batch} {_} {_} {_} a b =>
    if ieeeDot o then some (dot batch a b (fun _ => 0)) else none
  dotTyped := fun _ l r out o {batch} {_} {_} {_} a b => do
    guard (ieeeDot o)
    return fun i => Structural.ofFloat out (dot batch (fun j => Structural.toFloat l (a j))
      (fun j => Structural.toFloat r (b j)) (fun _ => 0) i)
  dotAcc := fun _ l r out o {batch} {_} {_} {_} a b acc => do
    guard (ieeeDot o)
    return fun i => Structural.ofFloat out (dot batch (fun j => Structural.toFloat l (a j))
      (fun j => Structural.toFloat r (b j)) (fun j => Structural.toFloat out (acc j)) i)

/-- Direct BF16 encoding of a host value, including the sign of zero. -/
def bf16Bits (x : Float) : Nat :=
  if x.isNaN then (FP.Value.qNaN .bf16).raw
  else if x.isInf then (FP.Value.infinity .bf16 (x < 0)).raw
  else (FP.round .bf16 .ieeeValue x.toRat0 (x.toBits == 0x8000000000000000)).raw

private def sourceFormat (p : Option ComputeDType) : FloatDType → Option FP.Format
  | .bf16 => some .bf16
  | .fp32 => some .fp32
  | .real => if p == some .fp32 then some .fp32 else none
  | _ => none

private def encodedFloat (f : FP.Format) (bits : Nat) : Float :=
  (Float32.ofBits (if f == .bf16 then (bits <<< 16).toUInt32 else bits.toUInt32)).toFloat

private def roundSource (p : Option ComputeDType) (d : FloatDType) (x : Float) : Float :=
  match sourceFormat p d with
  | some .fp32 => x.toFloat32.toFloat
  | some .bf16 => encodedFloat .bf16 (bf16Bits x)
  | none => x

private def sourceLiteral (p : Option ComputeDType) (d : FloatDType) (q : ℚ) : Float :=
  match sourceFormat p d with
  | some f => encodedFloat f (FP.round f .ieeeValue q).raw
  | none => roundRat q

private def sourceBinary (p : Option ComputeDType) (d : FloatDType)
    (op : Structural.Binary) (x y : Float) : Float :=
  if sourceFormat p d == some .fp32 then
    let a := x.toFloat32
    let b := y.toFloat32
    match op with
    | .add => (a + b).toFloat | .sub => (a - b).toFloat
    | .mul => (a * b).toFloat | .div => (a / b).toFloat
    | .max => (max a b).toFloat
    | .pow => roundSource p d (x ^ y)
  else roundSource p d (algebra.binary p d op x y)

private def unaryDType : Structural.Unary → FloatDType
  | .neg d | .abs d => d
  | _ => .real

/-- CPU reference for the source-rounded FP32/FP64 scalar, reduction and BF16
cast fragment. The host transcendental functions are evaluated in binary64
and rounded at the source precision; reductions accumulate in lane order.
This is not a GPU/libdevice bit-equivalence claim. The original `algebra`
remains the binary64 approximation for existing registrations. -/
private def sourceRoundedAlgebra : CAlgebra Float where
  literal := sourceLiteral
  negInf := -Float.inf
  binary := sourceBinary
  unary := fun p op x => roundSource p (unaryDType op) (unary op x)
  cast := fun p _ dst => roundSource p dst
  fromNat := fun p n => sourceLiteral p .real n
  fromInt := fun p i => sourceLiteral p .real i
  fp32Bits := algebra.fp32Bits
  fp32Load := fun x => x.toFloat32.toFloat
  compareLt := algebra.compareLt
  compareLe := algebra.compareLe
  compareEq := algebra.compareEq
  reduceMax := fun p _ => reduce (sourceBinary p .real .max) (-Float.inf)
  reduceSum := fun p _ => reduce (sourceBinary p .real .add) 0
  reduceSumTyped := fun p d _ axis keep xs => some fun i =>
    Structural.ofFloat d (reduce (sourceBinary p d .add) 0 axis keep (fun j => Structural.toFloat d (xs j)) i)
  reduceMaxTyped := fun p d _ axis keep xs => some fun i =>
    Structural.ofFloat d (reduce (sourceBinary p d .max) (-Float.inf) axis keep (fun j => Structural.toFloat d (xs j)) i)

-- `CAlgebra` has total scalar fields, so admission must precede execution.
-- The private algebra is only exposed through the checked grid entry below.
private def hasPrecision (p : Option ComputeDType) : Bool :=
  p == some .fp32 || p == some .fp64

private def arithmeticOK (p : Option ComputeDType) : FloatDType → Bool
  | .real => hasPrecision p
  | .fp32 => true
  | _ => false

private def storageOK : FloatDType → Bool
  | .real | .fp32 | .bf16 => true
  | _ => false

private def arithmeticTileOK (p : Option ComputeDType) : TileDType → Bool
  | .real => hasPrecision p
  | .fp32 | .nat | .int => true
  | _ => false

private def transportOK : TileDType → Bool
  | .real | .fp32 | .bf16 | .nat | .int | .bool => true
  | _ => false

-- The reflected Boolean guards of LogExp/LSE erase their FP32 context for
-- comparisons. Only precision-independent, exact operands are permitted
-- there: already represented values, exact constants, and absolute value.
-- This does not permit an untyped rounded operation in a numeric expression.
private def exactGuardLiteral (q : ℚ) : Bool :=
  (FP.round .fp32 .ieeeValue q).toRat? == some q

mutual
private def opOK (p : Option ComputeDType) : {d : TileDType} → {sh : TileShape} → QOp d sh → Bool
  | _, _, .const _ => hasPrecision p
  | _, _, .constFloat d _ => arithmeticOK p d || d == .bf16
  | _, _, .constNat _ | _, _, .constInt _ | _, _, .constBool _
  | _, _, .programId _ | _, _, .numPrograms _ | _, _, .arange _ => true
  | d, _, .ref .. => transportOK d
  | _, _, .negInf => hasPrecision p
  | _, _, .broadcast a _ | _, _, .full _ a | _, _, .boolNot a => opOK p a
  | _, _, .withPrecision d .fp32 a => storageOK d && opOK (some .fp32) a
  | _, _, .withPrecision d .fp64 a => storageOK d && opOK (some .fp64) a
  | _, _, .castFloat src dst a => storageOK src &&
      (arithmeticOK p dst || dst == .bf16) && opOK p a
  | _, _, .negFloat d a | _, _, .absFloat d a => arithmeticOK p d && opOK p a
  | d, _, .add _ _ a b | d, _, .sub _ _ a b | d, _, .mul _ _ a b | d, _, .div _ _ a b =>
      arithmeticTileOK p d && opOK p a && opOK p b
  | _, _, .exp a | _, _, .libdeviceExp a | _, _, .libdeviceLog a
  | _, _, .libdeviceExpm1 a | _, _, .libdeviceLog1p a | _, _, .libdeviceTanh a
  | _, _, .exp2 a | _, _, .log a | _, _, .log2 a | _, _, .sigmoid a
  | _, _, .sqrt a | _, _, .rsqrt a | _, _, .libdeviceRsqrt a | _, _, .tanh a
  | _, _, .sin a | _, _, .cos a | _, _, .tan a | _, _, .atan a
  | _, _, .cosh a | _, _, .sinh a | _, _, .erf a | _, _, .minPosInf a =>
      hasPrecision p && opOK p a
  | _, _, .pow _ a b | _, _, .max2 _ a b => hasPrecision p && opOK p a && opOK p b
  | _, _, .maximumFloat d _ a b => arithmeticOK p d && opOK p a && opOK p b
  | _, _, @QOp.lt .real _ _ _ _ _ a b | _, _, @QOp.le .real _ _ _ _ _ a b
  | _, _, @QOp.gt .real _ _ _ _ _ a b | _, _, @QOp.ge .real _ _ _ _ _ a b
  | _, _, @QOp.eq .real _ _ _ _ _ a b | _, _, @QOp.ne .real _ _ _ _ _ a b =>
      if p.isNone then exactGuardOK a && exactGuardOK b else hasPrecision p && opOK p a && opOK p b
  | _, _, @QOp.lt d _ _ _ _ _ a b | _, _, @QOp.le d _ _ _ _ _ a b
  | _, _, @QOp.gt d _ _ _ _ _ a b | _, _, @QOp.ge d _ _ _ _ _ a b
  | _, _, @QOp.eq d _ _ _ _ _ a b | _, _, @QOp.ne d _ _ _ _ _ a b =>
      transportOK d && opOK p a && opOK p b
  | _, _, .boolAnd _ a b | _, _, .boolOr _ a b => opOK p a && opOK p b
  | _, _, .where c a b | _, _, .ite c a b => opOK p c && opOK p a && opOK p b
  | _, _, .natToReal a | _, _, .intToReal a => hasPrecision p && opOK p a
  | _, _, .castNatToInt a | _, _, .castIntToNat a => opOK p a
  | _, _, .reduceSum _ _ a | _, _, .reduceMax _ _ a => hasPrecision p && opOK p a
  | _, _, .reduceSumTyped d _ _ a | _, _, .reduceMaxTyped d _ _ a => arithmeticOK p d && opOK p a
  | d, _, .load _ (.region _ off) m _ =>
      arithmeticTileOK p d && opOK p off && maskOK p m
  | _, _, _ => false

private def exactGuardOK : {d : TileDType} → {sh : TileShape} → QOp d sh → Bool
  | d, _, .ref .. => d == .real
  | _, _, .const q => exactGuardLiteral q
  | _, _, .broadcast a _ | _, _, .full _ a => exactGuardOK a
  | _, _, .absFloat d a => d == .real && exactGuardOK a
  | _, _, .withPrecision d .fp32 a => d == .real && opOK (some .fp32) a
  | _, _, .withPrecision d .fp64 a => d == .real && opOK (some .fp64) a
  | _, _, _ => false

private def maskOK (p : Option ComputeDType) : {d : TileDType} → {sh : TileShape} → QMaskOpt d sh → Bool
  | _, _, .none => true
  | _, _, .mask a => opOK p a
  | _, _, .maskOther a b => opOK p a && opOK p b
end

private def computeOK : {d : ComputeDType} → {sh : TileShape} → QComputeOp d sh → Bool
  | _, _, .alg d a => opOK (some d) a
  | .fp32, _, .const _ | .int32, _, .const _ | .uint32, _, .const _ => true
  | _, _, .full _ a => computeOK a
  | _, _, .load d (.region _ off) m _ => d != .fp64 && opOK (some d) off && maskOK (some d) m
  | _, _, _ => false

private def exprOK : {d : TileDType} → {sh : TileShape} → QExpr d sh → Bool
  | _, _, .alg a => opOK none a
  | _, _, .compute a => computeOK a
  | _, _, _ => false

mutual
private def stmtOK : QStmt → Bool
  | .alg (.assign d _ _ a) => transportOK d && opOK none a
  | .alg (.store d _ (.region _ off) a m) => transportOK d && opOK none off && opOK none a && maskOK none m
  | .assign d _ _ a => transportOK d && exprOK a
  | .store d _ (.region _ off) a m => transportOK d && opOK none off && exprOK a && maskOK none m
  | .forLoop _ _ b | .forRange _ _ _ _ b => bodyOK b
  | .forRangeDyn _ lo hi step b | .forRangeInt _ lo hi step b =>
      opOK none lo && opOK none hi && opOK none step && bodyOK b
  | .ifThen c b => opOK none c && bodyOK b
  | .ifThenElse c a b => opOK none c && bodyOK a && bodyOK b
  | _ => false

private def bodyOK : List QStmt → Bool
  | [] => true
  | a :: tail => stmtOK a && bodyOK tail
end

/-- Check every statement, including both branches and inactive lanes, before
the specialized registration enters the source-rounded carrier. -/
def sourceRoundedAdmits : QKernel → Bool
  | .mk _ _ body => bodyOK body

def runSourceRoundedGrid (k : QKernel) (dims : List Nat) (initial : State Float) : Except String (State Float) := do
  unless sourceRoundedAdmits k do throw "kernel outside source-rounded precision/operation fragment"
  let some result := Run.runGrid sourceRoundedAlgebra k dims initial | throw "kernel execution failed"
  return result

#guard sourceRoundedAlgebra.binary (some .fp32) .real .add 1 (1 / 16777216) == 1
#guard sourceRoundedAlgebra.binary (some .fp64) .real .add 1 (1 / 16777216) > 1
#guard sourceRoundedAlgebra.cast (some .fp32) .real .real (1 + 1 / 16777216) == 1
#guard sourceRoundedAlgebra.reduceSum (some .fp32) (shape := [2]) ⟨0, by decide⟩ false
  (fun i => if i.1.val == 0 then 1 else 1 / 16777216) PUnit.unit == 1
#guard sourceRoundedAlgebra.reduceSum (some .fp64) (shape := [2]) ⟨0, by decide⟩ false
  (fun i => if i.1.val == 0 then 1 else 1 / 16777216) PUnit.unit > 1
#guard sourceRoundedAlgebra.cast none .real .bf16 1.00390625 == 1
#guard sourceRoundedAlgebra.cast none .real .bf16 (1.00390625 + 1 / 1073741824) == 1.0078125

-- A three-lane accumulation distinguishes the ascending fold from its reverse.
#guard sourceRoundedAlgebra.reduceSum (some .fp32) (shape := [3]) ⟨0, by decide⟩ false
  (fun i => if i.1.val == 0 then 1 else 1 / 16777216) PUnit.unit == 1
#guard sourceRoundedAlgebra.reduceSum (some .fp32) (shape := [3]) ⟨0, by decide⟩ false
  (fun i => if i.1.val == 2 then 1 else 1 / 16777216) PUnit.unit == 1 + 1 / 8388608

-- Pin the typed path independently of the untyped reduction and its guards.
private def typedSumProbe (oneLane : Nat) : Option Float :=
  (sourceRoundedAlgebra.reduceSumTyped (some .fp32) .fp32 (shape := [3]) ⟨0, by decide⟩ false
    (fun i => Structural.ofFloat .fp32 (if i.1.val == oneLane then 1 else 1 / 16777216 : Float))).map
    (fun values => Structural.toFloat .fp32 (values PUnit.unit))

#guard typedSumProbe 0 == some 1
#guard typedSumProbe 2 == some (1 + 1 / 8388608)

-- Unsupported optional operations must not inherit the binary64 methods.
#guard (sourceRoundedAlgebra.fma .fp32).isNone
#guard (sourceRoundedAlgebra.fmaTyped .fp32).isNone
#guard (sourceRoundedAlgebra.atomicAdd .fp32).isNone
#guard sourceRoundedAlgebra.divRN.isNone
#guard (sourceRoundedAlgebra.isFinite .fp32).isNone
#guard (sourceRoundedAlgebra.minimum (some .fp32) .real).isNone
#guard (sourceRoundedAlgebra.reduceMin (some .fp32) (shape := [1]) ⟨0, by decide⟩ false
  (fun _ => 1)).isNone
#guard (sourceRoundedAlgebra.dot (some .fp32) (batch := []) (m := 1) (k := 1) (n := 1)
  (fun _ => 1) (fun _ => 1)).isNone
#guard (sourceRoundedAlgebra.dotWithOptions (some .fp32) {} (batch := []) (m := 1) (k := 1) (n := 1)
  (fun _ => 1) (fun _ => 1)).isNone
#guard (sourceRoundedAlgebra.dotTyped (some .fp32) .fp32 .fp32 .fp32 {}
  (batch := []) (m := 1) (k := 1) (n := 1)
  (fun _ => Structural.ofFloat .fp32 (1 : Float)) (fun _ => Structural.ofFloat .fp32 (1 : Float))).isNone
#guard (sourceRoundedAlgebra.dotAcc (some .fp32) .fp32 .fp32 .fp32 {}
  (batch := []) (m := 1) (k := 1) (n := 1)
  (fun _ => Structural.ofFloat .fp32 (1 : Float)) (fun _ => Structural.ofFloat .fp32 (1 : Float))
  (fun _ => Structural.ofFloat .fp32 (0 : Float))).isNone

private def probe (e : QOp d sh) : QKernel := .mk [] [] [.assign d sh "probe" (.alg e)]

-- Each check is pinned separately, without the enclosing assignment that
-- would otherwise mask a broken arithmetic check with a transport rejection.
private def unsupportedFloats : List FloatDType := [.fp16, .f8e4, .f8e5]

#guard unsupportedFloats.all fun d => !opOK (some .fp32) (.constFloat d 1)
#guard unsupportedFloats.all fun d =>
  !opOK none (.load d.toTileDType (.region "x" (.constNat 0)) .none)
-- An FP16/F8 cast source is itself inadmissible, so test storageOK directly.
#guard unsupportedFloats.all fun d => !storageOK d
#guard unsupportedFloats.all fun d => !opOK none (.ref d.toTileDType [] "x")

-- Reject a hidden untyped add even in a mask, inactive loop, or dead branch.
private def untypedAdd : QOp .real [] :=
  .add .real .nil (.ref .real [] "x") (.ref .real [] "y")

private def badMask : QOp .bool [] := .lt .real .nil untypedAdd (.const 0)
private def badBody : List QStmt := [.assign .real [] "bad" (.alg untypedAdd)]

#guard !sourceRoundedAdmits (probe (.load .fp32 (.region "x" (.constNat 0)) (.mask badMask)))
#guard !sourceRoundedAdmits (probe (.load .fp32 (.region "x" (.constNat 0))
  (.maskOther badMask (.constFloat .fp32 0))))
#guard !sourceRoundedAdmits (probe (.load .fp32 (.region "x" (.constNat 0))
  (.maskOther (.constBool false) (.castFloat .real .fp32 untypedAdd))))
#guard !sourceRoundedAdmits (.mk [] [] [.forLoop "i" 0 badBody])
#guard !sourceRoundedAdmits (.mk [] [] [.forRange "i" 0 0 1 badBody])
#guard !sourceRoundedAdmits (.mk [] [] [.forRangeDyn "i" (.constNat 0) (.constNat 0) (.constNat 1) badBody])
#guard !sourceRoundedAdmits (.mk [] [] [.forRangeInt "i" (.constInt 0) (.constInt 0) (.constNat 1) badBody])
#guard !sourceRoundedAdmits (.mk [] [] [.ifThenElse (.constBool true) [] badBody])

-- Rejection is at the instantiated registration, not a NaN substitute.
#guard !sourceRoundedAdmits (probe (.castFloat .real .fp16 (.withPrecision .real .fp32 (.const 1))))
#guard !sourceRoundedAdmits (probe (.castFloat .real .f8e4 (.withPrecision .real .fp32 (.const 1))))
#guard !sourceRoundedAdmits (probe (.castFloat .real .f8e5 (.withPrecision .real .fp32 (.const 1))))
#guard !sourceRoundedAdmits (probe (.castFloat .fp16 .fp32 (.ref .fp16 [] "x")))
#guard !sourceRoundedAdmits (probe (.add .fp16 .nil (.constFloat .fp16 1) (.constFloat .fp16 2)))
#guard !sourceRoundedAdmits (probe (.mul .f8e4 .nil (.constFloat .f8e4 1) (.constFloat .f8e4 2)))
#guard !sourceRoundedAdmits (probe (.div .f8e5 .nil (.constFloat .f8e5 1) (.constFloat .f8e5 2)))
#guard !sourceRoundedAdmits (probe (.add .real .nil (.ref .real [] "x") (.ref .real [] "y")))
#guard !sourceRoundedAdmits (probe (.exp (.ref .real [] "x")))
#guard !sourceRoundedAdmits (probe (.absFloat .real (.ref .real [] "x")))
#guard !sourceRoundedAdmits (probe (.castFloat .real .real (.ref .real [] "x")))
#guard !sourceRoundedAdmits (probe (.const (1 / 3)))
#guard !sourceRoundedAdmits (probe (.lt .real .nil (.const (1 / 3)) (.ref .real [] "x")))
#guard !sourceRoundedAdmits (probe (.withPrecision .real .fp32 (.divRN .nil (.const 1) (.const 3))))
#guard ([.fp16, .f8e4, .f8e5] : List FloatDType).all fun d =>
  !sourceRoundedAdmits (probe (.constFloat d 1)) &&
  !sourceRoundedAdmits (probe (.negFloat d (.constFloat d 1)))
#guard sourceRoundedAdmits (probe (.lt .real .nil (.absFloat .real (.ref .real [] "x")) (.const (1 / 2))))
#guard sourceRoundedAdmits (probe (.withPrecision .real .fp32 (.add .real .nil (.const 1) (.const 2))))
#guard sourceRoundedAdmits (probe (.withPrecision .real .fp64 (.add .real .nil (.const 1) (.const 2))))
#guard sourceRoundedAdmits (probe (.add .fp32 .nil (.constFloat .fp32 1) (.constFloat .fp32 2)))

end VeriTile.Interp.Binary64
