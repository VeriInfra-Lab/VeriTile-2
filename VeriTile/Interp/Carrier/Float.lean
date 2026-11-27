import Batteries.Data.Rat.Float
import VeriTile.Interp.Algebra
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
def sourceRoundedAlgebra : CAlgebra Float := { algebra with
  literal := sourceLiteral
  binary := sourceBinary
  unary := fun p op x => roundSource p (unaryDType op) (unary op x)
  cast := fun p _ dst => roundSource p dst
  fromNat := fun p n => sourceLiteral p .real n
  fromInt := fun p i => sourceLiteral p .real i
  fp32Load := fun x => x.toFloat32.toFloat
  reduceMax := fun p _ => reduce (sourceBinary p .real .max) (-Float.inf)
  reduceSum := fun p _ => reduce (sourceBinary p .real .add) 0
  reduceSumTyped := fun p d _ axis keep xs => some fun i =>
    Structural.ofFloat d (reduce (sourceBinary p d .add) 0 axis keep (fun j => Structural.toFloat d (xs j)) i)
  reduceMaxTyped := fun p d _ axis keep xs => some fun i =>
    Structural.ofFloat d (reduce (sourceBinary p d .max) (-Float.inf) axis keep (fun j => Structural.toFloat d (xs j)) i)
}

#guard sourceRoundedAlgebra.binary (some .fp32) .real .add 1 (1 / 16777216) == 1
#guard sourceRoundedAlgebra.binary (some .fp64) .real .add 1 (1 / 16777216) > 1
#guard sourceRoundedAlgebra.cast (some .fp32) .real .real (1 + 1 / 16777216) == 1
#guard sourceRoundedAlgebra.reduceSum (some .fp32) (shape := [2]) ⟨0, by decide⟩ false
  (fun i => if i.1.val == 0 then 1 else 1 / 16777216) PUnit.unit == 1
#guard sourceRoundedAlgebra.reduceSum (some .fp64) (shape := [2]) ⟨0, by decide⟩ false
  (fun i => if i.1.val == 0 then 1 else 1 / 16777216) PUnit.unit > 1
#guard sourceRoundedAlgebra.cast none .real .bf16 1.00390625 == 1
#guard sourceRoundedAlgebra.cast none .real .bf16 (1.00390625 + 1 / 1073741824) == 1.0078125

end VeriTile.Interp.Binary64
