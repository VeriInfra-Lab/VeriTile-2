/- Batch interface for the bit-pattern interpreter carrier regression. -/
import VeriTile.Interp.Carrier.FPValue

open VeriTile.Triton VeriTile.Triton.FP VeriTile.Interp

private def parseFormat : String → Except String Format
  | "bf16" => .ok .bf16
  | "fp32" => .ok .fp32
  | _ => .error "unknown format"

private def parseMode : String → Except String Rounding
  | "rne" => .ok .nearestEven
  | "rtz" => .ok .towardZero
  | "rup" => .ok .towardPositive
  | "rdn" => .ok .towardNegative
  | _ => .error "unknown rounding mode"

private def parseBool : String → Except String Bool
  | "0" => .ok false
  | "1" => .ok true
  | _ => .error "expected 0 or 1"

private def parseBits (f : Format) (s : String) : Except String (Value f) := do
  let some n := s.toNat? | throw "expected unsigned bits"
  if n >= 2 ^ f.width then throw "bit pattern exceeds format width"
  return Value.ofBits f n

private def runLine (line : String) : Except String Nat := do
  let [fmt, mode, flushIn, flushOut, op, a, b, c] := line.splitOn " "
    | throw "expected: format mode flushIn flushOut op a b c"
  let f ← parseFormat fmt
  let cfg : Config := ⟨← parseMode mode, ← parseBool flushIn, ← parseBool flushOut⟩
  let model := FPValue.partialAlgebra f cfg
  let d : FloatDType := match f with | .fp32 => .fp32 | .bf16 => .bf16
  let evaluate : Except String (Option (FP.Value f)) := do
    if op == "round" then
      let some num := a.toInt? | throw "invalid numerator"
      let some den := b.toNat? | throw "invalid denominator"
      if den == 0 then throw "zero denominator"
      let q := mkRat num den
      let rounded := model.literal none d q
      return if q == 0 && (← parseBool c) then model.unary none (.neg d) rounded else rounded
    let x := some (← parseBits f a)
    let y := some (← parseBits f b)
    let z := some (← parseBits f c)
    match op with
    | "neg" => return model.unary none (.neg d) x
    | "abs" => return model.unary none (.abs d) x
    | "add" => return model.binary none d .add x y
    | "sub" => return model.binary none d .sub x y
    | "mul" => return model.binary none d .mul x y
    | "div" => return model.binary none d .div x y
    | "fma" => return (model.fmaTyped d).bind fun g => g x y z
    | "eq" | "lt" =>
      let comparison := if op == "eq" then model.compareEq none d else model.compareLt none d
      return comparison.map fun g => FP.Value.ofBits f (if g x y then 1 else 0)
    | _ => throw "outside arithmetic-only carrier"
  let some result ← evaluate | throw "arithmetic word missing"
  return result.raw

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    match runLine line.trimAscii.toString with
    | .ok n => output.putStrLn (toString n)
    | .error e => throw (IO.userError e)
