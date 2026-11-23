import VeriTile.Interp.Carrier.FPValue
import VeriTile.Interp.Reflect
import bench.examples.VectorAdd.Kernels
import bench.examples.FloatDTypeAdd.Kernels

namespace VeriTile.Tests.InterpFPValue
open VeriTile.Interp VeriTile.Triton VeriTile.Triton.FP

-- The arithmetic result is independent of the rest algebra at the supported format.
example (rest : CAlgebra (FP.Value .fp32)) (cfg) (a b) :
    (FPValue.algebra .fp32 rest cfg).binary (some .fp32) .real .mul a b = FP.mul cfg a b := rfl

example (rest : CAlgebra (FP.Value .bf16)) (cfg) (a : FP.Value .bf16) :
    (FPValue.algebra .bf16 rest cfg).cast none .bf16 .bf16 a = a := rfl

-- Bind separate names so the benchmark's own mirror can coexist with other regression modules.
def vector (n : Nat) := Bench.Examples.VectorAdd.Kernels.originalKernel n
def castVector (n : Nat) := Bench.Examples.FloatDTypeAdd.Kernels.originalKernel n
reflect_kernel vector
reflect_kernel castVector

private instance {f} : Inhabited (FP.Value f) := ⟨FP.Value.zero f⟩

private def initial (f : Format) : State (FP.Value f) where
  init := fun r _ => .mk .real (if r == "x" then FP.round f .ieeeValue (1/2) else FP.round f .ieeeValue 1)
  pids _ := 0
  numPids _ := 1
  undef d _ _ := Structural.defaultValue d

private def result (f : Format) (k : QKernel) (d : FloatDType) : Option Nat := do
  let t ← FPValue.run f .ieeeValue k (initial f)
  let cell ← t.cells[(("out" : RegionName), (0 : Nat))]?
  let x := Structural.toFloat d (cell.read d.toTileDType)
  return x.raw

#guard result .fp32 (vector.mirror 2) .real == some 0x3fc00000
#guard result .fp32 (castVector.mirror 2) .real == some 0x3fc00000
#guard !(FPValue.admits .bf16 (vector.mirror 2))

-- Reuse the returned state, including an existing cell and its raw NaN payload.
#guard Id.run do
  let seed := (initial .fp32).write "previous" 8 (.mk .fp32 (FP.Value.ofBits .fp32 0x7fa12345))
  let some first := FPValue.run .fp32 .ieeeValue (vector.mirror 2) seed | return Bool.false
  let some next := FPValue.run .fp32 .ieeeValue (castVector.mirror 2) first | return Bool.false
  return ((next.read "previous" 8).read .fp32).raw == 0x7fa12345

private def bf16Compute : QKernel := .mk [] ["out"]
  [.store .bf16 [] (.region "out" (.constNat 0))
    (.fmaTyped .bf16 .nil .nil (.alg (.constFloat .bf16 (129/128)))
      (.alg (.constFloat .bf16 (127/128))) (.alg (.constFloat .bf16 (-1)))) .none]
-- (1 + 2^-7) * (1 - 2^-7) - 1 = -2^-14, with one final rounding.
#guard result .bf16 bf16Compute .bf16 == some 0xb880

#guard Id.run do
  let m := FPValue.partialAlgebra .fp32
  let some fused := m.fma .fp32 | return Bool.false
  let literal := m.literal (some .fp32) .real
  let x := fused (literal (8193/8192)) (literal (8191/8192)) (literal (-1))
  let nan := m.fp32Bits ⟨0x7fa12345⟩
  return x.map FP.Value.raw == some 0xb2800000 && nan.map FP.Value.raw == some 0x7fa12345 &&
    (m.fma .fp64).isNone

-- Every source bit must survive a same-format cast, including a signaling NaN.
#guard Id.run do
  let f := FPValue.partialAlgebra .bf16
  let word := some (FP.Value.ofBits .bf16 0xff83)
  return (f.cast none .bf16 .bf16 word).map FP.Value.raw == some 0xff83 &&
    (f.cast none .bf16 .fp32 word).isNone &&
    (f.unary none .exp word).isNone

private def deadUnsupported (e : QOp .real []) : QKernel := .mk [] []
  [.ifThen (.constBool Bool.false) [.assign .real [] "bad" (.compute (.alg .fp32 e))]]
#guard (FPValue.run .fp32 .ieeeValue (deadUnsupported (.exp (.const 0))) (initial .fp32)).isNone
#guard !(FPValue.admits .fp32 (deadUnsupported (.reduceSum (shape := [1]) ⟨0,by decide⟩ Bool.false (.natToReal (.arange 1)))))
#guard !(FPValue.admits .fp32 (.mk [] [] [.assign .fp16 [] "half" (.alg (.constFloat .fp16 1))]))

-- Compile-time cases cover unordered comparisons, directed rounding, flushing and signed zeros.
#guard Id.run do
  let m := FPValue.partialAlgebra .fp32 { Config.ieeeValue with rounding := .towardNegative }
  let nan := some (FP.Value.ofBits .fp32 0x7fc00001)
  let one := some (FP.Value.ofBits .fp32 0x3f800000)
  let negOne := some (FP.Value.ofBits .fp32 0xbf800000)
  let le := (m.compareLe none .fp32).map fun run => run nan one
  return le == some Bool.false && ((m.binary none .fp32 .add one negOne).map FP.Value.raw == some 0x80000000) &&
    ((m.unary none (.abs .fp32) negOne).map FP.Value.raw == some 0x3f800000)
#guard Id.run do
  let m := FPValue.partialAlgebra .bf16 { Config.ieeeValue with flushInputs := Bool.true }
  let subnormal := some (FP.Value.ofBits .bf16 1)
  return (m.binary none .bf16 .add subnormal subnormal).map FP.Value.raw == some 0

end VeriTile.Tests.InterpFPValue
