import VeriTile.Interp.Carrier.Float
import tests.lean.InterpEvalSmoke

namespace VeriTile.Tests.InterpFloatCarrier
open VeriTile Triton Interp FP VeriTile.Bench.Examples

private def run (k : QKernel) (input : RegionName → Nat → Float) (region : RegionName)
    (size : Nat) : Option (List Float) := do
  let s ← interp Binary64.algebra k {
    init := fun r i => .mk .real (input r i)
    pids := fun _ => 0, numPids := fun _ => 1
    undef := fun d _ _ => Structural.defaultValue d }
  return (List.range size).map fun i => (s.read region i).read .real

#guard run (VectorAdd.Kernels.originalKernel.mirror 2)
  (fun r i => if r == "x" then i.toFloat + 0.25 else 0.5) "out" 2 == some [0.75, 1.75]
#guard run (RowWiseSum.Kernels.rowWiseSumKernel.mirror "x" "y" 3 3)
  (fun _ i => (i+1).toFloat) "y" 1 == some [6]

private def u := Binary64.algebra.unary none
#guard (u .erf 1 - 0.8427007929497149).abs < 2e-15
#guard u .erf (-10) == -1 && (u .erf Float.nan).isNaN
#guard u .libdeviceLog1p 1e-20 == 1e-20 && u .libdeviceExpm1 (-1e-20) == -1e-20
#guard u .sigmoid 0 == 0.5 && (u .sqrt (-1)).isNaN
-- The product alone rounds to 1; a fused operation retains the nonzero residual.
#guard (Binary64.algebra.fma .fp64).map (fun f => f (1 + (1.0).scaleB (-27)) (1 - (1.0).scaleB (-27)) (-1))
  == some (-(1.0 : Float).scaleB (-54))
#guard Binary64.algebra.literal none .real ((2^1100 + 1) / (2^1100 + 3)) == 1
#guard (Binary64.algebra.literal none .real (1 / (2^1075))).toBits == 0
#guard (Binary64.algebra.literal none .real ((2^60+1) / (2^1135))).toBits == 1
#guard (Binary64.algebra.literal none .real (-1 / (2^1075))).toBits == (1 : UInt64) <<< 63

private def matrix (r c : Fin 2) : Float := (2*r.val + c.val + 1).toFloat

-- [[1,2],[3,4]]² has lower left entry 15. An unmodelled input precision fails.
private def product (precision : String) : Option Float := do
  let result ← Binary64.algebra.dotWithOptions none {inputPrecision := some precision}
    (batch := []) (m := 2) (k := 2) (n := 2)
    (fun (r,c,_) => matrix r c) (fun (r,c,_) => matrix r c)
  return result (1,0,())
#guard product "ieee" == some 15
#guard (product "tf32").isNone
end VeriTile.Tests.InterpFloatCarrier
