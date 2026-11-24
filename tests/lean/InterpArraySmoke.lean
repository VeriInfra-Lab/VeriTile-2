import VeriTile.Interp.Array.Exec
import VeriTile.Interp.Reflect
import bench.examples.VectorAdd.Kernels
import bench.examples.FlatVectorAdd.Kernels

namespace VeriTile.Tests.InterpArraySmoke

open VeriTile.Triton VeriTile.Triton.FP VeriTile.Interp VeriTile.Bench.Examples

-- The reflected kernels use only fp32 loads, addition, and stores. The other
-- mandatory operations are stubs on this exact natural-number test carrier.
private def algebra : CAlgebra Nat where
  literal := fun _ _ q => q.num.toNat / q.den
  negInf := 0
  binary := fun _ _ op a b => match op with
    | .add => a + b | .sub => a - b | .mul => a * b | .div => a / b | .max => max a b | .pow => a ^ b
  unary := fun _ _ a => a
  cast := fun _ _ _ a => a
  fromNat := fun _ n => n
  fromInt := fun _ i => i.toNat
  fp32Bits := fun b => b.bits.toNat
  fp32Load := id
  reduceMax := fun _ {_} _ _ _ _ => 0
  reduceSum := fun _ {_} _ _ _ _ => 0

private def initial (pid : Nat) : Array.State Nat where
  init := fun r i => .mk .real (if r == "x" then 2*i + 1 else if r == "y" then i + 3 else 99)
  pids := fun _ => pid
  numPids := fun _ => 2
  undef := fun d _ _ => Structural.defaultValue d

-- Keep these specialized mirrors local to this regression namespace.
def vectorProgram := VectorAdd.Kernels.originalKernel 4
def maskedProgram := FlatVectorAdd.Kernels.addMaskedKernel "x" "y" "out" 2 3
reflect_kernel vectorProgram
reflect_kernel maskedProgram

private def outputs (k : QKernel) (pid : Nat) : Option (List Nat) × Option (List Nat) :=
  let s := initial pid
  let offsets := List.range 5
  ((Array.interp algebra k s).map fun t => offsets.map fun i => (t.read "out" i).read .real,
   (interp algebra k s.view).map fun t => offsets.map fun i => (t.read "out" i).read .real)

#eval outputs vectorProgram.mirror 0
#guard outputs vectorProgram.mirror 0 = (some [4, 7, 10, 13, 99], some [4, 7, 10, 13, 99])
#eval outputs maskedProgram.mirror 1
#guard outputs maskedProgram.mirror 1 = (some [99, 99, 10, 99, 99], some [99, 99, 10, 99, 99])

-- Aliased lanes accumulate in iteration order at one sparse address.
private def accumulate : QKernel := .mk [] [] [.forLoop "i" 2
  [.alg (.atomicAdd .nat [3] (.region "a" (.broadcast (.constNat 1000000000) [3]))
    (.arange 3) .none)]]
#guard ((Array.interp algebra accumulate (initial 0)).map fun s =>
  ((s.read "a" 1000000000).read .nat, s.memory.cells.size)) = some (6, 1)

-- Four row-major lanes write one cell. Appending decimal digits makes each
-- atomic update observable, including permutations that preserve the last lane.
private def aliasedAddress : QMemAccess .real [2, 2] :=
  .region "out" (.broadcast (.constNat 0) [2, 2])

private def aliasedOutputs (st : QAlgStmt) : Option Nat × Option Nat :=
  let s := ((initial 0).write ("out", 0) (.mk .real 0)).setReg "lanes" .real [2, 2]
    (fun i => 2 * i.1.val + i.2.1.val + 1)
  let m := { algebra with atomicAdd := fun _ => some (fun a b => a * 10 + b) }
  let k := QKernel.mk [] [] [.alg st]
  ((Array.interp m k s).map fun t => (t.read "out" 0).read .real,
   (interp m k s.view).map fun t => (t.read "out" 0).read .real)

#guard aliasedOutputs (.store .real [2, 2] aliasedAddress (.ref .real [2, 2] "lanes") .none)
    = (some 4, some 4)
#guard aliasedOutputs (.atomicAdd .real [2, 2] aliasedAddress (.ref .real [2, 2] "lanes") .none)
    = (some 1234, some 1234)

-- Checked block-pointer lanes skip out-of-bounds writes. A masked pointer
-- store ignores its `other` branch and updates the previously written cell.
private def pointers : QKernel := .mk [] []
  [.alg (.store .nat [3] (.blockPtr (.makeBlockPtr (d := .nat) "p" 0 [2] [3] [1] [0]) [0])
    (.arange 3) .none),
   .store .nat [3] (.ptr (.ptrAdd .scalarL (.ptrBase (d := .nat) "p") (.arange 3)))
    (.alg (.broadcast (.constNat 9) [3]))
    (.maskOther (.lt .nat .scalarR (.arange 3) (.constNat 1)) (.ref .nat [3] "unbound"))]
#guard ((Array.interp algebra pointers (initial 0)).map fun t =>
  ((t.read "p" 0).read .nat, (t.read "p" 1).read .nat, (t.read "p" 2).read .real,
   t.memory.cells.size)) = some (9, 1, 99, 2)

-- Retyping a register discards its previous binding, including empty tiles.
private def rebound := ((initial 0).setReg "v" .nat [0] (fun i => Fin.elim0 i.1)).setReg "v" .nat [2, 3]
  (fun i => 3 * i.1.val + i.2.1.val)
#guard (rebound.view.getReg .nat [0] "v").isNone
#guard (rebound.view.getReg .nat [2, 3] "v").map ((TileShape.allIndices [2, 3]).map)
    = some [0, 1, 2, 3, 4, 5]

-- Nested ranges and guarded branches use the bound register or propagate failure.
private def control : QKernel := .mk [] []
  [.forRangeDyn "i" (.constNat 1) (.constNat 5) (.constNat 2)
    [.forRangeInt "j" (.constInt (-2)) (.constInt 0) (.constNat 1)
      [.ifThenElse (.constBool Bool.false) [.effectMarker "unsupported"]
        [.store .nat [] (.region "ctrl" (.ref .nat [] "i")) (.alg (.ref .nat [] "i")) .none]]],
   .forRange "i" 0 2 0 [.effectMarker "unsupported"], .effectMarker "tl.debug_barrier"]
#guard ((Array.interp algebra control (initial 0)).map fun t =>
  [(t.read "ctrl" 1).read .nat, (t.read "ctrl" 3).read .nat]) = some [1, 3]
#guard (Array.interp algebra (.mk [] [] [.ifThen (.constBool Bool.true) [.effectMarker "unsupported"]])
    (initial 0)).isNone

-- The floating atomic backend is optional and absent on this algebra.
#guard (Array.interp algebra (.mk [] [] [.alg (.atomicAdd .real [] (.region "a" (.constNat 0))
  (.const 1) .none)]) (initial 0)).isNone

end VeriTile.Tests.InterpArraySmoke
