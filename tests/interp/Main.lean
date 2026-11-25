/- Native executable registry. Reflected example kernels live outside the
interpreter target. The host binary32 fragment serves these two entries
until the general-purpose carriers are registered. -/
import VeriTile.Interp.Reflect
import VeriTile.Interp.Run.Main
import VeriTile.Interp.Run.GridOrder
import bench.examples.VectorAdd.Kernels
import bench.examples.OnlineSoftmax.Kernels

open VeriTile VeriTile.Triton VeriTile.Interp VeriTile.Interp.Run
open VeriTile.Bench.Examples

namespace VeriTile.Interp.Run

-- Give the executable's fixed port bindings their own names, so its mirrors
-- can be imported alongside the reflection and execution regression modules.
def vectorProgram (block : Nat) := VectorAdd.Kernels.originalKernel block
def softmaxProgram (cols : Nat) := OnlineSoftmax.Kernels.onlineSoftmaxKernel "x" "y" cols

reflect_kernel vectorProgram
reflect_kernel softmaxProgram

-- An unsupported numeric operation produces no value. No numeric placeholder
-- can reach a result file. The table below admits only the two reflected kernels.
private def fp32 : CAlgebra (Option Float32) where
  literal := fun _ _ q => if q == 0 then some 0 else none
  negInf := some (-1 / 0)
  binary := fun _ _ op a b => do
    let x ← a
    let y ← b
    match op with
    | .add => some (x + y) | .sub => some (x - y) | .mul => some (x * y)
    | .div => some (x / y) | .max => some (max x y) | .pow => none
  unary := fun _ op a => match op with
    | .exp | .libdeviceExp => a.map Float32.exp
    | _ => none
  cast := fun _ src dst a => if src == dst then a else none
  fromNat := fun _ n => some n.toFloat32
  fromInt := fun _ i => some (Float32.ofInt i)
  fp32Bits := fun b => some (Float32.ofBits b.bits.toNat.toUInt32)
  fp32Load := id
  reduceMax := fun _ {_} _ _ _ _ => none
  reduceSum := fun _ {_} _ _ _ _ => none

private def readWord (data : ByteArray) (i : Nat) : UInt32 :=
  (data.extract (4*i) (4*i+4)).data.foldr (fun b w => (w <<< 8) ||| b.toUInt32) 0

private def runFP32 : RunCarrier := fun grid k inputs out shape => do
  unless inputs.all (fun (_, t) => t.dtype == .fp32) do throw "fp32-basic needs fp32 tensors"
  let count := elementCount shape
  let sentinel := readWord (← sentinelBytes .fp32) 0
  let initial : State (Option Float32) := {
    init := fun reg i => .mk .real do
      if reg == out && i < count then return Float32.ofBits sentinel
      let t ← inputs.lookup reg
      guard (4*i+4 ≤ t.data.size)
      return Float32.ofBits (readWord t.data i)
    pids := fun _ => 0, numPids := fun _ => 1
    undef := fun d _ _ => FP.Structural.defaultValue d }
  let some state := runGrid fp32 k grid initial | throw "kernel execution failed"
  let mut bytes := ByteArray.empty
  for i in [:count] do
    let some cell := state.cells[(out,i)]? | throw s!"kernel did not write {out.name}[{i}]"
    let some value := cell.read .real | throw s!"unsupported value at {out.name}[{i}]"
    if value.toBits == sentinel then throw s!"output retains the sentinel at {out.name}[{i}]"
    for j in [:4] do bytes := bytes.push (value.toBits >>> (8*j).toUInt32).toUInt8
  return ⟨.fp32, shape, bytes⟩

-- Incomplete writes and unsupported arithmetic must fail before persistence.
#guard !(runFP32 [1] (.mk [] [] []) [] "out" [1]).isOk
#guard !(runFP32 [1] (.mk [] [] [.store .real [] (.region "out" (.constNat 0))
  (.alg (.const (1/3))) .none]) [] "out" [1]).isOk

private def programs (dims : List Nat) : Except String Nat := do
  let x := dims.headD 0
  unless x > 0 && dims.tail.all (· == 1) do throw "these kernels require a positive one-dimensional grid"
  return x

private def gridProbeState : State (Option Float32) := {
  init := fun _ _ => .mk .nat 0, pids := fun _ => 0, numPids := fun _ => 1
  undef := fun d _ _ => FP.Structural.defaultValue d }

-- Literal schedules check both padding and axis order independently of the index formula.
example : launchOrder [2, 3] =
    [(0, 0, 0), (0, 1, 0), (0, 2, 0), (1, 0, 0), (1, 1, 0), (1, 2, 0)] := by decide
example : launchOrder [2, 2, 2] =
    [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1),
     (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1)] := by decide
example : launchOrder [3] = [(0, 0, 0), (1, 0, 0), (2, 0, 0)] := by decide
example : launchOrder [2, 0, 3] = [] := by decide

-- Check the three-dimensional schedule against a noncommutative accumulation
-- of the eight linearized program ids. A different order or lost predecessor memory fails.
#guard Id.run do
  let addr : QMemAccess .nat [] := .region "trace" (.constNat 0)
  let digit : QOp .nat [] := .add .nat .nil (.programId 0) (.mul .nat .nil (.numPrograms 0)
    (.add .nat .nil (.programId 1) (.mul .nat .nil (.numPrograms 1) (.programId 2))))
  let step : QOp .nat [] := .add .nat .nil (.mul .nat .nil (.load .nat addr .none) (.constNat 10)) digit
  let probe : QKernel := .mk [] [] [.store .nat [] addr (.alg step) .none]
  return (runGrid fp32 probe [2, 2, 2] gridProbeState).map
    (fun t => (t.read "trace" 0).read .nat) == some 4261537

-- Each program reads the initial register before overwriting it. The second
-- program would store 9 if the first program's registers leaked through.
#guard Id.run do
  let probe : QKernel := .mk [] [] [
    .store .nat [] (.region "seen" (.programId 0)) (.alg (.ref .nat [] "local")) .none,
    .assign .nat [] "local" (.alg (.constNat 9))]
  let initial := gridProbeState.setReg "local" .nat [] (fun _ => 7)
  return (runGrid fp32 probe [2] initial).map (fun t => (t.read "seen" 1).read .nat) == some 7

private def vectorAdd : KernelEntry where
  inputs := ["x", "y"]
  output := "out"
  bind := fun dims shape => do
    let x ← programs dims
    let [size] := shape | throw "VectorAdd needs vectors"
    unless size > 0 && size % x == 0 do throw "vector length must be a positive multiple of grid X"
    return vectorProgram.mirror (size / x)

private def softmax : KernelEntry where
  inputs := ["x"]
  output := "y"
  bind := fun dims shape => do
    let x ← programs dims
    let [rows, cols] := shape | throw "OnlineSoftmax needs a matrix"
    unless rows == x && cols > 0 do throw "OnlineSoftmax needs one program per row and a nonempty row"
    return softmaxProgram.mirror cols

def exampleCli (args : List String) : IO UInt32 :=
  runCli [("VectorAdd", vectorAdd), ("OnlineSoftmax", softmax)] [("fp32-basic", runFP32)] args

end VeriTile.Interp.Run

def main (args : List String) : IO UInt32 := exampleCli args
