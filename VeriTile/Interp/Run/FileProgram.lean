import VeriTile.Interp.Run.Main
import VeriTile.Interp.Carrier.Float
import VeriTile.Triton.Float.BitValue

/-! Typed file storage for host Float execution. FP32 and FP64 inputs
decode exactly into binary64; encoding checks the declared output dtype and
shape independently of the selected arithmetic algebra. -/
namespace VeriTile.Interp.Run
open VeriTile.Triton

structure Port where
  name : RegionName
  dtype : DType
  shape : List Nat
  /-- A dense logical matrix may live in a padded physical row. -/
  rowStride : Option Nat := none

private def Port.offset (port : Port) (logical : Nat) : Nat :=
  match port.rowStride, port.shape with
  | some stride, [_,cols] => logical / cols * stride + logical % cols
  | _, _ => logical

private def Port.contains (port : Port) (physical : Nat) : Bool :=
  match port.rowStride, port.shape with
  | some stride, [rows,cols] => physical / stride < rows && physical % stride < cols
  | _, _ => physical < elementCount port.shape

def checkInput (t : Tensor) (dtype : DType) (shape : List Nat) : Except String Unit := do
  unless t.dtype == dtype && t.shape == shape do
    throw s!"expected {repr dtype} {shape}, received {repr t.dtype} {t.shape}"

/-- Runtime source FP32 scalars enter the reflected rational parameter at
their represented value, including when the decimal is not exactly binary32. -/
def fp32Setting (settings : Settings) (key : String) : Except String ℚ := do
  let rounded := FP.round .fp32 .ieeeValue (← setting settings.scalars key)
  let some q := rounded.toRat? | throw s!"{key} is outside the finite FP32 range"
  return q

#guard fp32Setting { scalars := [("v", 1/10)] } "v" == .ok (13421773 / 134217728)

private def readBits (t : Tensor) (i : Nat) : Nat :=
  let w := t.dtype.width
  (t.data.extract (i*w) ((i+1)*w)).data.foldr (fun b n => 256*n + b.toNat) 0

private def decode (t : Tensor) (i : Nat) : Float :=
  let bits := readBits t i
  match t.dtype with
  | .fp32 => (Float32.ofBits bits.toUInt32).toFloat
  | .fp64 => Float.ofBits bits.toUInt64
  | _ => Float.nan

-- Direct conversion lands above the BF16 midpoint. A detour through FP32
-- would hit the midpoint itself and round down to 0x3f80.
#guard Binary64.bf16Bits (1.00390625 + 1 / 1073741824) == 0x3f81
#guard Binary64.bf16Bits (Float.ofBits 0x8000000000000000) == 0x8000

private def resultTensor (s : State Float) (port : Port) : Except String Tensor := do
  let mut bytes := ByteArray.empty
  for i in [:elementCount port.shape] do
    let some cell := s.cells[(port.name,port.offset i)]? | throw s!"missing write to {port.name.name}[{i}]"
    let bits ← match cell, port.dtype with
      | .mk .real x, .fp32 => pure x.toFloat32.toBits.toNat
      | .mk .real x, .fp64 => pure x.toBits.toNat
      | .mk .bf16 x, .bf16 => pure (Binary64.bf16Bits x)
      | _, _ => throw s!"unexpected store dtype at {port.name.name}[{i}]"
    for j in [:port.dtype.width] do bytes := bytes.push (bits >>> (8*j)).toUInt8
  return ⟨port.dtype, port.shape, bytes⟩

def runFloatFiles (algebra : CAlgebra Float) (dims : List Nat) (k : QKernel) (inputs : List (RegionName × Tensor))
    (outputs : List Port) : Except String (List Tensor) := do
  unless inputs.all (fun (_,t) => t.dtype == .fp32 || t.dtype == .fp64) do
    throw "binary64 input storage must be FP32 or FP64"
  let initial : State Float := {
    init := fun region i => .mk .real <| Id.run do
      let some t := inputs.lookup region | return Float.nan
      if i ≥ elementCount t.shape then return Float.nan
      return decode t i
    pids := fun _ => 0, numPids := fun _ => 1
    undef := fun d _ _ => FP.Structural.defaultValue d }
  let some s := runGrid algebra k dims initial | throw "kernel execution failed"
  for ((region,i),_) in s.cells.toList do
    let some port := outputs.find? (·.name == region) | throw s!"write to undeclared output {region.name}"
    unless port.contains i do throw s!"write outside {region.name} at {i}"
  outputs.mapM (resultTensor s)

def runBinary64Files (dims : List Nat) (k : QKernel) (inputs : List (RegionName × Tensor))
    (outputs : List Port) : Except String (List Tensor) :=
  runFloatFiles Binary64.algebra dims k inputs outputs

end VeriTile.Interp.Run
