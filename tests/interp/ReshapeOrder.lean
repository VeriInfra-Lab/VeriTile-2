import VeriTile.Interp.EvalOp
import VeriTile.Interp.Carrier.Float

open VeriTile.Triton VeriTile.Interp

private def state : State Float where
  init := fun _ _ => .mk .nat 0
  pids := fun _ => 0
  numPids := fun _ => 1
  undef := fun d _ _ => FP.Structural.defaultValue d

/-- Read every output coordinate of the interpreter's reshape in row-major order. -/
private def checkReshape (input output : TileShape) (encode : TileIndex input → Nat)
    (expected : List Nat) : IO Bool := do
  let s := state.setReg "input" .nat input encode
  let op : QOp .nat output := .reshape output (.ref .nat input "input")
  let actual := (evalOp Binary64.algebra none op s).map fun values =>
    (TileShape.allIndices output).map values
  if actual == some expected then return true
  IO.eprintln s!"reshape {input} → {output}: expected {expected}, got {repr actual}"
  return false

def main : IO UInt32 := do
  -- Coordinate-coded input distinguishes different source elements without a second reshape.
  let matrix ← checkReshape [2, 3] [3, 2] (fun (r, c, _) => 10 * r.val + c.val)
    [0, 1, 2, 10, 11, 12]
  let cube ← checkReshape [2, 2, 3] [3, 2, 2]
    (fun (z, r, c, _) => 100 * z.val + 10 * r.val + c.val)
    [0, 1, 2, 10, 11, 12, 100, 101, 102, 110, 111, 112]
  return if matrix && cube then 0 else 1
