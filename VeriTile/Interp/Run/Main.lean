/- File runner for the reflected kernels and executable carriers supplied by
the outer executable. Kernel bindings and their shape checks stay with the
registry, keeping bench imports outside the interpreter library. -/
import VeriTile.Interp.Run.Grid
import VeriTile.Interp.Run.TensorIO

namespace VeriTile.Interp.Run
open VeriTile.Triton

structure KernelEntry where
  inputs : List RegionName
  output : RegionName
  /-- Given the grid and the common tensor shape, instantiate the kernel. -/
  bind : List Nat → List Nat → Except String QKernel

/-- A carrier owns the tensor encoding of its cells and the output readback. -/
abbrev RunCarrier := List Nat → QKernel → List (RegionName × Tensor) → RegionName →
  List Nat → Except String Tensor

private def usage (kernels : List (String × KernelEntry)) (carriers : List String) : String :=
  let forms := kernels.map fun (name, entry) =>
    "  " ++ " ".intercalate (name :: (entry.inputs.map (·.name)) ++ [entry.output.name])
  "veritile-run --carrier NAME --grid X[,Y[,Z]] KERNEL INPUT... OUTPUT\n" ++
    "\n".intercalate forms ++ "\nCarriers: " ++ ", ".intercalate carriers

private def writeOutput (path : System.FilePath) (tensor : Tensor) : IO Unit := do
  let bytes ← IO.ofExcept tensor.toBytes
  let temp := path.addExtension s!"tmp.{← IO.Process.getPID}.{← IO.monoNanosNow}"
  -- Open exclusively. The callback returns no handle, so it closes before rename or cleanup.
  let written ← IO.FS.withFile temp .writeNew fun handle => EIO.toBaseIO do
    handle.write bytes
    handle.flush
  try
    EIO.ofExcept written
    IO.FS.rename temp path
  catch e =>
    IO.FS.removeFile temp
    throw e

def runCli (kernels : List (String × KernelEntry)) (carriers : List (String × RunCarrier))
    (args : List String) : IO UInt32 := do
  let help := usage kernels (carriers.map Prod.fst)
  if args == ["--help"] then
    IO.println help
    return (0 : UInt32)
  try
    let "--carrier" :: carrier :: "--grid" :: grid :: kernel :: files := args
      | throw <| IO.userError help
    let some run := carriers.lookup carrier | throw <| IO.userError s!"unknown carrier {carrier}"
    let some entry := kernels.lookup kernel | throw <| IO.userError s!"unknown kernel {kernel}"
    let some dims := (grid.splitOn ",").mapM String.toNat?
      | throw <| IO.userError s!"invalid grid {grid}"
    unless 1 ≤ dims.length && dims.length ≤ 3 do throw <| IO.userError s!"invalid grid {grid}"
    unless files.length == entry.inputs.length + 1 do
      throw <| IO.userError s!"{kernel} needs {entry.inputs.length} input file(s) and one output file"
    let some output := files.getLast? | throw <| IO.userError help
    let tensors ← files.dropLast.mapM fun path => Tensor.read path
    let first :: _ := tensors | throw <| IO.userError "expected at least one input tensor"
    unless tensors.all (·.shape == first.shape) do throw <| IO.userError "input tensor shapes differ"
    let k ← IO.ofExcept (entry.bind dims first.shape)
    let result ← IO.ofExcept (run dims k (entry.inputs.zip tensors) entry.output first.shape)
    writeOutput output result
    return (0 : UInt32)
  catch e =>
    IO.eprintln e
    return (1 : UInt32)

end VeriTile.Interp.Run
