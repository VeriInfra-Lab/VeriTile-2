/- File runner for the reflected kernels and executable carriers supplied by
the outer executable. Kernel bindings and their shape checks stay with the
registry, keeping bench imports outside the interpreter library. -/
import VeriTile.Interp.Run.Grid
import VeriTile.Interp.Run.TensorIO
import Lean.Data.Json.Parser

namespace VeriTile.Interp.Run
open VeriTile.Triton

structure KernelEntry where
  inputs : List RegionName
  output : RegionName
  /-- Given the grid and the common tensor shape, instantiate the kernel. -/
  bind : List Nat → List Nat → Except String QKernel
  /-- Opt-in explicit source constexpr bindings. Existing entries still specialize from the shape. -/
  bindConstants : List (String × Nat) → List Nat → List Nat → Except String QKernel :=
    fun constants dims shape => do
      unless constants.isEmpty do throw "this kernel does not accept explicit constexpr parameters"
      bind dims shape

/-- A carrier owns the tensor encoding of its cells and the output readback. -/
abbrev RunCarrier := List Nat → QKernel → List (RegionName × Tensor) → RegionName →
  List Nat → Except String Tensor

/-- Exact decimal values supplied at the public CLI, split by source binding kind. -/
structure Settings where
  constants : List (String × ℚ) := []
  scalars : List (String × ℚ) := []

def Settings.check (s : Settings) (constants scalars : List String) : Except String Unit := do
  for (values, names) in [(s.constants, constants), (s.scalars, scalars)] do
    unless values.length == names.length && names.all (fun k => (values.lookup k).isSome) do
      throw s!"expected settings {names}, received {values.map Prod.fst}"

def setting (values : List (String × ℚ)) (key : String) : Except String ℚ :=
  match values.lookup key with | some value => .ok value | none => .error s!"missing {key}"

def naturalSetting (values : List (String × ℚ)) (key : String) : Except String Nat := do
  let n ← setting values key
  unless n.den == 1 && n.num ≥ 0 do throw s!"{key} must be a natural number"
  return n.num.toNat

/-- A file binding declares its ordered read ports and the result files. A
port may occur in both lists when the source updates it in place. -/
structure FileEntry where
  inputs : List RegionName
  outputs : List RegionName
  carrier : String
  run : Settings → List Nat → List Tensor → Except String (List Tensor)

private def usage (kernels : List (String × KernelEntry)) (entries : List (String × FileEntry))
    (carriers : List String) : String :=
  let forms := kernels.map fun (name, entry) =>
    "  " ++ " ".intercalate (name :: (entry.inputs.map (·.name)) ++ [entry.output.name])
  let extra := entries.map fun (name, entry) =>
    "  " ++ " ".intercalate (name :: (entry.inputs.map (·.name)) ++
      [if entry.outputs.length == 1 then (entry.outputs.head?.map (·.name)).getD "OUTPUT" else "OUTPUT-DIR"])
  "veritile-run --carrier NAME --grid X[,Y[,Z]] [--constexpr NAME=NUMBER | --scalar NAME=NUMBER]... KERNEL INPUT... OUTPUT\n" ++
    "\n".intercalate (forms ++ extra) ++ "\nCarriers: " ++ ", ".intercalate carriers.eraseDups

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

/-- Multi-output calls publish a new result directory. All tensor bytes are
prepared before the single rename, so a reader cannot observe half a launch. -/
private def writeResults (path : System.FilePath) (outputs : List (RegionName × Tensor)) : IO Unit := do
  if let [(_, tensor)] := outputs then return ← writeOutput path tensor
  let temp := path.addExtension s!"tmp.{← IO.Process.getPID}.{← IO.monoNanosNow}"
  IO.FS.createDir temp
  try
    for (port, tensor) in outputs do
      IO.FS.writeBinFile (temp / (port.name ++ ".tensor")) (← IO.ofExcept tensor.toBytes)
    IO.FS.rename temp path
  finally
    if ← temp.pathExists then IO.FS.removeDirAll temp

private def parseSettings (args : List String) (settings : Settings := {}) :
    Except String (Settings × List String) := do
  match args with
  | option :: item :: rest =>
    unless option == "--constexpr" || option == "--scalar" do return (settings,args)
    let [key, text] := item.splitOn "=" | throw s!"invalid setting {item}; expected NAME=NUMBER"
    let value : ℚ ← match text.toNat? with
      | some natural => pure (natural : ℚ)
      | none => do
        let .num n ← Lean.Json.parse text | throw s!"invalid number in {item}"
        pure (mkRat n.mantissa (10 ^ n.exponent))
    unless !key.isEmpty && !(settings.constants ++ settings.scalars).any (·.1 == key) do
      throw s!"empty or repeated setting {key}"
    let next := if option == "--constexpr" then { settings with constants := (key,value) :: settings.constants }
      else { settings with scalars := (key,value) :: settings.scalars }
    parseSettings rest next
  | _ => return (settings,args)

def runCli (kernels : List (String × KernelEntry)) (carriers : List (String × RunCarrier))
    (args : List String) (entries : List (String × FileEntry) := []) : IO UInt32 := do
  let help := usage kernels entries (carriers.map Prod.fst ++ entries.map (·.2.carrier))
  if args == ["--help"] then
    IO.println help
    return (0 : UInt32)
  try
    let "--carrier" :: carrier :: "--grid" :: grid :: rest := args | throw <| IO.userError help
    let (settings, positional) ← IO.ofExcept (parseSettings rest)
    let kernel :: files := positional | throw <| IO.userError help
    let some dims := (grid.splitOn ",").mapM String.toNat? | throw <| IO.userError s!"invalid grid {grid}"
    unless 1 ≤ dims.length && dims.length ≤ 3 do throw <| IO.userError s!"invalid grid {grid}"
    let some output := files.getLast? | throw <| IO.userError help
    if let some entry := entries.lookup kernel then
      unless carrier == entry.carrier do throw <| IO.userError s!"{kernel} requires carrier {entry.carrier}"
      unless files.length == entry.inputs.length + 1 do throw <| IO.userError s!"{kernel} expects {entry.inputs.length} inputs and one output path"
      let tensors ← files.dropLast.mapM fun path => Tensor.read path
      let results ← IO.ofExcept (entry.run settings dims tensors)
      unless !entry.outputs.isEmpty && results.length == entry.outputs.length do throw <| IO.userError "file binding returned wrong number of outputs"
      writeResults output (entry.outputs.zip results)
    else
      let some run := carriers.lookup carrier | throw <| IO.userError s!"unknown carrier {carrier}"
      let some entry := kernels.lookup kernel | throw <| IO.userError s!"unknown kernel {kernel}"
      unless settings.scalars.isEmpty do throw <| IO.userError s!"{kernel} does not accept scalar settings"
      let constants ← IO.ofExcept <| settings.constants.mapM fun (key,_) => do
        return (key, ← naturalSetting settings.constants key)
      unless files.length == entry.inputs.length + 1 do throw <| IO.userError s!"{kernel} needs {entry.inputs.length} input file(s) and one output file"
      let tensors ← files.dropLast.mapM fun path => Tensor.read path
      let first :: _ := tensors | throw <| IO.userError "expected at least one input tensor"
      unless tensors.all (·.shape == first.shape) do throw <| IO.userError "input tensor shapes differ"
      let k ← IO.ofExcept (entry.bindConstants constants dims first.shape)
      writeOutput output (← IO.ofExcept (run dims k (entry.inputs.zip tensors) entry.output first.shape))
    return (0 : UInt32)
  catch e =>
    IO.eprintln e
    return (1 : UInt32)

end VeriTile.Interp.Run
