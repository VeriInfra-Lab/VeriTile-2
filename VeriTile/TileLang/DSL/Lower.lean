import VeriTile.TileLang.DSL.Accepted
import VeriTile.Triton.Core.SignedCast

/-! Executable A3.1 lowering for single-thread, one-dimensional int32 kernels.
The launch extent and tensor extents accompany the per-program core kernel.
Specialization, shared memory, synchronization and operator contracts have
separate owners. Unsupported statements cannot disappear during lowering. -/
namespace VeriTile.TileLang
open Lean VeriTile.Triton

structure Lowered where
  name : Name
  entry : Name
  grid : Nat
  threads : Nat
  /-- Ordered parameters, each a one-dimensional int32 tensor of this extent. -/
  buffers : List (Name × Nat)
  result : Name
  kernel : Kernel

namespace CoreLower

private structure Context where
  grid : Nat
  axis : Name
  buffers : List (Name × Nat)
  result : Name

private inductive Scalar where
  | integer (value : Op .int [])
  | boolean (value : Op .bool [])

private abbrev Registers := List (Name × TileDType)

-- Establish every access in bounds in the declared launch. Reject other
-- indices until #86 can carry their dynamic bounds obligations.
private def offset (ctx : Context) (buffer : Name) (coords : List Index) : Except String (Op .nat []) := do
  let some extent := ctx.buffers.lookup buffer | throw s!"unknown int32 tensor {buffer}"
  match coords with
  | [.atIndex (.ident i)] =>
    unless i == ctx.axis && ctx.grid ≤ extent do throw "unproved one-dimensional tensor index"
    return .programId 0
  | [.atIndex (.integer i)] =>
    unless i < extent do throw "tensor index is outside its extent"
    return .constNat i
  | _ => throw "tensor indexing requires a checked one-dimensional coordinate (#86)"

private def scalar (ctx : Context) (regs : Registers) : Value → Except String Scalar
  | .integer n => do
    unless n < 2^31 do throw "integer literal does not fit int32"
    return .integer (.constInt n)
  | .boolean b => return .boolean (.constBool b)
  | .ident name => do
    if name == ctx.axis then return .integer (.castNatToInt (.programId 0))
    match regs.lookup name with
    | some .nat => return .integer (.castNatToInt (.ref .nat [] name.getString!))
    | some .int => return .integer (.ref .int [] name.getString!)
    | some .bool => return .boolean (.ref .bool [] name.getString!)
    | _ => throw s!"unbound scalar {name}"
  | .index name coords => do
    return .integer (.intToSigned 32 (.load .int (.region ⟨name.getString!⟩ (← offset ctx name coords)) .none))
  | .neg x => do
    let .integer v ← scalar ctx regs x | throw "unary minus expects int32"
    return .integer (.intToSigned 32 (.sub .int .nil (.constInt 0) v))
  | .binary op x y => do
    match op, ← scalar ctx regs x, ← scalar ctx regs y with
    | .add, .integer a, .integer b => return .integer (.intToSigned 32 (.add .int .nil a b))
    | .sub, .integer a, .integer b => return .integer (.intToSigned 32 (.sub .int .nil a b))
    | .mul, .integer a, .integer b => return .integer (.intToSigned 32 (.mul .int .nil a b))
    | .lt, .integer a, .integer b => return .boolean (.lt .int .nil a b)
    | .eq, .integer a, .integer b => return .boolean (.eq .int .nil a b)
    | _, _, _ => throw "unavailable scalar operator or incompatible operand types (#86)"
  | _ => throw "value needs a TileLang expression or operator contract (#85–#89)"

mutual
private def statement (ctx : Context) (current : Registers) (stmt : Statement) :
    Except String (Stmt × Registers) := do
  match stmt with
  | .assign (.variable name) rhs =>
    unless name != ctx.axis && (ctx.buffers.lookup name).isNone do throw "cannot shadow a launch or tensor parameter"
    let (dtype, assignment) ← match ← scalar ctx current rhs with
      | .integer v => pure (TileDType.int, Stmt.assign .int [] name.getString! v)
      | .boolean v => pure (TileDType.bool, Stmt.assign .bool [] name.getString! v)
    if let some previous := current.lookup name then
      unless previous == dtype do throw "scalar assignment changes its dtype"
    return (assignment, (name, dtype) :: current)
  | .assign (.index buffer coords) rhs =>
    unless buffer == ctx.result do throw "only the returned tensor may be written by this lowering"
    let index ← offset ctx buffer coords
    let .integer v ← scalar ctx current rhs | throw "int32 tensor store expects int32"
    return (.store .int [] (.region ⟨buffer.getString!⟩ index) v .none, current)
  | .branch condition yes no =>
    let .boolean b ← scalar ctx current condition | throw "branch condition must have bool dtype"
    let (thenBody, _) ← suite ctx current yes
    let (elseBody, _) ← suite ctx current no
    -- Only bindings already live at branch entry can be read after the join.
    return (.ifThenElse b thenBody elseBody, current)
  | .loop [i] `range [.pos (.integer count)] body =>
    unless count < 2^31 do throw "range extent must fit int32"
    unless i != ctx.axis && (ctx.buffers.lookup i).isNone && (current.lookup i).isNone do
      throw "loop binder shadows a live parameter or scalar"
    let (loopBody, _) ← suite ctx ((i, .nat) :: current) body
    return (.forLoop i.getString! count loopBody, current)
  | .invoke name _ => throw s!"{name} needs an operator or synchronization contract (#85–#90)"
  | _ => throw "statement needs a TileLang control or operator contract (#85–#90)"
termination_by sizeOf stmt
decreasing_by all_goals decreasing_tactic

private def suite (ctx : Context) (regs : Registers) (stmts : List Statement) :
    Except String (List Stmt × Registers) := do
  match stmts with
  | [] => return ([], regs)
  | s :: rest =>
    let (head, next) ← statement ctx regs s
    let (tail, after) ← suite ctx next rest
    return (head :: tail, after)
termination_by sizeOf stmts
decreasing_by all_goals decreasing_tactic
end

private def extentOf : Value → Value → Except String Nat
  | .tuple [.integer n], .ident `T.int32 | .list [.integer n], .ident `T.int32 => pure n
  | _, _ => throw "parameter requires a literal one-dimensional int32 shape (#84)"

private def buffersOf (params : List Parameter) (prelude : List Statement) : Except String (List (Name × Nat)) := do
  let mut declared := []
  for stmt in prelude do
    let .annotate id shape dtype := stmt | throw "prelude requires static specialization (#84/#90)"
    if (declared.lookup id).isSome then throw "duplicate tensor declaration"
    declared := (id, ← extentOf shape dtype) :: declared
  let mut buffers := []
  for param in params do
    let (id, extent) ← match param with
      | .required id => do
        let some n := declared.lookup id | throw "untyped parameter requires a tensor declaration (#84)"
        declared := declared.filter (·.1 != id)
        pure (id, n)
      | .tensor id shape dtype => pure (id, ← extentOf shape dtype)
      | .optional .. => throw "parameter defaults require specialization (#84)"
    if (buffers.lookup id).isSome then throw "duplicate parameter"
    buffers := (id, extent) :: buffers
  unless declared.isEmpty do throw "extra tensor declaration in prelude"
  return buffers.reverse

private def entry (name : Name) (f : Procedure) (buffers : List (Name × Nat)) (result : Name)
    (launch : Statement) : Except String Lowered := do
  let .kernel grid [axis] body := launch | throw "expected one one-dimensional kernel"
  let [.pos (.integer count), .keyword `threads (.integer 1)] := grid
    | throw "core lowering requires a literal one-dimensional grid and threads=1"
  unless 0 < count && count < 2^31 do throw "grid extent must be a positive int32"
  unless (buffers.lookup result).isSome do throw "returned value must be a tensor parameter"
  unless (buffers.lookup axis).isNone do throw "grid binder shadows a tensor parameter"
  let (code, _) ← suite ⟨count, axis, buffers, result⟩ [] body
  let regions := buffers.map fun (name, _) => (⟨name.getString!⟩ : RegionName)
  return ⟨name, f.name, count, 1, buffers, result, ⟨regions, [⟨result.getString!⟩], code⟩⟩

/-- Direct eager outputs come from the return. A specialized factory's returned
prim_func and single JIT output index determine its core entry and output. -/
private def lower (p : Program) : Except String Lowered := do
  unless p.accepted do throw "program is outside its mode's accepted TileLang subset"
  unless p.mode == .tileLang && p.layouts.isEmpty do throw "mode or layout helper requires a lowering contract"
  match p.definition with
  | .direct f =>
    unless p.jit == some [] do throw "direct JIT options require specialization (#84/#90)"
    let .ret (.ident result) :: launch :: revPrelude := f.body.reverse
      | throw "expected a final return naming the output tensor"
    let buffers ← buffersOf f.params revPrelude.reverse
    entry f.name f buffers result launch
  | .factory factory macros prim _ =>
    unless factory.params.isEmpty && factory.body.isEmpty && macros.isEmpty do
      throw "factory parameters, static prelude or macro expansion require #84/#90"
    let some [.outputs [outIdx]] := p.jit
      | throw "factory requires a single explicit JIT output index"
    let [launch] := prim.body | throw "factory entry requires exactly one kernel"
    let buffers ← buffersOf prim.params []
    let some (result, _) := buffers[outIdx]? | throw "factory output index is outside the parameter list"
    entry factory.name prim buffers result launch

end CoreLower

/-- Lower one typed public quotation to the shared core and retain its launch
contract. Source acceptance alone does not discharge missing operator semantics. -/
def Program.lower (p : Program) : Except String Lowered := CoreLower.lower p

end VeriTile.TileLang
