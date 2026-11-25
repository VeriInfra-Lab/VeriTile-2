import Lean.Data.Json
import VeriTile.Interp.Mirror

/-! Trusted export of the executable mirror's scalar/tile fragment to the NumPy
runtime in scripts/interp/pyexec.py. Generated modules expose `run(memory, grid=(1,), registers=None)`.
The default for an unqualified real is binary32. The export and NumPy's
transcendental functions are outside the Lean adequacy theorem. The fragment
uses numeric registers and direct region loads/stores, with explicit errors
for unsupported operations, pointer forms and numerical modes. -/
namespace VeriTile.Interp.Carrier
open Lean (Json toJson)
open VeriTile.Triton

private abbrev Encoded := Except String Json

private def dtypeName : TileDType → Except String String
  | .real | .fp32 => pure "fp32"
  | .fp16 => pure "fp16"
  | .bf16 => pure "bf16"
  | .f8e4 => pure "f8e4"
  | .f8e5 => pure "f8e5"
  | .nat => pure "nat"
  | .int => pure "int"
  | .bool => pure "bool"
  | .ptr | .blockPtr => throw "NumPy export requires a numeric or Boolean register"

private def array (xs : List Json) := Json.arr xs.toArray
private def typedNode (tag dtype : String) (sh : TileShape) (args : List Encoded) : Encoded := do
  return array ([toJson tag,toJson dtype,toJson sh] ++ (← args.mapM id))

private def exprNode (tag : String) (d : TileDType) (sh : TileShape) (args : List Encoded) : Encoded := do
  typedNode tag (← dtypeName d) sh args

private def stmtNode (tag : String) (args : List Encoded) : Encoded := do
  return array (toJson tag :: (← args.mapM id))

private def literal (d : TileDType) (n : Int) (den : Nat := 1) : Encoded :=
  exprNode "const" d [] [pure (toJson n), pure (toJson den)]

/-- A mirror broadcast can insert a dimension inside a tile. Insert those
singleton axes before NumPy applies trailing-dimension broadcasting. -/
private def aligned {a b out : TileShape} (bc : Broadcast a b out) : TileShape × TileShape :=
  match bc with
  | .nil => ([], [])
  | .scalarL => (List.replicate b.length 1, b)
  | .scalarR => (a, List.replicate a.length 1)
  | .consSame sub | .consL sub | .consR sub =>
    let (xs,ys) := aligned sub
    (a.headD 1 :: xs, b.headD 1 :: ys)
  | .leadL sub =>
    let (xs,ys) := aligned sub
    (1 :: xs, b.headD 1 :: ys)
  | .leadR sub =>
    let (xs,ys) := aligned sub
    (a.headD 1 :: xs, 1 :: ys)

private def reshapeArg (d : TileDType) (before after : TileShape) (x : Encoded) : Encoded :=
  if before = after then x else exprNode "reshape" d after [x]

private def binary {a b out : TileShape} (tag : String) (result left right : TileDType)
    (bc : Broadcast a b out) (x y : Encoded) : Encoded :=
  let (xs,ys) := aligned bc
  exprNode tag result out [reshapeArg left a xs x, reshapeArg right b ys y]

private def opType {d s} (_ : QOp d s) := d

private def loadNode (d : TileDType) (s : TileShape) (name : String) (off : Encoded)
    (mask : Except String (Json × Json)) : Encoded := do
  let (cond, other) ← mask
  exprNode "load" d s [pure (toJson name),off,pure cond,pure other,pure (toJson "none")]

private def dotNode (d : TileDType) (s : TileShape) (opts : DotOptions) (x y : Encoded) : Encoded := do
  unless (d = .fp32 ∨ d = .real) ∧ (opts.outDType.isNone ∨ opts.outDType = some d) ∧
      opts.allowTF32 != some true ∧ (opts.inputPrecision.isNone ∨ opts.inputPrecision = some "ieee") ∧
      opts.maxNumImpreciseAcc.isNone do throw "NumPy dot requires IEEE fp32 inputs and accumulation"
  exprNode "dot" d s [x,y]

private def encodeOp {d : TileDType} {s : TileShape} (term : QOp d s) : Encoded :=
  match term with
  | .const q | .constFloat _ q => literal d q.num q.den
  | .constNat n => literal d n
  | .constInt n => literal d n
  | .constBool b => literal d b.toNat
  | .negInf => exprNode "negInf" d s []
  | .minPosInf x => exprNode "minimumFloat" d s [encodeOp x,exprNode "posInf" d s []]
  | .programId ax => exprNode "programId" d s [pure (toJson ax)]
  | .numPrograms ax => exprNode "numPrograms" d s [pure (toJson ax)]
  | .arange n => exprNode "arange" d s [pure (toJson n)]
  | .ref _ _ name => exprNode "ref" d s [pure (toJson name)]
  | .broadcast x _ | .full _ x => exprNode "broadcast" d s [encodeOp x]
  | .withPrecision .real .fp32 x | .withPrecision .fp32 .fp32 x => encodeOp x
  | .castFloat _ _ x | .natToReal x | .intToReal x
  | .castNatToInt x | .castIntToNat x => exprNode "cast" d s [encodeOp x]
  | .negFloat _ x => exprNode "neg" d s [encodeOp x]
  | .absFloat _ x => exprNode "abs" d s [encodeOp x]
  | .libdeviceExp x => exprNode "exp" d s [encodeOp x]
  | .libdeviceLog x => exprNode "log" d s [encodeOp x]
  | .libdeviceExpm1 x => exprNode "expm1" d s [encodeOp x]
  | .libdeviceLog1p x => exprNode "log1p" d s [encodeOp x]
  | .libdeviceTanh x => exprNode "tanh" d s [encodeOp x]
  | .libdeviceRsqrt x => exprNode "rsqrt" d s [encodeOp x]
  | .exp x => exprNode "exp" d s [encodeOp x]
  | .exp2 x => exprNode "exp2" d s [encodeOp x]
  | .log x => exprNode "log" d s [encodeOp x]
  | .log2 x => exprNode "log2" d s [encodeOp x]
  | .sqrt x => exprNode "sqrt" d s [encodeOp x]
  | .rsqrt x => exprNode "rsqrt" d s [encodeOp x]
  | .tanh x => exprNode "tanh" d s [encodeOp x]
  | .sin x => exprNode "sin" d s [encodeOp x]
  | .cos x => exprNode "cos" d s [encodeOp x]
  | .tan x => exprNode "tan" d s [encodeOp x]
  | .atan x => exprNode "atan" d s [encodeOp x]
  | .cosh x => exprNode "cosh" d s [encodeOp x]
  | .sinh x => exprNode "sinh" d s [encodeOp x]
  | .sigmoid x => exprNode "sigmoid" d s [encodeOp x]
  | .boolNot x => exprNode "boolNot" d s [encodeOp x]
  | .add _ bc x y => binary "add" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .sub _ bc x y => binary "sub" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .mul _ bc x y => binary "mul" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .div _ bc x y => binary "div" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .floorDiv _ bc x y => binary "floorDiv" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .mod _ bc x y => binary "mod" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .lt _ bc x y => binary "lt" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .le _ bc x y => binary "le" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .eq _ bc x y => binary "eq" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .gt _ bc x y => binary "gt" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .ge _ bc x y => binary "ge" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .ne _ bc x y => binary "ne" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .maximumFloat _ bc x y => binary "maximumFloat" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .minimumFloat _ bc x y => binary "minimumFloat" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .max2 bc x y => binary "max2" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .pow bc x y => binary "pow" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .boolAnd bc x y => binary "boolAnd" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .boolOr bc x y => binary "boolOr" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .divRN bc x y => binary "div" d (opType x) (opType y) bc (encodeOp x) (encodeOp y)
  | .reduceMin ax keep x => exprNode "reduceMin" d s [pure (toJson ax.val),pure (toJson keep),encodeOp x]
  | .reduceMax ax keep x => exprNode "reduceMax" d s [pure (toJson ax.val),pure (toJson keep),encodeOp x]
  | .reduceSum ax keep x => exprNode "reduceSum" d s [pure (toJson ax.val),pure (toJson keep),encodeOp x]
  | .reduceSumTyped _ ax keep x => exprNode "reduceSum" d s [pure (toJson ax.val),pure (toJson keep),encodeOp x]
  | .reduceMaxTyped _ ax keep x => exprNode "reduceMax" d s [pure (toJson ax.val),pure (toJson keep),encodeOp x]
  | .reduceSumBool ax keep x => exprNode "reduceSum" d s [pure (toJson ax.val),pure (toJson keep),encodeOp x]
  | .reduceMaxNat ax keep x => exprNode "reduceMax" d s [pure (toJson ax.val),pure (toJson keep),encodeOp x]
  | .reduceMaxInt ax keep x => exprNode "reduceMax" d s [pure (toJson ax.val),pure (toJson keep),encodeOp x]
  | .dot x y opts => dotNode d s opts (encodeOp x) (encodeOp y)
  | .dotTyped .fp32 .fp32 .fp32 x y opts => dotNode d s opts (encodeOp x) (encodeOp y)
  | .where c x y => exprNode "where" d s [encodeOp c,encodeOp x,encodeOp y]
  | .ite c x y => exprNode "ite" d s [encodeOp c,encodeOp x,encodeOp y]
  | .reshape _ x => exprNode "reshape" d s [encodeOp x]
  | .expandDim _ x => exprNode "reshape" d s [encodeOp x]
  | .transpose x => exprNode "transpose" d s [encodeOp x]
  | .load _ (.region region off) .none _ =>
    loadNode d s region.name (encodeOp off) (pure (.null,.null))
  | .load _ (.region region off) (.mask cond) _ =>
    loadNode d s region.name (encodeOp off) (do return (← encodeOp cond,.null))
  | .load _ (.region region off) (.maskOther cond other) _ =>
    loadNode d s region.name (encodeOp off) (do return (← encodeOp cond,← encodeOp other))
  | _ => throw "unsupported NumPy mirror operation or address form"
termination_by structural term

private def encodeMask : {d : TileDType} → {s : TileShape} → QMaskOpt d s → Except String (Json × Json)
  | _, _, .none => pure (.null,.null)
  | _, _, .mask x => do return (← encodeOp x,.null)
  | _, _, .maskOther x y => do return (← encodeOp x,← encodeOp y)


private def computeName : ComputeDType → String
  | .uint32 => "uint32" | .int32 => "int32" | .fp32 => "fp32" | .fp64 => "fp64"

private def wordBits : {d : ComputeDType} → ComputeCarrier d → Nat
  | .uint32, v => v.bits.toNat | .int32, v => v.bits.toNat
  | .fp32, v => v.bits.toNat | .fp64, v => v.bits.toNat

private def encodeCompute {d : ComputeDType} {s : TileShape} (term : QComputeOp d s) : Encoded :=
  match term with
  | .alg .fp32 e => encodeOp e
  | .const v => typedNode "bits" (computeName d) s [pure (toJson (wordBits v))]
  | .load .fp32 (.region r off) m _ => loadNode .fp32 s r.name (encodeOp off) (encodeMask m)
  | .bitcast src dst _ x => typedNode "bitcast" (computeName dst) s [pure (toJson (computeName src)),encodeCompute x]
  | .full _ e => typedNode "broadcast" (computeName d) s [encodeCompute e]
  | _ => throw "unsupported NumPy compute precision, bit pattern or address form"

private def fused {a b ab c out : TileShape} (d : TileDType) (abBC : Broadcast a b ab)
    (outBC : Broadcast ab c out) (x y z : Encoded) : Encoded := do
  unless d = .real ∨ d = .fp32 do throw "NumPy fused multiply-add requires fp32"
  let (xs,ys) := aligned abBC
  let (abs,cs) := aligned outBC
  let atProduct := fun sh rs v =>
    reshapeArg d ab abs (exprNode "broadcast" d ab [reshapeArg d sh rs v])
  exprNode "fma" d out [atProduct a xs x, atProduct b ys y, reshapeArg d c cs z]

private def encodeExpr {d : TileDType} {s : TileShape} (term : QExpr d s) : Encoded :=
  match term with
  | .alg x => encodeOp x
  | .compute x => encodeCompute x
  | .isFinite .fp32 x => exprNode "isFinite" .bool s [exprNode "cast" .fp32 s [encodeExpr x]]
  | .fma .fp32 abBC outBC x y z =>
    fused .real abBC outBC (encodeExpr x) (encodeExpr y) (encodeExpr z)
  | .fmaTyped _ abBC outBC x y z =>
    fused d abBC outBC (encodeExpr x) (encodeExpr y) (encodeExpr z)
  | _ => throw "unsupported NumPy compute expression"

private def writeNode {d s} (address : QMemAccess d s) (v : Encoded) (m : QMaskOpt d s) : Encoded := do
  let .region r off := address | throw "NumPy stores require a direct region address"
  let activeMask ← match m with
    | .none => pure Json.null
    | .mask x | .maskOther x _ => encodeOp x
  stmtNode "store" [pure (toJson r.name),encodeOp off,v,pure activeMask]

private def assignNode (name : String) (v : Encoded) := stmtNode "assign" [pure (toJson name),v]
private def block (stmts : Except String (List Json)) : Encoded := array <$> stmts

private def loopNode (name : String) (start stop stride body : Encoded) :=
  stmtNode "for" [pure (toJson name),start,stop,stride,body]

mutual
private def encodeAlgStmt : QAlgStmt → Encoded
  | .assign _ _ name v => assignNode name (encodeOp v)
  | .store _ _ addr v m => writeNode addr (encodeOp v) m
  | .forLoop name n body => loopNode name (literal .nat 0) (literal .nat n) (literal .nat 1) (block (encodeAlgList body))
  | .forRange name lo hi stride body =>
    loopNode name (literal .nat lo) (literal .nat hi) (literal .nat stride) (block (encodeAlgList body))
  | .forRangeDyn name lo hi stride body | .forRangeInt name lo hi stride body =>
    loopNode name (encodeOp lo) (encodeOp hi) (encodeOp stride) (block (encodeAlgList body))
  | .ifThen cond yes => stmtNode "if" [encodeOp cond,block (encodeAlgList yes),pure (array [])]
  | .ifThenElse cond yes no => stmtNode "if" [encodeOp cond,block (encodeAlgList yes),block (encodeAlgList no)]
  | _ => throw "unsupported NumPy statement (atomic operation or effect)"
termination_by structural st => st

private def encodeAlgList : List QAlgStmt → Except String (List Json)
  | [] => pure []
  | x :: xs => do
    return (← encodeAlgStmt x) :: (← encodeAlgList xs)
termination_by structural xs => xs
end

mutual
private def encodeStmt : QStmt → Encoded
  | .assign _ _ name v => assignNode name (encodeExpr v)
  | .store _ _ addr v m => writeNode addr (encodeExpr v) m
  | .forLoop name n body => loopNode name (literal .nat 0) (literal .nat n) (literal .nat 1) (block (encodeList body))
  | .forRange name lo hi stride body =>
    loopNode name (literal .nat lo) (literal .nat hi) (literal .nat stride) (block (encodeList body))
  | .forRangeDyn name lo hi stride body | .forRangeInt name lo hi stride body =>
    loopNode name (encodeOp lo) (encodeOp hi) (encodeOp stride) (block (encodeList body))
  | .ifThen cond yes => stmtNode "if" [encodeOp cond,block (encodeList yes),pure (array [])]
  | .ifThenElse cond yes no => stmtNode "if" [encodeOp cond,block (encodeList yes),block (encodeList no)]
  | .alg x => encodeAlgStmt x
  | _ => throw "unsupported NumPy statement (atomic operation or effect)"
termination_by structural st => st

private def encodeList : List QStmt → Except String (List Json)
  | [] => pure []
  | x :: xs => do
    return (← encodeStmt x) :: (← encodeList xs)
termination_by structural xs => xs
end

/-- Export an actual mirror kernel to an importable Python program. Region and
register names are JSON data and cannot contribute Python source syntax. -/
def exportPython : QKernel → Except String String
  | .mk inputs outputs body => do
    let plan := Json.mkObj [("inputs",toJson (inputs.map Region.name)),("outputs",toJson (outputs.map Region.name)),
      ("body",← block (encodeList body))]
    let quoted := (toJson plan.compress).compress
    return "import json\nfrom scripts.interp.pyexec import run_kernel\n\nPROGRAM = json.loads(" ++
      quoted ++ ")\n\ndef run(memory, grid=(1,), registers=None):\n    return run_kernel(PROGRAM, memory, grid, registers)\n"

end VeriTile.Interp.Carrier
