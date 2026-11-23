import Lean.Data.Json
import VeriTile.Interp.Carrier.Symbolic

namespace VeriTile.Interp.Symbolic
open Lean (Json toJson)
open VeriTile.Triton VeriTile.Triton.FP VeriTile.Triton.FP.Equational

private def dtype : FloatDType → String
  | .real => "real" | .fp32 => "fp32" | .fp16 => "fp16" | .bf16 => "bf16"
  | .f8e4 => "f8e4" | .f8e5 => "f8e5"

private def precision (p : Option ComputeDType) : Json := toJson (p.map fun
  | .uint32 => "uint32" | .int32 => "int32" | .fp32 => "fp32" | .fp64 => "fp64")

private def indexPrecision : IndexComputePrecision → String
  | .fp32 => "fp32" | .fp64 => "fp64"

private def binaryName : Structural.Binary → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .max => "max" | .pow => "pow"

private def unaryTags : Structural.Unary → List Json
  | .neg d => ["neg",dtype d] | .abs d => ["abs",dtype d]
  | .exp => ["exp"] | .libdeviceExp => ["libdeviceExp"] | .libdeviceLog => ["libdeviceLog"]
  | .libdeviceExpm1 => ["libdeviceExpm1"] | .libdeviceLog1p => ["libdeviceLog1p"]
  | .libdeviceTanh => ["libdeviceTanh"] | .exp2 => ["exp2"] | .log => ["log"] | .log2 => ["log2"]
  | .sigmoid => ["sigmoid"] | .sqrt => ["sqrt"] | .rsqrt => ["rsqrt"] | .libdeviceRsqrt => ["libdeviceRsqrt"]
  | .tanh => ["tanh"] | .sin => ["sin"] | .cos => ["cos"] | .tan => ["tan"] | .atan => ["atan"]
  | .cosh => ["cosh"] | .sinh => ["sinh"] | .erf => ["erf"] | .minPosInf => ["minPosInf"]

private def scanName : ScanOp → String
  | .sum => "sum" | .prod => "prod" | .max => "max" | .min => "min"

private def node (kind : String) (tags : List Json) (children : List Json) : Json :=
  .arr #[.str kind,toJson tags,toJson children]

private def options (o : DotOptions) : Json :=
  let out := o.outDType.map fun
    | .real => "real" | .fp32 => "fp32" | .fp16 => "fp16" | .bf16 => "bf16"
    | .f8e4 => "f8e4" | .f8e5 => "f8e5" | .nat => "nat" | .int => "int"
    | .bool => "bool" | .ptr => "ptr" | .blockPtr => "blockPtr"
  Json.arr #[toJson out,toJson o.allowTF32,toJson o.inputPrecision,toJson o.maxNumImpreciseAcc]

private def callNode : Call → List Json → Json
  | .fma p => node "fma" [indexPrecision p]
  | .fmaTyped d => node "fmaTyped" [dtype d]
  | .atomicAdd d => node "atomicAdd" [dtype d]
  | .powi p n => node "libdevicePowi" [precision p,toJson n]
  | .minimum p d => node "minimum" [precision p,dtype d]
  | .divRN => node "divRN" []
  | .float8E5Bits d bits => node "float8E5Bits" [dtype d,toJson bits.val]
  | .reduction op typed p d shape axis keep =>
    let kind := (match op with | .sum => "reduceSum" | .max => "reduceMax"
                                | .min => "reduceMin" | .prod => "reduceProd") ++ (if typed then "Typed" else "")
    node kind [precision p,dtype d,toJson shape,toJson axis,toJson keep]
  | .scan p op dir shape axis => node "scan" [precision p,scanName op,
      (match dir with | .forward => "forward" | .reverse => "reverse" : String),toJson shape,toJson axis]
  | .dot mode p l r o opts k =>
    let kind := match mode with
      | .dot => "dot" | .dotWithOptions => "dotWithOptions" | .dotTyped => "dotTyped" | .dotAcc => "dotAcc"
    node kind [precision p,dtype l,dtype r,dtype o,options opts,toJson k]

private def symbolNode (s : Symbol) (args : List Json) : Except String Json := do
  match s with
  | .negInf => return node "negInf" [] args
  | .binary p d op => return node "binary" [precision p,dtype d,binaryName op] args
  | .unary p op => return node "unary" (precision p :: unaryTags op) args
  | .cast p s d => return node "cast" [precision p,dtype s,dtype d] args
  | .fromNat p n => return node "fromNat" [precision p,toJson n] args
  | .fromInt p n => return node "fromInt" [precision p,toJson n] args
  | .fp32Bits b => return node "fp32Bits" [toJson b.bits.toNat] args
  | .fp32Load => return node "fp32Load" [] args
  | .literal .. => throw "foreign real literal has no computable rational preimage"
  | .reduceMax .. => throw "foreign full-tile reduction; expected a symbolic carrier lane"

mutual
private def tree : Expr → Except String Json
  | .leaf a => atomTree a
  | .app s args => do symbolNode s (← args.mapM tree)
private def atomTree : Atom → Except String Json
  | .literal p d q => pure (node "literal" [precision p,dtype d,toJson q.num,toJson q.den] [])
  | .call op args => do return callNode op (← args.mapM tree)
end

/-- A complete versioned document in output-element order. -/
def exportTrees (values : List Expr) : Except String Json := do
  return Json.mkObj [("version",1),("outputs",toJson (← values.mapM tree))]

def writeTrees (path : System.FilePath) (values : List Expr) : IO Unit := do
  let json ← IO.ofExcept (exportTrees values)
  IO.FS.writeFile path (json.compress ++ "\n")

end VeriTile.Interp.Symbolic
