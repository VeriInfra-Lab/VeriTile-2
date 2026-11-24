/-
Sequential spelling extensions for the target census (#77).

`tl.range` uses Python range bounds; `loop_unroll_factor` is only a compiler
hint (the documentation includes values below two as no unrolling). The target
census uses that hint with a literal value, and uses `step`.
Other range keywords remain parse failures. `pass` emits no statement.
Import this module and open `VeriTile.Dist.Frontend.TritonExt.Range` to enable
these spellings; importing alone leaves their tokens inactive.

Sources (accessed 2026-11-13):
- Triton v3.5.1 `range` documentation:
  https://github.com/triton-lang/triton/blob/v3.5.1/python/triton/language/core.py#L3212-L3253
- Python pass statement:
  https://docs.python.org/3/reference/simple_stmts.html#the-pass-statement
- Target uses at Triton-distributed 7908e4ea9010bb2238f9f05b28c904fd4b71c60a:
  `python/triton_dist/kernels/nvidia/moe_reduce_rs.py:582,663`,
  `python/triton_dist/kernels/nvidia/moe_reduce_ar.py:589` (range keywords);
  `python/triton_dist/kernels/nvidia/allgather_group_gemm.py:119` (named step).

The upstream expander is unchanged. These term elaborators rewrite the new
spellings before delegating to it; call-source rewriting precedes its checked
constexpr specialization. This module does not implement the other semantic
and constexpr gaps assigned to #77 by the census. Its source hooks cover
`with_triton_signature`, `with_triton_call` and source-procedure definitions;
other helper bindings and effects need the separately tracked source work.

The 2026-11-23 scan of the 18 Triton-distributed files still listed in
`scripts/census/targets.tsv` finds no kernel method-sum call, so that spelling
remains a parse failure; the upstream `tl.sum` operation is unchanged.
Five `with dl.simt_exec_region()` statements remain at the same pin:
`python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset.py:179,388`,
`python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset_inter_node.py:248`,
and `python/triton_dist/kernels/nvidia/common_ops.py:158,173`.
Their distributed SIMT-region semantics belong to #79, as recorded by the
#78 subset draft (PR #495); that support is not on this branch. They remain
rejected, not erased. This safe syntax slice does not complete #77.
- https://github.com/VeriInfra-Lab/VeriTile-2/issues/79
- https://github.com/VeriInfra-Lab/VeriTile-2/pull/495 (draft head d7800b1a3,
  `documents/dist/TritonDistSubset.md:22`, checked 2026-11-23)
-/
import VeriTile.Dist.Frontend.TritonExt.SourceHelperSyntax
import VeriTile.Triton.DSL.PythonFullConstructors

namespace VeriTile.Dist.Frontend.TritonExt.Range
open Lean Elab Term
open VeriTile.Triton.DSL

declare_syntax_cat tritonRangeArg
scoped syntax tritonExpr : tritonRangeArg
scoped syntax "step=" tritonExpr : tritonRangeArg
scoped syntax "loop_unroll_factor=" num : tritonRangeArg
scoped syntax (name := tritonRange) "for " ident " in " "tl.range(" tritonRangeArg,* ")"
  " { " tritonStmt* " }" : tritonStmt
scoped syntax (name := pythonRangeStep) "for " ident " in " "range(" tritonExpr ", " tritonExpr
  ", " "step=" tritonExpr ")" " { " tritonStmt* " }" : tritonStmt
-- The existing grammar tokenizes this literal prefix as one token.
scoped syntax (name := pythonRangeZeroStep) "for " ident " in " "range(0, " tritonExpr
  ", " "step=" tritonExpr ")" " { " tritonStmt* " }" : tritonStmt
scoped syntax (name := tritonPass) "pass" : tritonStmt

private partial def lowerRange (raw : Syntax) : MacroM Syntax := do
  let raw := raw.setArgs (← (raw.getArgs.filter (! ·.isOfKind ``tritonPass)).mapM lowerRange)
  match raw with
  | `(tritonStmt| for $i:ident in tl.range($args:tritonRangeArg,*) { $body:tritonStmt* }) =>
    let mut bounds : List (TSyntax `tritonExpr) := []
    let mut step : Option (TSyntax `tritonExpr) := none
    let mut unroll := Bool.false
    let mut keyword := Bool.false
    for arg in args.getElems do
      match arg with
      | `(tritonRangeArg| step=$value:tritonExpr) =>
        if step.isSome then Macro.throwErrorAt arg "duplicate tl.range step"
        step := some value
        keyword := Bool.true
      | `(tritonRangeArg| loop_unroll_factor=$_:num) =>
        if unroll then Macro.throwErrorAt arg "duplicate tl.range loop_unroll_factor"
        unroll := Bool.true
        keyword := Bool.true
      | `(tritonRangeArg| $value:tritonExpr) =>
        if keyword then Macro.throwErrorAt arg "positional tl.range bound after keyword"
        bounds := bounds ++ [value]
      | _ => Macro.throwUnsupported
    match bounds, step with
    | [stop], none => return (← `(tritonStmt| for $i:ident in range($stop) { $body* })).raw
    | [stop], some stride =>
      let start ← `(tritonExpr| 0)
      return (← `(tritonStmt| for $i:ident in range($start, $stop, $stride) { $body* })).raw
    | [start, stop], none =>
      return (← `(tritonStmt| for $i:ident in range($start, $stop) { $body* })).raw
    | [start, stop, stride], none | [start, stop], some stride =>
      return (← `(tritonStmt| for $i:ident in range($start, $stop, $stride) { $body* })).raw
    | _, _ => Macro.throwErrorAt raw "tl.range requires one to three bounds and at most one step"
  | `(tritonStmt| for $i:ident in range($start:tritonExpr, $stop:tritonExpr, step=$stride:tritonExpr) { $body:tritonStmt* }) =>
    return (← `(tritonStmt| for $i:ident in range($start, $stop, $stride) { $body* })).raw
  | `(tritonStmt| for $i:ident in range(0, $stop:tritonExpr, step=$stride:tritonExpr) { $body:tritonStmt* }) =>
    let start ← `(tritonExpr| 0)
    return (← `(tritonStmt| for $i:ident in range($start, $stop, $stride) { $body* })).raw
  | _ => return raw

@[term_elab VeriTile.Triton.DSL.tritonBlock]
def elaborateRange : TermElab := fun stx expected => do
  let lowered ← liftMacroM (lowerRange stx)
  if lowered == stx then throwUnsupportedSyntax
  elabTerm lowered expected

-- Rewrite before call-signature specialization so constexpr bounds take the
-- same path as the corresponding Python range.
@[term_elab VeriTile.Triton.DSL.CallSignature.withSignature,
  term_elab VeriTile.Triton.DSL.CallSignature.withCall,
  term_elab VeriTile.Triton.DSL.SourceProcedures.sourceParams,
  term_elab VeriTile.Triton.DSL.SourceProcedures.sourceProcedure]
def elaborateRangeSource : TermElab := fun stx expected => do
  let raw := stx.getArgs.back!
  let .ok source := RawSourceText.normalize raw.getAtomVal | throwUnsupportedSyntax
  let .ok parsed := Parser.runParserCategory (← getEnv) `term ("triton {\n" ++ source ++ "\n}")
    | throwUnsupportedSyntax
  let lowered ← liftMacroM (lowerRange parsed)
  if lowered == parsed then throwUnsupportedSyntax
  let `(triton { $body:tritonStmt* }) := lowered | throwUnsupportedSyntax
  let source := String.intercalate "\n" (body.toList.map (PythonFullConstructors.render ·.raw))
  let replacement := Syntax.atom raw.getHeadInfo ("{\n" ++ source ++ "\n}")
  elabTerm (stx.setArgs (stx.getArgs.set! (stx.getArgs.size - 1) replacement)) expected

end VeriTile.Dist.Frontend.TritonExt.Range
