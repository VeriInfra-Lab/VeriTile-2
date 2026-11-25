import Lean

/-! Closed source syntax for the A3.1 freeze draft. The public quotation returns
the concrete syntax tree for the parameter, operator and event elaborators.
Braces delimit Python suites; semicolons separate their statements. -/
namespace VeriTile.TileLang
open Lean Parser

/-- The source tree retains the grammar production, literal spelling and operands. -/
inductive Source where
  | token (spelling : String)
  | name (id : Name)
  | node (production : Name) (children : List Source)
  deriving Repr, BEq, Inhabited

declare_syntax_cat tlExpr
declare_syntax_cat tlArg
declare_syntax_cat tlIndex
declare_syntax_cat tlPlace
declare_syntax_cat tlTarget
declare_syntax_cat tlStmt
declare_syntax_cat tlSuite
declare_syntax_cat tlIter
declare_syntax_cat tlMacro
declare_syntax_cat tlParam
declare_syntax_cat tlTensor
declare_syntax_cat tlOuter
declare_syntax_cat tlStatic
declare_syntax_cat tlBinding
declare_syntax_cat tlCfg

private def plainSpelling : Syntax → Bool
  | .ident _ raw n _ => raw.toString == n.toString
  | _ => false

private def pyName (n : Name) : Bool :=
  match n with
  | .str .anonymous s => (s.toList.head?.any fun c => c.isAlpha || c == '_') &&
      s.toList.all (fun c => c.isAlphanum || c == '_') &&
      !(["if", "else", "return", "import", "from", "def", "for", "with", "as",
         "True", "False", "None", "lambda", "while", "yield", "pass", "class",
         "break", "continue", "assert", "and", "or", "not", "in", "T", "math",
         "tilelang", "global", "nonlocal", "elif", "try", "except", "finally",
         "async", "await", "del", "is", "raise"] : List String).contains s
  | _ => false

/-- Local Python identifiers include Lean keywords such as `by`. Qualified
identifiers cannot slip through as unregistered primitives or local macros. -/
def tlName : Parser := rawIdentNoAntiquot >>
  checkStackTop (fun s => plainSpelling s && pyName s.getId) "expected an unqualified TileLang source identifier"

private def valueName (n : Name) : Bool :=
  pyName n || match n with
  | .str base field => (pyName base && (field == "dtype" || field == "shape")) ||
      (base == `T && ["float16", "float32", "bfloat16", "int32", "int64", "bool"].contains field) ||
      n == `T.GemmWarpPolicy.FullRow
  | _ => false

def tlValueName : Parser := rawIdentNoAntiquot >>
  checkStackTop (fun s => plainSpelling s && valueName s.getId) "unsupported TileLang value or attribute"

syntax tlValueName : tlExpr
syntax num : tlExpr
syntax scientific : tlExpr
syntax str : tlExpr
syntax "True" : tlExpr
syntax "False" : tlExpr
syntax "(" tlExpr ")" : tlExpr
syntax "(" tlExpr "," tlExpr,*,? ")" : tlExpr
syntax "[" tlExpr,*,? "]" : tlExpr
syntax:max tlName noWs "[" tlIndex,+,? "]" : tlExpr
syntax tlExpr : tlIndex
syntax (tlExpr)? ":" (tlExpr)? : tlIndex
syntax:75 "-" tlExpr:75 : tlExpr
syntax:80 tlExpr:81 " ** " tlExpr:75 : tlExpr
syntax:70 tlExpr:70 " * " tlExpr:71 : tlExpr
syntax:70 tlExpr:70 " / " tlExpr:71 : tlExpr
syntax:70 tlExpr:70 " // " tlExpr:71 : tlExpr
syntax:70 tlExpr:70 " % " tlExpr:71 : tlExpr
syntax:65 tlExpr:65 " + " tlExpr:66 : tlExpr
syntax:65 tlExpr:65 " - " tlExpr:66 : tlExpr
syntax:56 tlExpr:56 " ^ " tlExpr:57 : tlExpr
syntax:50 tlExpr:51 " < " tlExpr:51 : tlExpr
syntax:50 tlExpr:51 " > " tlExpr:51 : tlExpr
syntax:50 tlExpr:51 " <= " tlExpr:51 : tlExpr
syntax:50 tlExpr:51 " >= " tlExpr:51 : tlExpr
syntax:50 tlExpr:51 " == " tlExpr:51 : tlExpr
syntax:50 tlExpr:51 " != " tlExpr:51 : tlExpr
syntax:40 tlExpr:41 " if " tlExpr:41 " else " tlExpr:40 : tlExpr

syntax tlExpr : tlArg
syntax (name := kw) tlName "=" tlExpr : tlArg
syntax (name := primitive) rawIdentNoAntiquot "(" tlArg,*,? ")" : tlExpr
syntax (name := layout) "T.Layout" "(" tlExpr "," "lambda" tlName,+ ":" tlExpr ")" : tlExpr
syntax "{" tlName ":" tlExpr (",")? "}" : tlExpr

syntax tlName : tlPlace
syntax (name := indexedTarget) tlName noWs "[" tlIndex,+,? "]" : tlPlace
syntax tlPlace : tlTarget
syntax tlName "," tlName,+ : tlTarget
syntax tlName : tlParam
syntax (name := defaultParam) tlName "=" tlExpr : tlParam
syntax tlName ":" "T.Tensor" "(" tlExpr "," tlExpr ")" : tlTensor
syntax tlTensor : tlParam

syntax (name := binding) tlTarget "=" tlExpr : tlBinding
syntax tlBinding : tlStmt
syntax tlTensor : tlStmt
syntax tlPlace "+=" tlExpr : tlStmt
syntax tlPlace "*=" tlExpr : tlStmt
syntax tlPlace "-=" tlExpr : tlStmt
syntax tlPlace "/=" tlExpr : tlStmt
syntax (name := operation) rawIdentNoAntiquot "(" tlArg,*,? ")" : tlStmt
syntax "return" tlExpr : tlStmt
syntax (name := branch) "if" tlExpr ":" tlSuite ("else" ":" tlSuite)? : tlStmt
syntax (name := loop) "for" tlName,+ "in" tlIter ":" tlSuite : tlStmt
syntax (name := loopCall) rawIdentNoAntiquot "(" tlArg,*,? ")" : tlIter
syntax (name := kernel) "with" "T.Kernel" "(" tlArg,+,? ")" "as" tlName ":" tlSuite : tlStmt
syntax (name := grid) "with" "T.Kernel" "(" tlArg,+,? ")" "as" "(" tlName,+,? ")" ":" tlSuite : tlStmt
syntax (name := role) "with" "T.ws" "(" tlExpr ")" ":" tlSuite : tlStmt
syntax "{" sepBy1(tlStmt, ";") (";")? "}" : tlSuite
syntax (name := helper) "@T.macro" "def" tlName "(" tlName,*,? ")" ":" tlSuite : tlMacro

-- The outer configuration admits literals and source names in defaults and
-- expressions; only these binding/assert/constexpr-branch statements can run there.
syntax tlBinding : tlStatic
syntax (name := staticBranch) "if" tlExpr ":" "{" sepBy1(tlStatic, ";") (";")? "}" ("else" ":" "{" sepBy1(tlStatic, ";") (";")? "}")? : tlStatic
syntax "assert" tlExpr ("," str)? : tlStatic
syntax (name := outputs) "out_idx" "=" "[" num,+,? "]" : tlCfg
syntax (name := config) "pass_configs" "=" "{" (str <|> rawIdentNoAntiquot) ":" ("True" <|> "False") "}" : tlCfg
syntax (name := factory) ("@tilelang.jit" ("(" tlCfg,+,? ")")?)?
  "def" tlName "(" tlParam,*,? ")" ":" "{"
  (tlStatic ";")* (tlMacro ";")*
  "@T.prim_func" "def" tlName "(" tlTensor,*,? ")" ":" tlSuite ";"
  "return" tlName "}" : tlOuter
syntax (name := eager) "@tilelang.jit" ("(" tlCfg,+,? ")")?
  "def" tlName "(" tlParam,*,? ")" ":" tlSuite : tlOuter

-- Compare complete call shapes. Keyword order is immaterial, while duplicate
-- keys, a positional operand after a keyword, and new keyword combinations fail.
private def fits (args : Syntax) (n : Nat) (keys : List Name := []) : Bool := Id.run do
  let xs := args.getSepArgs
  let positions := xs.takeWhile (fun x => !x.isOfKind ``kw)
  let tailArgs := xs.extract positions.size xs.size
  let actual := tailArgs.map (fun x => x[0].getId)
  return positions.size == n && tailArgs.all (·.isOfKind ``kw) &&
    actual.size == keys.length && keys.all (fun k => actual.contains k)

/-- The same identifier cannot introduce either an unregistered T.* call or
an arbitrary Python call. The only dynamic names are earlier declared macros. -/
private def validCall (k n : Name) (args : Syntax) (macros : List (Name × Nat)) : Bool :=
  if k == ``loopCall then
    match n with
    | `T.Parallel => fits args 1 || fits args 2
    | `T.Pipelined => fits args 1 [`num_stages] || fits args 2 [`num_stages]
    | `range => fits args 1
    | _ => false
  else if k == ``operation then
    match n with
    | `T.clear | `T.use_swizzle | `T.annotate_layout => fits args 1
    | `T.copy | `T.fill | `T.atomic_add => fits args 2
    | `T.tma_copy => fits args 2 [`barrier]
    | `T.mbarrier_arrive => fits args 0 [`mbarrier]
    | `T.mbarrier_wait_parity => fits args 0 [`mbarrier, `parity]
    | `T.reduce_sum => fits args 3 || fits args 2 [`dim]
    | `T.reduce_max => fits args 2 [`dim, `clear]
    | `T.gemm => [[], [`policy], [`transpose_A], [`transpose_B], [`transpose_B, `policy]].any
        (fun keys => fits args 3 keys)
    | _ => macros.any fun (m, arity) => n == m && fits args arity
  else
    match n with
    | `T.alloc_fragment | `T.alloc_shared => fits args 2 || fits args 1 [`dtype]
    | `T.ceildiv | `T.max | `T.min | `T.empty | `T.floordiv => fits args 2
    | `T.exp2 | `T.const | `T.infinity | `T.alloc_barrier | `T.log2 | `math.ceil => fits args 1
    | `T.if_then_else => fits args 3
    | _ => macros.any fun (m, arity) => n == m && fits args arity

private partial def checkedTree (stx : Syntax) (macros : List (Name × Nat)) : Bool := Id.run do
  let k := stx.getKind
  if k == ``primitive || k == ``operation || k == ``loopCall then
    unless plainSpelling stx[0] && validCall k stx[0].getId stx[2] macros do return false
  if k == ``loop then
    let iter := stx[3]
    let arity := if iter[0].getId == `T.Parallel then iter[2].getSepArgs.size else 1
    unless stx[1].getSepArgs.size == arity do return false
  if k == ``kernel || k == ``grid then
    let grids := if k == ``kernel then 1 else stx[7].getSepArgs.size
    unless (1 ≤ grids && grids ≤ 3) &&
      (fits stx[3] grids || fits stx[3] grids [`threads]) do return false
  return stx.getArgs.all (fun x => checkedTree x macros)

private def validDefaults (s : Syntax) : Bool :=
  (s.find? fun x => x.isOfKind ``primitive &&
    !([`math.ceil, `T.ceildiv, `T.const, `T.min, `T.max] : List Name).contains x[0].getId).isNone &&
  (s.find? (fun x => x.isOfKind ``layout || x.isOfKind ``indexedTarget)).isNone

private def validConfigs (s : Syntax) : Bool := Id.run do
  let entries := (s.find? fun x => x.getArgs.any (·.isOfKind ``config) ||
    x.getArgs.any (·.isOfKind ``outputs))
  let some entries := entries | return true
  let kinds := entries.getSepArgs.map Syntax.getKind
  unless kinds.toList.Nodup do return false
  let some c := entries.getSepArgs.find? (·.isOfKind ``config) | return true
  return c[3].isStrLit? == some "tl.disable_warp_specialized" ||
    [`tilelang.PassConfigKey.TL_ENABLE_FAST_MATH, `tilelang.PassConfigKey.TL_DISABLE_WARP_SPECIALIZED].contains c[3].getId

private def distinctParams (xs : Syntax) : Bool := Id.run do
  let names := xs.getSepArgs.map fun p => ((p.find? Syntax.isIdent).map Syntax.getId).getD .anonymous
  let ps := xs.getSepArgs
  let withoutDefault := ps.takeWhile (fun p => !p.isOfKind ``defaultParam)
  return names.toList.Nodup && (ps.extract withoutDefault.size ps.size).all (·.isOfKind ``defaultParam)

private def validOuter (s : Syntax) : Bool := Id.run do
  unless validConfigs s && distinctParams s[4] && validDefaults s[4] && checkedTree s[4] [] do return false
  if s.isOfKind ``eager then
    return (s[8].find? (fun x => x.isOfKind ``kernel || x.isOfKind ``grid)).isSome && checkedTree s []
  -- Factory child nodes follow the production above: outer bindings and
  -- macros, prim_func name/parameters/suite, and the returned name.
  unless s.isOfKind ``factory && s[12].getId == s[20].getId && distinctParams s[14] do return false
  let mut macros : List (Name × Nat) := []
  for g in s[9].getArgs do
    let h := g[0]
    let name := h[2].getId
    if macros.any (·.1 == name) || name == s[12].getId ||
        !distinctParams h[4] || !checkedTree h macros then return false
    macros := (name, h[4].getSepArgs.size) :: macros
  return validDefaults s[8] && checkedTree s[8] [] && checkedTree s[14] [] && checkedTree s[17] macros

/-- The whitelist and local macro binding check run inside the parser, before
a quoted term can be elaborated. -/
def checkedOuter : Parser := categoryParser `tlOuter 0 >>
  checkStackTop validOuter "unsupported TileLang call, arguments, kernel binding or macro"

syntax (name := quotation) "tilelang" "{" checkedOuter "}" : term

private partial def quoteSource (s : Syntax) : MetaM Expr := do
  match s with
  | .atom _ text => return mkApp (mkConst ``Source.token) (toExpr text)
  | .ident _ _ n _ => return mkApp (mkConst ``Source.name) (toExpr n)
  | .node _ k xs =>
    let children ← xs.toList.mapM quoteSource
    return mkApp2 (mkConst ``Source.node) (toExpr k) (← Meta.mkListLit (mkConst ``Source) children)
  | .missing => throwError "missing TileLang syntax"

@[term_elab quotation] def elabTileLang : Elab.Term.TermElab := fun stx _ => quoteSource stx[2]

-- These cases exercise the public term parser. An elaborator error would
-- accept the parse and fail these regressions.
private def sample (body : String) : String :=
  "tilelang { @tilelang.jit def demo(X, Y): {with T.Kernel(1, threads=32) as b: {" ++ body ++ "}}}"

run_cmd
  let env ← getEnv
  for body in ["T.copy(X, Y)", "for i in T.Pipelined(2, num_stages=k): {Y[i] = X[i] + 1}",
    "T.mbarrier_wait_parity(parity=(k // n) % n, mbarrier=X[b])",
    "with T.ws(1): {T.tma_copy(X[:, :], Y[:, :], barrier=X[b])}",
    "L = T.Layout(X.shape, lambda i, j: [j, i]); T.annotate_layout({X: L})"] do
    if let .error e := Parser.runParserCategory env `term (sample body) then
      throwError "expected TileLang syntax to parse: {body}: {e}"
  for body in ["T.wgmma(X, Y)", "T.tcgen05(X)", "T.fence_proxy_async()",
    "T.gemm(X, Y, X, future_kw=True)", "T.gemm(X, Y, X, policy=a, policy=b)",
    "T.copy(X, Y, 1)", "T.copy(X, unknown(Y))", "unknown.T.copy(X, Y)",
    "T.mbarrier_arrive(mbarrier=X, X)", "while k: {T.clear(X)}",
    "for i in arbitrary(k): {T.clear(X)}", "T.copy(X, T.tcgen05(Y))",
    "for i, j in range(n): {T.clear(X)}", "X, Y += 1"] do
    if (Parser.runParserCategory env `term (sample body)).isOk then
      throwError "accepted outside TileLang syntax: {body}"

/-- A declaration and use retain the formal arguments and both constexpr arms. -/
private def factoryExample : Source := tilelang {
  def demo(n, enabled): {
    if enabled: {k = n} else: {k = 1};
    @T.macro def stage(X, Y): {T.copy(X, Y)};
    @T.prim_func def run(X: T.Tensor([k], T.float32), Y: T.Tensor([k], T.float32)): {
      with T.Kernel(k) as b: {stage(X, Y)}
    };
    return run
  }
}

end VeriTile.TileLang
