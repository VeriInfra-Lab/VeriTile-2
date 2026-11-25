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

-- These productions can start at an ordinary identifier without adding a
-- keyword to Lean's global token table.
def tlBool : Parser := nonReservedSymbol "True" true <|> nonReservedSymbol "False" true
def tlOutputs : Parser := nonReservedSymbol "out_idx" true
def tlConfig : Parser := nonReservedSymbol "pass_configs" true
def tlAssert : Parser := nonReservedSymbol "assert" true

syntax (name := valueExpr) tlValueName : tlExpr
syntax (name := integerLiteral) num : tlExpr
syntax (name := scientificLiteral) scientific : tlExpr
syntax (name := stringLiteral) str : tlExpr
syntax (name := booleanLiteral) tlBool : tlExpr
syntax (name := groupedExpr) "(" tlExpr ")" : tlExpr
syntax (name := tupleExpr) "(" tlExpr "," tlExpr,*,? ")" : tlExpr
syntax (name := listExpr) "[" tlExpr,*,? "]" : tlExpr
syntax:max (name := indexedExpr) tlName noWs "[" tlIndex,+,? "]" : tlExpr
syntax (name := indexExpr) tlExpr : tlIndex
syntax (name := sliceIndex) (tlExpr)? ":" (tlExpr)? : tlIndex
syntax:75 (name := negExpr) "-" tlExpr:75 : tlExpr
syntax:80 (name := powExpr) tlExpr:81 " ** " tlExpr:75 : tlExpr
syntax:70 (name := mulExpr) tlExpr:70 " * " tlExpr:71 : tlExpr
syntax:70 (name := divExpr) tlExpr:70 " / " tlExpr:71 : tlExpr
syntax:70 (name := floorDivExpr) tlExpr:70 " // " tlExpr:71 : tlExpr
syntax:70 (name := modExpr) tlExpr:70 " % " tlExpr:71 : tlExpr
syntax:65 (name := addExpr) tlExpr:65 " + " tlExpr:66 : tlExpr
syntax:65 (name := subExpr) tlExpr:65 " - " tlExpr:66 : tlExpr
syntax:56 (name := xorExpr) tlExpr:56 " ^ " tlExpr:57 : tlExpr
syntax:50 (name := ltExpr) tlExpr:51 " < " tlExpr:51 : tlExpr
syntax:50 (name := gtExpr) tlExpr:51 " > " tlExpr:51 : tlExpr
syntax:50 (name := leExpr) tlExpr:51 " <= " tlExpr:51 : tlExpr
syntax:50 (name := geExpr) tlExpr:51 " >= " tlExpr:51 : tlExpr
syntax:50 (name := eqExpr) tlExpr:51 " == " tlExpr:51 : tlExpr
syntax:50 (name := neExpr) tlExpr:51 " != " tlExpr:51 : tlExpr
syntax:40 (name := conditionalExpr) tlExpr:41 " if " tlExpr:41 " else " tlExpr:40 : tlExpr

syntax (name := positionalArg) tlExpr : tlArg
syntax (name := kw) tlName "=" tlExpr : tlArg
syntax (name := primitive) rawIdentNoAntiquot "(" tlArg,*,? ")" : tlExpr
syntax (name := layout) rawIdentNoAntiquot "(" tlExpr "," &"lambda" tlName,+ ":" tlExpr ")" : tlExpr
syntax (name := layoutMap) "{" tlName ":" tlExpr (",")? "}" : tlExpr

syntax (name := namePlace) tlName : tlPlace
syntax (name := indexedTarget) tlName noWs "[" tlIndex,+,? "]" : tlPlace
syntax (name := placeTarget) tlPlace : tlTarget
syntax (name := tupleTarget) tlName "," tlName,+ : tlTarget
syntax (name := requiredParam) tlName : tlParam
syntax (name := defaultParam) tlName "=" tlExpr : tlParam
syntax (name := tensorAnnotation) tlName ":" &"T.Tensor" "(" tlExpr "," tlExpr ")" : tlTensor
syntax (name := tensorParam) tlTensor : tlParam

syntax (name := binding) tlTarget "=" tlExpr : tlBinding
syntax (name := assignStmt) tlBinding : tlStmt
syntax (name := tensorStmt) tlTensor : tlStmt
syntax (name := addAssignStmt) tlPlace "+=" tlExpr : tlStmt
syntax (name := mulAssignStmt) tlPlace "*=" tlExpr : tlStmt
syntax (name := subAssignStmt) tlPlace "-=" tlExpr : tlStmt
syntax (name := divAssignStmt) tlPlace "/=" tlExpr : tlStmt
syntax (name := operation) rawIdentNoAntiquot "(" tlArg,*,? ")" : tlStmt
syntax (name := returnStmt) "return" tlExpr : tlStmt
syntax (name := branch) "if" tlExpr ":" tlSuite ("else" ":" tlSuite)? : tlStmt
syntax (name := loop) "for" tlName,+ "in" tlIter ":" tlSuite : tlStmt
syntax (name := loopCall) rawIdentNoAntiquot "(" tlArg,*,? ")" : tlIter
syntax (name := kernel) "with" &"T.Kernel" "(" tlArg,+,? ")" &"as" tlName ":" tlSuite : tlStmt
syntax (name := grid) "with" &"T.Kernel" "(" tlArg,+,? ")" &"as" "(" tlName,+,? ")" ":" tlSuite : tlStmt
syntax (name := role) "with" &"T.ws" "(" tlExpr ")" ":" tlSuite : tlStmt
syntax (name := suite) "{" sepBy1(tlStmt, ";") (";")? "}" : tlSuite
syntax (name := helper) "@T.macro" "def" tlName "(" tlName,*,? ")" ":" tlSuite : tlMacro

-- The outer configuration admits literals and source names in defaults and
-- expressions; only these binding/assert/constexpr-branch statements can run there.
syntax (name := staticAssign) tlBinding : tlStatic
syntax (name := staticBranch) "if" tlExpr ":" "{" sepBy1(tlStatic, ";") (";")? "}" ("else" ":" "{" sepBy1(tlStatic, ";") (";")? "}")? : tlStatic
syntax (name := staticAssert) tlAssert tlExpr ("," str)? : tlStatic
syntax (name := outputs) tlOutputs "=" "[" num,+,? "]" : tlCfg
syntax (name := config) tlConfig "=" "{" (str <|> rawIdentNoAntiquot) ":" tlBool "}" : tlCfg
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
  if k == ``layout && !(plainSpelling stx[0] && stx[0].getId == `T.Layout) then return false
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
  let params := if s.isOfKind ``eager then s[5] else s[4]
  unless validConfigs s && distinctParams params && validDefaults params && checkedTree params [] do return false
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
private def validateOuter : Parser := {
  info := epsilonInfo
  fn := fun _ state => Id.run do
    let s := state.stxStack.back
    if validOuter s then return state
    if s.isOfKind ``factory then
      let macros := s[9].getArgs.map (fun g => g[0][2].getId)
      let unbound := s[17].find? fun call =>
        (call.isOfKind ``primitive || call.isOfKind ``operation) &&
        pyName call[0].getId && !macros.contains call[0].getId
      if let some call := unbound then
        return state.mkUnexpectedError s!"unbound TileLang local macro: {call[0].getId}"
    return state.mkUnexpectedError "unsupported TileLang call, arguments, kernel binding or macro"
}

@[combinator_formatter validateOuter] private def validateOuterFmt : PrettyPrinter.Formatter := pure ()
@[combinator_parenthesizer validateOuter] private def validateOuterParen : PrettyPrinter.Parenthesizer := pure ()

def checkedOuter : Parser := categoryParser `tlOuter 0 >> validateOuter
def quotationKeyword : Parser := nonReservedSymbol "tilelang" true

syntax (name := quotation) quotationKeyword "{" checkedOuter "}" : term

private partial def quoteSource (s : Syntax) : MetaM Expr := do
  match s with
  | .atom _ text => return mkApp (mkConst ``Source.token) (toExpr text)
  | .ident _ _ n _ => return mkApp (mkConst ``Source.name) (toExpr n)
  | .node _ k xs =>
    let children ← xs.toList.mapM quoteSource
    return mkApp2 (mkConst ``Source.node) (toExpr k) (← Meta.mkListLit (mkConst ``Source) children)
  | .missing => throwError "missing TileLang syntax"

@[term_elab quotation] def elabTileLang : Elab.Term.TermElab := fun stx _ => quoteSource stx[2]

end VeriTile.TileLang
