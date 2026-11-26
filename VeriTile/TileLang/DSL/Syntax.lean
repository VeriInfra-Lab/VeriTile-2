import VeriTile.TileLang.DSL.Accepted

/-! Closed source syntax for the A3.1 freeze draft. The public quotation returns
a typed Program, including calls whose semantics are deferred.
Braces delimit Python suites; semicolons separate their statements. -/
namespace VeriTile.TileLang
open Lean Parser

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

/-- Local Python identifiers include Lean keywords such as `by`. Qualified
identifiers cannot slip through as unregistered primitives or local macros. -/
def tlName : Parser := rawIdentNoAntiquot >>
  checkStackTop (fun s => plainSpelling s && sourceIdentifier s.getId) "expected an unqualified TileLang source identifier"

private def valueSpelling (mode : Mode) : Name → Bool
  | .str .anonymous field => sourceIdentifier (.mkSimple field)
  | .str `T field => syntacticCall mode (.str `T field)
  | .str base field => valueSpelling mode base && sourceIdentifier (.mkSimple field)
  | _ => false

def tlValueName : Parser := rawIdentNoAntiquot >>
  checkStackTop (fun s => plainSpelling s && valueSpelling .tileScale s.getId) "unsupported TileLang value or attribute"

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
-- Trailing word operators start at an identifier token in the Pratt table.
def pyAnd : Parser := atomic (rawIdentNoAntiquot >> checkStackTop (fun s => s.getId == `and) "expected and")
def pyOr : Parser := atomic (rawIdentNoAntiquot >> checkStackTop (fun s => s.getId == `or) "expected or")
syntax:35 (name := andExpr) tlExpr:35 pyAnd tlExpr:36 : tlExpr
syntax:30 (name := orExpr) tlExpr:30 pyOr tlExpr:31 : tlExpr
def pyNot : Parser := atomic (rawIdentNoAntiquot >> checkStackTop (fun s => s.getId == `not) "expected not")
syntax:45 (name := notExpr) pyNot tlExpr:45 : tlExpr
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
syntax:25 (name := conditionalExpr) tlExpr:30 " if " tlExpr:30 " else " tlExpr:25 : tlExpr

syntax (name := positionalArg) tlExpr : tlArg
syntax (name := kw) tlName "=" tlExpr : tlArg
-- A Boolean prefix followed by a parenthesized operand is still a prefix, e.g. not (a or b).
def tlCallee : Parser := atomic (rawIdentNoAntiquot >>
  checkStackTop (fun s => plainSpelling s && syntacticCall .tileScale s.getId) "expected a callable source name")
syntax (name := primitive) tlCallee "(" tlArg,*,? ")" : tlExpr
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
syntax (name := assertStmt) tlAssert tlExpr ("," str)? : tlStmt
syntax (name := returnStmt) "return" tlExpr : tlStmt
syntax (name := branch) "if" tlExpr ":" tlSuite ("else" ":" tlSuite)? : tlStmt
syntax (name := loop) "for" tlName,+ "in" tlIter ":" tlSuite : tlStmt
syntax (name := loopCall) rawIdentNoAntiquot "(" tlArg,*,? ")" : tlIter
syntax (name := kernel) "with" &"T.Kernel" "(" tlArg,+,? ")" &"as" tlName ":" tlSuite : tlStmt
syntax (name := grid) "with" &"T.Kernel" "(" tlArg,+,? ")" &"as" "(" tlName,+,? ")" ":" tlSuite : tlStmt
syntax (name := role) "with" &"T.ws" "(" tlExpr ")" ":" tlSuite : tlStmt
syntax (name := suite) "{" sepBy1(tlStmt, ";") (";")? "}" : tlSuite
syntax (name := whileStmt) &"while" tlExpr ":" tlSuite : tlStmt
syntax (name := breakStmt) &"break" : tlStmt
syntax (name := continueStmt) &"continue" : tlStmt
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


-- A top-level helper has exactly one return and no other executable statement.
-- Its layout expression must use only the bound input and coordinate grammar.
declare_syntax_cat tlLayoutDecl
syntax (name := pureHelper) "def" tlName "(" tlName ")" ":" "{" "return" tlExpr "}" : tlLayoutDecl
declare_syntax_cat tlUnit
syntax (name := unitProgram) (atomic(tlLayoutDecl ";"))* tlOuter : tlUnit

private def names (s : Syntax) : List Name := s.getSepArgs.toList.map Syntax.getId
private def spelling (s : Syntax) : String := s.reprint.getD "" |>.trimAscii |>.toString

private def bin? (k : Name) : Option Binary :=
  [(``powExpr, .pow), (``mulExpr, .mul), (``divExpr, .div), (``floorDivExpr, .floorDiv),
   (``modExpr, .mod), (``addExpr, .add), (``subExpr, .sub), (``xorExpr, .xor), (``ltExpr, .lt),
   (``gtExpr, .gt), (``leExpr, .le), (``geExpr, .ge), (``eqExpr, .eq), (``neExpr, .ne),
   (``andExpr, .and), (``orExpr, .or)].lookup k

private abbrev Read := Except String
private def reject (s : Syntax) : Read α := .error s!"unsupported TileLang production: {s.getKind}"

mutual
private partial def readValue (s : Syntax) : Read Value := do
  let k := s.getKind
  if k == ``valueExpr then return .ident s[0].getId
  if k == ``integerLiteral then return .integer (← s[0].isNatLit?.elim (reject s) pure)
  if k == ``scientificLiteral then return .decimal (spelling s[0])
  if k == ``stringLiteral then return .string (← s[0].isStrLit?.elim (reject s) pure)
  if k == ``booleanLiteral then return .boolean (spelling s[0] == "True")
  if k == ``groupedExpr then return ← readValue s[1]
  if k == ``tupleExpr then return .tuple ((← readValue s[1]) :: (← s[3].getSepArgs.toList.mapM readValue))
  if k == ``listExpr then return .list (← s[1].getSepArgs.toList.mapM readValue)
  if k == ``indexedExpr then return .index s[0].getId (← s[2].getSepArgs.toList.mapM readIndex)
  if k == ``primitive then return .call s[0].getId (← s[2].getSepArgs.toList.mapM readArgument)
  if k == ``layout && s[0].getId == `T.Layout then
    return .layout (← readValue s[2]) (names s[5]) (← readValue s[7])
  if k == ``layoutMap then return .layoutMap s[1].getId (← readValue s[3])
  if k == ``negExpr then return .neg (← readValue s[1])
  if k == ``notExpr then return .not (← readValue s[1])
  if k == ``conditionalExpr then return .conditional (← readValue s[0]) (← readValue s[2]) (← readValue s[4])
  if let some op := bin? k then return .binary op (← readValue s[0]) (← readValue s[2])
  reject s
private partial def readArgument (s : Syntax) : Read Argument := do
  if s.isOfKind ``kw then return .keyword s[0].getId (← readValue s[2])
  if s.isOfKind ``positionalArg then return .pos (← readValue s[0])
  reject s
private partial def readIndex (s : Syntax) : Read Index := do
  if s.isOfKind ``indexExpr then return .atIndex (← readValue s[0])
  if s.isOfKind ``sliceIndex then
    return .slice (← s[0].getArgs[0]?.mapM readValue) (← s[2].getArgs[0]?.mapM readValue)
  reject s
end

private partial def readPlace (s : Syntax) : Read Place := do
  if s.isOfKind ``placeTarget then return ← readPlace s[0]
  if s.isOfKind ``namePlace then return .variable s[0].getId
  if s.isOfKind ``indexedTarget then return .index s[0].getId (← s[2].getSepArgs.toList.mapM readIndex)
  if s.isOfKind ``tupleTarget then return .unpack (s[0].getId :: names s[2])
  reject s

private def readParam (s : Syntax) : Read Parameter := do
  if s.isOfKind ``requiredParam then return .required s[0].getId
  if s.isOfKind ``defaultParam then return .optional s[0].getId (← readValue s[2])
  let t := if s.isOfKind ``tensorParam then s[0] else s
  if t.isOfKind ``tensorAnnotation then return .tensor t[0].getId (← readValue t[4]) (← readValue t[6])
  reject s

private partial def readStmt (s : Syntax) : Read Statement := do
  let k := s.getKind
  let suiteAt := fun (b : Syntax) => b[1].getSepArgs.toList.mapM readStmt
  if k == ``assignStmt || k == ``staticAssign then
    return .assign (← readPlace s[0][0]) (← readValue s[0][2])
  if k == ``tensorStmt then return .annotate s[0][0].getId (← readValue s[0][4]) (← readValue s[0][6])
  if let some op := [(``addAssignStmt, Binary.add), (``subAssignStmt, .sub),
      (``divAssignStmt, .div), (``mulAssignStmt, .mul)].lookup k then
    return .update (← readPlace s[0]) op (← readValue s[2])
  if k == ``operation then return .invoke s[0].getId (← s[2].getSepArgs.toList.mapM readArgument)
  if k == ``returnStmt then return .ret (← readValue s[1])
  if k == ``branch then
    let no ← if s[4].getNumArgs == 0 then pure [] else suiteAt s[4][2]
    return .branch (← readValue s[1]) (← suiteAt s[3]) no
  if k == ``staticBranch then
    let no ← if s[7].getNumArgs == 0 then pure [] else s[7][3].getSepArgs.toList.mapM readStmt
    return .branch (← readValue s[1]) (← s[4].getSepArgs.toList.mapM readStmt) no
  if k == ``staticAssert || k == ``assertStmt then return .assertStatic (← readValue s[1]) s[2][1].isStrLit?
  if k == ``loop then
    return .loop (names s[1]) s[3][0].getId (← s[3][2].getSepArgs.toList.mapM readArgument) (← suiteAt s[5])
  if k == ``kernel || k == ``grid then
    let bs := if k == ``kernel then [s[6].getId] else names s[7]
    return .kernel (← s[3].getSepArgs.toList.mapM readArgument) bs
      (← suiteAt (if k == ``kernel then s[8] else s[10]))
  if k == ``role then return .role (← readValue s[3]) (← suiteAt s[6])
  if k == ``whileStmt then return .whileLoop (← readValue s[1]) (← suiteAt s[3])
  if k == ``breakStmt then return .breakLoop
  if k == ``continueStmt then return .continueLoop
  reject s

private def readConfigs (s : Syntax) : Read (List JitOption) := do
  let some entries := s.find? (fun e => e.getArgs.any fun c => c.isOfKind ``config || c.isOfKind ``outputs)
    | return []
  entries.getSepArgs.toList.mapM fun e => do
    if e.isOfKind ``outputs then return .outputs (← e[3].getSepArgs.toList.mapM fun n => n.isNatLit?.elim (reject n) pure)
    if e.isOfKind ``config then
      let key := match e[3].isStrLit? with | some v => OptionKey.literal v | none => .symbol e[3].getId
      return .flag key (spelling e[5] == "True")
    reject e

private def readUnit (m : Mode) (u : Syntax) : Read Program := do
  let layouts ← u[0].getArgs.toList.mapM fun g => do
    let h := g[0]
    let .layout shape coords mapping ← readValue h[8] | throw "expected a single return T.Layout(shape, lambda …)"
    let helper : LayoutHelper := ⟨h[1].getId, h[3].getId, shape, coords, mapping⟩
    unless helper.valid do throw "layout helper must use the bound buffer shape and coordinate arithmetic"
    return helper
  let s := u[1]
  let paramsAt := fun (p : Syntax) => p.getSepArgs.toList.mapM readParam
  let suiteAt := fun (b : Syntax) => b[1].getSepArgs.toList.mapM readStmt
  if s.isOfKind ``eager then
    return ⟨m, layouts, some (← readConfigs s[1]), .direct ⟨s[3].getId, ← paramsAt s[5], ← suiteAt s[8]⟩⟩
  unless s.isOfKind ``factory do reject s
  let outer : Procedure := ⟨s[2].getId, ← paramsAt s[4], ← s[8].getArgs.toList.mapM (fun g => readStmt g[0])⟩
  let macros ← s[9].getArgs.toList.mapM fun g => do
    let h := g[0]
    return (⟨h[2].getId, (names h[4]).map Parameter.required, ← suiteAt h[7]⟩ : Procedure)
  let primFunc : Procedure := ⟨s[12].getId, ← paramsAt s[14], ← suiteAt s[17]⟩
  let opts ← if s[0].getNumArgs == 0 then pure none else some <$> readConfigs s[0]
  return ⟨m, layouts, opts, .factory outer macros primFunc s[20].getId⟩

/-- Shared grammar. The raw quotation preserves exported calls outside the admitted fragment.
The explicitly excluded low-level operations fail in TileLang mode even when nested. -/
private def hasComment : List Char → Bool → Bool
  | [], _ => false
  | '\\' :: _ :: more, true => hasComment more true
  | '"' :: more, quoted => hasComment more (!quoted)
  | '-' :: '-' :: _, false | '/' :: '-' :: _, false => true
  | _ :: more, quoted => hasComment more quoted

private def validateUnit (m : Mode) : Parser := {
  info := epsilonInfo
  fn := fun c state => Id.run do
    let u := state.stxStack.back
    let stack := state.stxStack
    -- The opening brace's trailing trivia includes a comment before the first definition.
    let start := (stack.get! (stack.size - 2)).getTailPos?.getD 0
    if hasComment (c.extract start state.pos).toList false then
      return state.mkUnexpectedError "Lean comments are forbidden inside source quotations"
    if m == .tileLang && (u.find? fun n =>
        [``whileStmt, ``breakStmt, ``continueStmt, ``andExpr, ``orExpr, ``notExpr].contains n.getKind).isSome then
      return state.mkUnexpectedError "TileScale control operators require tilescale mode"
    if let some bad := u.find? fun n =>
        [``operation, ``primitive, ``loopCall, ``layout].contains n.getKind &&
          !(plainSpelling n[0] && syntacticCall m n[0].getId) then
      return state.mkUnexpectedError s!"outside the {repr m} call grammar: {bad[0].getId}"
    if let some bad := u.find? fun n => n.isOfKind ``valueExpr && !valueSpelling m n[0].getId then
      return state.mkUnexpectedError s!"outside the {repr m} value grammar: {bad[0].getId}"
    if let .error e := readUnit m u then return state.mkUnexpectedError e
    return state
}
@[combinator_formatter validateUnit] private def validateUnitFmt (_ : Mode) : PrettyPrinter.Formatter := pure ()
@[combinator_parenthesizer validateUnit] private def validateUnitParen (_ : Mode) : PrettyPrinter.Parenthesizer := pure ()
def tileLangUnit : Parser := categoryParser `tlUnit 0 >> validateUnit .tileLang
def tileScaleUnit : Parser := categoryParser `tlUnit 0 >> validateUnit .tileScale
def quotationKeyword : Parser := nonReservedSymbol "tilelang" true
def scaleKeyword : Parser := nonReservedSymbol "tilescale" true
syntax (name := quotation) quotationKeyword "{" tileLangUnit "}" : term
syntax (name := scaleQuotation) scaleKeyword "{" tileScaleUnit "}" : term

@[term_elab quotation, term_elab scaleQuotation] def elabTileLang : Elab.Term.TermElab := fun stx _ => do
  let mode := if stx.isOfKind ``quotation then Mode.tileLang else .tileScale
  match readUnit mode stx[2] with
  | .ok p => return toExpr p
  | .error e => throwError "{e}"

end VeriTile.TileLang
