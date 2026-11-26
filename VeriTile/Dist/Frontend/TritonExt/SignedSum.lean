-- Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/all_to_all_single_2d.py:35-39,98-112
-- Licence: MIT
-- Changes: transcribed to Lean; lower the signed split operations and receive-copy arithmetic with typed core operations
import VeriTile.Triton.DSL.StatementJitFunctions

/-! Signed int32 sums for the rank-one split tensors of the two distributed callers.
Triton v3.5.1, `python/triton/language/standard.py` lines 260–261, 268–291 and
332–341 retain the signed input width and use the same addition for sum and scan.
Each addition below keeps the low 32 bits, interpreted as a signed result. -/
namespace VeriTile.Dist.Frontend.TritonExt.SignedSum
open Lean Elab Term Meta
open VeriTile.Triton VeriTile.Triton.DSL

abbrev Operand := TSyntax `tritonExpr
abbrev Statement := TSyntax `tritonStmt

private inductive Kind where
  | pointer
  | scalar
  | constant
  | signedScalar
  | programIndex
  | lanes (extent : Operand)
  | mask (extent : Operand)
  | signed (extent : Operand)

private abbrev Facts := List (Name × Kind)

private partial def names (s : Syntax) : List Name :=
  if s.isIdent then [s.getId.eraseMacroScopes] else s.getArgs.toList.flatMap names

private partial def entries (e : Expr) : TermElabM (List Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then return []
  if e.isAppOfArity ``List.cons 3 then return e.getAppArgs[1]! :: (← entries e.getAppArgs[2]!)
  throwError "signed reduction requires a static call signature"

private def initial (signature : Syntax) : TermElabM (Facts × List Name) := do
  let profile ← elabTermEnsuringType signature (mkConst ``CallSignature)
  let mut facts := []
  let mut reserved := []
  for field in [``CallSignature.pointers, ``CallSignature.floatingPointers, ``CallSignature.scalars] do
    for pair in ← entries (← mkAppM field #[profile]) do
      let .lit (.strVal name) ← whnf (← mkAppM ``Prod.fst #[pair]) | throwError "expected ABI name"
      reserved := name.toName :: reserved
      if field == ``CallSignature.scalars then
        let dtype ← whnf (← mkAppM ``Prod.snd #[pair])
        facts := (name.toName, if dtype.isAppOf ``ScalarType.i32 then .signedScalar else .scalar) :: facts
      if field == ``CallSignature.pointers then
        if (← whnf (← mkAppM ``Prod.snd #[pair])).isAppOf ``SourceDType.i32 then
          facts := (name.toName, .pointer) :: facts
  for e in ← entries (← mkAppM ``CallSignature.constexpr #[profile]) do
    let .lit (.strVal name) ← whnf e | throwError "expected constexpr name"
    reserved := name.toName :: reserved
    let localDecl := (← getLCtx).findFromUserName? name.toName
    let integral ← match localDecl with
      | some d => isDefEq d.type (mkConst ``Nat)
      | none => pure Bool.false
    facts := (name.toName, if integral then .constant else .scalar) :: facts
  return (facts, reserved)

private def scalar? : Option Kind → Bool
  | some .scalar | some .signedScalar | some .programIndex | some .constant => Bool.true
  | _ => Bool.false

private partial def kind (facts : Facts) (e : Operand) : Option Kind := do
  if e.raw.getKind == choiceKind then return ← e.raw.getArgs.findSome? (fun v => kind facts ⟨v⟩)
  match e with
  | `(tritonExpr| ($v:tritonExpr)) => kind facts v
  | `(tritonExpr| $v:ident) => facts.lookup v.getId.eraseMacroScopes
  | `(tritonExpr| $_:num) | `(tritonExpr| tl.num_programs($_:tritonExpr)) => some .scalar
  | `(tritonExpr| tl.program_id($_:tritonExpr)) => some .programIndex
  | `(tritonExpr| tl.full([$n:tritonExpr], $_:tritonExpr, dtype=tl.int32))
  | `(tritonExpr| tl.zeros([$n:tritonExpr], dtype=tl.int32)) => some (.signed n)
  | `(tritonExpr| tl.full([], $_:tritonExpr, dtype=tl.int32)) => some .signedScalar
  | `(tritonExpr| tl.arange(0, $n:tritonExpr)) => some (.lanes n)
  | `(tritonExpr| $a:tritonExpr == $b:tritonExpr) =>
    let .lanes n ← kind facts a | none
    guard (scalar? (kind facts b))
    some (.mask n)
  | `(tritonExpr| $a:tritonExpr - $b:tritonExpr) =>
    guard (scalar? (kind facts a) && scalar? (kind facts b))
    some .scalar
  | `(tritonExpr| tl.load($p:ident + $offset:tritonExpr)) =>
    let .pointer ← facts.lookup p.getId.eraseMacroScopes | none
    match ← kind facts offset with
    | .lanes n => some (.signed n)
    | .scalar | .constant | .signedScalar | .programIndex => some .signedScalar
    | _ => none
  | `(tritonExpr| tl.load($p:ident)) =>
    let .pointer ← facts.lookup p.getId.eraseMacroScopes | none
    some .signedScalar
  | `(tritonExpr| tl.where($mask:tritonExpr, $v:tritonExpr, 0)) =>
    let .signed n ← kind facts v | none
    match ← kind facts mask with
    | .scalar | .constant | .signedScalar | .programIndex => some (.signed n)
    | .mask m | .lanes m =>
      guard (PythonFullConstructors.render m.raw == PythonFullConstructors.render n.raw)
      some (.signed n)
    | _ => none
  | _ => none

private abbrev Rewrite := StateT (List Name) TermElabM

private def fresh (base : String) : Rewrite Ident := do
  let used ← get
  let mut n := 0
  while used.contains (Name.mkSimple (base ++ toString n)) do n := n + 1
  let name := Name.mkSimple (base ++ toString n)
  set (name :: used)
  return mkIdent name

/-- Take each lane once, using the smallest signed int32 as the neutral element
for lane selection. The exclusive scalar loop bound makes the scan inclusive
at each output coordinate through the `>=` mask. -/
private def fold (dst : Ident) (source extent : Operand) (scan : Bool) : Rewrite (Array Statement) := do
  let input ← fresh "vt_sum_input"
  let lane ← fresh "vt_sum_lane"
  let scalar ← fresh "vt_sum_value"
  let offs ← fresh "vt_sum_offsets"
  let init ← if scan then `(tritonStmt| $dst:ident = tl.full([$extent:tritonExpr], 0, dtype=tl.int32))
    else `(tritonStmt| $dst:ident = tl.full([], 0, dtype=tl.int32))
  let term ← if scan then `(tritonExpr| tl.where($offs:ident >= $lane:ident, $scalar:ident, 0))
    else `(tritonExpr| $scalar:ident)
  return #[← `(tritonStmt| $input:ident = $source:tritonExpr),
    ← `(tritonStmt| $offs:ident = tl.arange(0, $extent:tritonExpr)), init,
    ← `(tritonStmt| for $lane:ident in range(0, $extent:tritonExpr) {
      $scalar:ident = tl.max(tl.where($offs:ident == $lane:ident, $input:ident, -2147483648), axis=0)
      $dst:ident = tl.cast($dst:ident + $term:tritonExpr, tl.int32) })]

private def reduction? (e : Operand) : Option (Bool × Operand) :=
  match e with
  | `(tritonExpr| tl.cumsum($v:tritonExpr, axis=0)) | `(tritonExpr| tl.cumsum($v:tritonExpr)) => some (Bool.true, v)
  | `(tritonExpr| tl.sum($v:tritonExpr, axis=0)) | `(tritonExpr| tl.sum($v:tritonExpr)) => some (Bool.false, v)
  | _ => none

abbrev Helper := Syntax → TermElabM (Option (Operand × Operand))

/-- Names a statement may overwrite. All tuple and annotated targets precede
the assignment token. Unknown forms conservatively invalidate every name they mention. -/
private partial def writes (s : Syntax) : List Name := Id.run do
  let args := s.getArgs.toList
  if s.getKind == choiceKind || s.getKind == nullKind then
    return args.flatMap writes
  if let first :: rest := args then
    if first.getAtomVal == "tl.store(" then return [] -- writes memory, not a register
    if first.isIdent then
      let assignment := fun (s : Syntax) => ["=", ":=", "+=", "-=", "*=", "/="].contains s.getAtomVal
      if let some i := args.findIdx? assignment then return (args.take i).flatMap names
    if ["if", "while", "for"].contains first.getAtomVal then
      if let some i := rest.findIdx? (·.getAtomVal == "{") then
        let binder := if first.getAtomVal == "for" then (rest.take 1).flatMap names else []
        return binder ++ (rest.drop (i + 1)).flatMap writes
  return names s

/-- A zero followed by a conditional helper write has an int32 join type.
Preserve the zero path when later operations read the joined register as signed. -/
private def joinZero (facts : Facts) (call : Helper) (stmt next : Syntax) : TermElabM Syntax := do
  let `(tritonStmt| $dst:ident = 0) := stmt | return stmt
  let `(tritonStmt| if $_:tritonExpr { $later:ident = $value:tritonExpr }) := next | return stmt
  unless dst.getId.eraseMacroScopes == later.getId.eraseMacroScopes do return stmt
  let alts := if value.raw.getKind == choiceKind then value.raw.getArgs else #[value.raw]
  for alt in alts do
    if let some (tensor, _) ← call alt then
      if let some (.signed _) := kind facts tensor then
        return (← `(tritonStmt| $dst:ident = tl.full([], 0, dtype=tl.int32))).raw
  return stmt

private def isSignedScalar (facts : Facts) (e : Operand) : Bool :=
  if let some .signedScalar := kind facts e then Bool.true else Bool.false

private def signedName (facts : Facts) (id : Ident) : Bool :=
  if let some .signedScalar := facts.lookup id.getId.eraseMacroScopes then Bool.true else Bool.false

private def isConst (facts : Facts) (e : Operand) : Bool :=
  if let some .constant := kind facts e then Bool.true else Bool.false

private def sameName (a b : Ident) := a.getId.eraseMacroScopes == b.getId.eraseMacroScopes

/-- Keep the source int32 operations before the memory frontend combines signed
displacements. The row/column views are recognized only for recorded aranges. -/
private partial def rowArithmetic (facts : Facts) (idx : Ident) (width count : Operand)
    (stx : Syntax) : MacroM Syntax := do
  let e : Operand := ⟨stx⟩
  let lanes := fun (id : Ident) => (facts.lookup id.getId.eraseMacroScopes).any fun
    | .lanes _ => Bool.true
    | _ => Bool.false
  let same := fun (a b : Operand) => PythonFullConstructors.render a.raw == PythonFullConstructors.render b.raw
  match e with
  | `(tritonExpr| ($off:ident + $i:ident * $w:tritonExpr + $r:ident[:, None]) * $h:tritonExpr) =>
    if signedName facts off && sameName i idx && same w width && lanes r && isConst facts h then
      return (← `(tritonExpr| tl.cast($e, tl.int32))).raw
  | `(tritonExpr| $i:ident * $w:tritonExpr + $r:ident[:, None] < $n:tritonExpr) =>
    if sameName i idx && same w width && lanes r && same n count then
      return (← `(tritonExpr| tl.cast($i:ident * $w:tritonExpr + $r:ident[:, None], tl.int32) < $n)).raw
  | `(tritonExpr| $i:ident * $w:tritonExpr * $h:tritonExpr) =>
    let program := (facts.lookup i.getId.eraseMacroScopes).any fun
      | .programIndex => Bool.true
      | _ => Bool.false
    if (sameName i idx && same w width || program && isConst facts w) && isConst facts h then
      return (← `(tritonExpr| tl.cast($e, tl.int32))).raw
  | `(tritonExpr| $r:ident[:, None] * $h:tritonExpr) =>
    if lanes r && isConst facts h then return (← `(tritonExpr| tl.cast($e, tl.int32))).raw
  | _ => pure ()
  return stx.setArgs (← stx.getArgs.mapM (rowArithmetic facts idx width count))

/-- Triton v3.5.1 standard.py:32–41 and semantic.py:311–322. For a positive
int32 tile extent, reduce the numerator modulo 2^32 before signed division.
Widening that word preserves its sign for the core range and loop index. -/
private def signedRange? (facts : Facts) (s : Syntax) : TermElabM (Option Syntax) := do
  let `(tritonStmt| for $idx:ident in range(0, tl.cdiv($n:tritonExpr, $w:tritonExpr)) { $body:tritonStmt* }) := s
    | return none
  unless isSignedScalar facts n do return none
  let supported := match w with
    | `(tritonExpr| $v:num) => 0 < v.getNat && v.getNat < 2^31
    | _ => isConst facts w
  unless supported do return none
  let written := body.toList.flatMap fun stmt => writes stmt.raw
  let stable := facts.filter fun f => !written.contains f.1
  let shadowed := (idx.getId.eraseMacroScopes :: (names n.raw ++ names w.raw)).any written.contains
  let adjusted ← body.mapM fun stmt => do
    -- Nested control or an unfamiliar statement retains its own typing.
    if shadowed then return stmt
    let raw := stmt.raw
    let load := raw.getNumArgs > 2 && raw[1]!.getAtomVal == "=" &&
      (PythonFullConstructors.render raw[2]!).startsWith "tl.load("
    if (raw.getNumArgs > 0 && raw[0]!.getAtomVal == "tl.store(") || load then
      return (⟨← liftMacroM (rowArithmetic stable idx w n raw)⟩ : Statement)
    return stmt
  let next ← `(tritonStmt| for $idx:ident in range(0,
    (tl.cast(tl.cast($n:tritonExpr + ($w:tritonExpr - 1), tl.int32), tl.int64) // $w:tritonExpr)) { $adjusted* })
  return some next.raw

private partial def lower (facts : Facts) (call : Helper) (s : Syntax) :
    Rewrite (Array Syntax × Facts × Bool) := do
  if let some next ← signedRange? facts s then
    let (out, after, _) ← lower facts call next
    return (out, after, Bool.true)
  if let `(tritonStmt| $dst:ident = $rhs:tritonExpr) := s then
    let remaining := facts.filter (·.1 != dst.getId.eraseMacroScopes)
    let alts := if rhs.raw.getKind == choiceKind then rhs.raw.getArgs else #[rhs.raw]
    for alt in alts do
      if let some (scan, source) := reduction? ⟨alt⟩ then
        if let some (.signed n) := kind facts source then
          let out ← fold dst source n scan
          let after := (dst.getId.eraseMacroScopes, if scan then .signed n else .signedScalar) :: remaining
          return (out.map (·.raw), after, Bool.true)
      if let some (tensor, idx) ← call alt then
        let some (.signed n) := kind facts tensor | throwErrorAt rhs "get_element_at requires a rank-one int32 tensor"
        unless scalar? (kind facts idx) do throwErrorAt idx "get_element_at index must be scalar"
        let mask ← `(tritonExpr| tl.where(tl.arange(0, $n:tritonExpr) == $idx:tritonExpr, $tensor:tritonExpr, 0))
        return ((← fold dst mask n Bool.false).map (·.raw), (dst.getId.eraseMacroScopes, .signedScalar) :: remaining, Bool.true)
    let after := (kind facts rhs).map (fun k => (dst.getId.eraseMacroScopes, k) :: remaining)
    return (#[s], after.getD remaining, Bool.false)
  if s.getNumArgs == 0 then return (#[s], facts, Bool.false)
  if s.getKind == choiceKind then
    for alt in s.getArgs do
      let (out, after, changed) ← lower facts call alt
      if changed then return (out, after, changed)
    return (#[s], facts.filter (fun f => !(writes s).contains f.1), Bool.false)
  let mut localFacts := facts
  let sequence := s.getKind == nullKind
  let repeats := s[0]!.getAtomVal == "for" || s[0]!.getAtomVal == "while"
  if repeats then
    localFacts := facts.filter (fun f => !(writes s).contains f.1)
    if s[0]!.getAtomVal == "for" && s.getNumArgs > 1 && s[1]!.isIdent then
      localFacts := (s[1]!.getId.eraseMacroScopes, .scalar) :: localFacts
  let mut out := #[]
  let mut changed := Bool.false
  let children := s.getArgs
  for i in [:children.size] do
    let original := children[i]!
    let child ← if sequence && i + 1 < children.size then joinZero localFacts call original children[i+1]!
      else pure original
    let (expanded, after, used) ← lower localFacts call child
    out := out ++ expanded
    if sequence then localFacts := after
    changed := changed || used || child != original
  -- Changes inside a conditional or loop cannot establish facts in its parent.
  let after := if sequence then localFacts else facts.filter (fun f => !(writes s).contains f.1)
  -- Both the initialized zero and the guarded helper assign signed int32.
  if let `(tritonStmt| if $_:tritonExpr { $id:ident = $rhs:tritonExpr }) := s then
    if signedName facts id then
      let alts := if rhs.raw.getKind == choiceKind then rhs.raw.getArgs else #[rhs.raw]
      for alt in alts do
        if let some (src, _) ← call alt then
          if let some (.signed _) := kind facts src then
            return (#[s.setArgs out], (id.getId.eraseMacroScopes, .signedScalar) :: after, changed)
  return (#[s.setArgs out], after, changed)

def prepare (signature body : Syntax) (call : Helper := fun _ => pure none) : TermElabM (Syntax × Bool) := do
  let some (facts, reserved) ← observing? (withoutErrToSorry (initial signature))
    | return (body, Bool.false)
  let ((out, _, changed), _) ← (lower facts call body).run (reserved ++ names body)
  return (out[0]!, changed)

def elaborate : TermElab := fun stx expected => do
  let raw := stx.getArgs.back!
  unless raw.getAtomVal.contains "tl.cumsum" || raw.getAtomVal.contains "tl.sum" || raw.getAtomVal.contains "tl.cdiv" do throwUnsupportedSyntax
  let .ok source := RawSourceText.normalize raw.getAtomVal | throwErrorAt raw "invalid signed reduction source"
  let .ok body := Parser.runParserCategory (← getEnv) `term ("triton {\n" ++ source ++ "\n}")
    | throwUnsupportedSyntax
  let (next, changed) ← prepare stx[1] body
  unless changed do throwUnsupportedSyntax
  let `(triton { $stmts:tritonStmt* }) := next | throwError "expected a complete source body"
  let text := String.intercalate "\n" (stmts.toList.map (PythonFullConstructors.render ·.raw))
  let repl := Syntax.atom raw.getHeadInfo ("{\n" ++ text ++ "\n}")
  elabTerm (stx.setArgs (stx.getArgs.set! (stx.getArgs.size - 1) repl)) expected

end VeriTile.Dist.Frontend.TritonExt.SignedSum
