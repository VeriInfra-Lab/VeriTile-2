import VeriTile.Dist.Assumptions
import VeriTile.Meta.StatementAudit

namespace VeriTile.Dist

open Lean Meta Elab Command

/-- The registered statement and the declaration that supplies its metadata. -/
structure TrustAssumptionRegistration where
  declaration : Name
  metadata : Name
  name : Name
  assumptionClass : TrustAssumptionClass

private initialize trustAssumptionRegistry :
    SimplePersistentEnvExtension TrustAssumptionRegistration (Array TrustAssumptionRegistration) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun modules => modules.foldl (· ++ ·) #[]
  }

private def checkRegistration (declaration metadata : Name) :
    MetaM TrustAssumptionRegistration := do
  let userName := ((privateToUserName? declaration).getD declaration).eraseMacroScopes
  let .str _ suffix := userName
    | throwError "trust assumption must have a named declaration"
  let name := Name.mkSimple suffix
  let info ← getConstInfo declaration
  forallTelescopeReducing info.type fun args result => do
    unless ← isDefEq result (mkSort .zero) do
      throwError "trust assumption '{declaration}' must be Prop-valued"
    let metadataType ← mkForallFVars args (mkConst ``TrustAssumption)
    let metadataDecl ← mkConstWithFreshMVarLevels metadata
    unless ← isDefEq (← inferType metadataDecl) metadataType do
      throwError "trust metadata '{metadata}' must return TrustAssumption with the same parameters"
    let record := mkAppN metadataDecl args
    unless ← isDefEq (mkApp (mkConst ``TrustAssumption.name) record) (toExpr name) do
      throwError "trust metadata '{metadata}' must name '{name}'"
    let statement := mkAppN (← mkConstWithLevelParams declaration) args
    unless ← isDefEq (mkApp (mkConst ``TrustAssumption.statement) record) statement do
      throwError "trust metadata '{metadata}' does not state '{declaration}'"
    let classExpr ← whnf (mkApp (mkConst ``TrustAssumption.assumptionClass) record)
    let assumptionClass ←
      if classExpr.isConstOf ``TrustAssumptionClass.semanticSource then
        pure TrustAssumptionClass.semanticSource
      else if classExpr.isConstOf ``TrustAssumptionClass.translationCorrectness then
        pure TrustAssumptionClass.translationCorrectness
      else
        throwError "trust metadata '{metadata}' must specify a fixed assumption class"
    return { declaration, metadata, name, assumptionClass }

private def builtinRegistrations : MetaM (Array TrustAssumptionRegistration) :=
  TrustAssumptions.builtinTrustAssumptionDeclarations.mapM (fun (declaration, metadata) =>
    checkRegistration declaration metadata)

def registeredTrustAssumptions : CoreM (Array TrustAssumptionRegistration) := do
  return (← builtinRegistrations.run') ++ trustAssumptionRegistry.getState (← getEnv)

private def registerAssumption (declaration metadata : Name) : CoreM Unit := do
  let entry ← (checkRegistration declaration metadata).run'
  if (← registeredTrustAssumptions).any (·.name == entry.name) then
    throwError "trust assumption '{entry.name}' is already registered"
  modifyEnv fun env => trustAssumptionRegistry.addEntry env entry

initialize
  registerBuiltinAttribute {
    name := `trust_assumption
    descr := "register a premise with metadata bearing the same name and parameters"
    add := fun declaration stx kind => do
      unless kind == .global do
        throwError "trust_assumption must be a global attribute"
      let id ← Attribute.Builtin.getIdent stx
      let metadata ← realizeGlobalConstNoOverload id
      registerAssumption declaration metadata
  }

-- Validate the built-in metadata at elaboration as well as when queried.
run_cmd do
  discard <| liftCoreM builtinRegistrations.run'

private def classLabel : TrustAssumptionClass → String
  | .semanticSource => "semantic source"
  | .translationCorrectness => "translation correctness"

-- Consult Lean's records for the exact declaration. A matcher may be shared by
-- multiple definitions, so the namespace of its name does not identify a premise.
private def isGeneratedAuxiliary (env : Environment) (referrer : Name)
    (info : ConstantInfo) : Bool := Id.run do
  let name := info.name
  if isMatcherCore env name || isSparseCasesOn env name then
    return true
  let matchEquations := Match.matchEqnsExt.getState
    (asyncMode := .async .asyncEnv) (asyncDecl := name) env
  if matchEquations.eqns.contains name ||
      [name.getPrefix, privateToUserName name.getPrefix].any (fun matcher =>
        (matchEquations.map.find? matcher).any (·.splitterName == name)) then
    return true
  -- The elaborator records equations and proof helpers in the branch that
  -- requested them, which may be the declaration referencing the helper.
  let equations := eqnsExt.getState
    (asyncMode := .async .asyncEnv) (asyncDecl := referrer) env
  if equations.mapInv.contains name then
    return true
  let lemmas := auxLemmasExt.getState
    (asyncMode := .async .asyncEnv) (asyncDecl := referrer) env
  return [false, true].any fun isPrivate =>
    (lemmas.lemmas.find? { type := info.type, isPrivate }).any (·.1 == name)

/-- Follow kernel dependencies as in `Lean.CollectAxioms.collect`. Constructors
carry the fields of classes and structures that their type constants name. -/
private partial def visitDependencies (env : Environment) (registered : NameSet)
    (referrer name : Name) : StateT NameSet CoreM Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  let userName := ((privateToUserName? name).getD name).eraseMacroScopes
  let some info := env.checked.get.find? name
    | throwError "could not inspect trust dependency '{name}'"
  if (`VeriTile.Dist.Assumption).isPrefixOf userName && !registered.contains name &&
      !isGeneratedAuxiliary env referrer info then
    throwError "unregistered trust assumption '{userName}'"
  if let .quotInfo _ := info then return
  let visit := visitDependencies env registered name
  info.type.getUsedConstants.forM visit
  if let some value := info.value? (allowOpaque := Bool.true) then
    value.getUsedConstants.forM visit
  if let .inductInfo inductiveType := info then
    inductiveType.ctors.forM visit

/-- Print the registered assumptions reached through the theorem type and
proof and the declarations they reference transitively. The report can include
assumptions mentioned in a dependency even when its full interface is unused
by the proof. A reached declaration in the reserved
`VeriTile.Dist.Assumption` namespace must be registered or identified by Lean
as a generated auxiliary. Auxiliary types and bodies are inspected too. -/
elab "#print_trust_assumptions " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload id
  let .thmInfo _ ← getConstInfo name | throwError "'{name}' is not a theorem"
  let env ← getEnv
  let registrations ← liftCoreM registeredTrustAssumptions
  -- Independently compiled imports can each introduce the same registry name.
  let mut names : NameSet := {}
  for entry in registrations do
    if names.contains entry.name then
      throwError "trust assumption '{entry.name}' is already registered"
    names := names.insert entry.name

  let registered : NameSet := registrations.foldl (fun names entry =>
    names.insert entry.declaration) {}
  let (_, reached) ← liftCoreM <| (visitDependencies env registered name name).run {}
  let entries := (registrations.filter (reached.contains ·.declaration)).qsort
    (·.name.toString < ·.name.toString)
  let lines := if entries.isEmpty then ["  none"] else
    entries.toList.map (fun entry => s!"  {entry.name} ({classLabel entry.assumptionClass})")
  logInfo <| String.intercalate "\n" (s!"Trust assumptions used by {id.getId}:" :: lines)

end VeriTile.Dist
