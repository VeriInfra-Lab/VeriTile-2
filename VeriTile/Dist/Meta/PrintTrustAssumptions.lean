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

/-- Print the named assumptions among the direct hypotheses of a theorem's
type. Inspection uses the head constant of each premise without unfolding
definitions or inspecting the proof. An unregistered head in the reserved
`VeriTile.Dist.Assumption` namespace is an error. -/
elab "#print_trust_assumptions " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload id
  let .thmInfo info ← getConstInfo name | throwError "'{name}' is not a theorem"
  let registrations ← liftCoreM registeredTrustAssumptions
  -- Independently compiled imports can each introduce the same registry name.
  let mut names : NameSet := {}
  for entry in registrations do
    if names.contains entry.name then
      throwError "trust assumption '{entry.name}' is already registered"
    names := names.insert entry.name

  liftTermElabM <| forallTelescope info.type fun premises _ => do
    let mut used : NameSet := {}
    for premise in premises do
      let type ← inferType premise
      let some head := type.consumeMData.getAppFn.constName? | continue
      if let some entry := registrations.find? (·.declaration == head) then
        used := used.insert entry.name
      else
        let userName := ((privateToUserName? head).getD head).eraseMacroScopes
        if (`VeriTile.Dist.Assumption).isPrefixOf userName then
          throwError "unregistered trust assumption '{userName}'"
    let entries := (registrations.filter (used.contains ·.name)).qsort
      (·.name.toString < ·.name.toString)
    let lines := if entries.isEmpty then ["  none"] else
      entries.toList.map (fun entry => s!"  {entry.name} ({classLabel entry.assumptionClass})")
    logInfo <| String.intercalate "\n" (s!"Trust assumptions used by {id.getId}:" :: lines)

end VeriTile.Dist
