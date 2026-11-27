import Lean

open Lean

/-- Inspect the compiled test modules and their transitive imports. Namespaces
do not determine ownership: each declaration has a module index in the environment. -/
def main (roots : List String) : IO Unit := do
  let imports := roots.toArray.map fun r => ({ module := r.toName } : Import)
  if imports.isEmpty || imports.any (fun i => !(`tests.lean).isPrefixOf i.module) then
    throw <| IO.userError "expected one or more tests.lean module names"
  initSearchPath (← findSysroot)
  let env ← importModules imports {}
  let mut rows : Array (String × String) := #[]
  for (name, info) in env.constants.toList do
    let .axiomInfo _ := info | continue
    let some idx := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[idx.toNat]!
    unless (`tests.lean).isPrefixOf origin do continue
    let file := String.intercalate "/" (origin.components.map Name.toString) ++ ".lean"
    let decl := (privateToUserName? name).getD name
    rows := rows.push (file, decl.toString)
  IO.println (toJson rows).compress
