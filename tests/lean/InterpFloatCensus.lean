import VeriTile.Interp.Carrier.Float
import tests.lean.InterpReflectBench
import tests.lean.InterpEvalSmoke

namespace VeriTile.Tests.InterpFloatCensus
open VeriTile Triton Interp

private def completes (k : QKernel) : Bool :=
  (interp Binary64.algebra k {
    init := fun _ i => .mk .real (i + 1).toFloat
    pids := fun _ => 0, numPids := fun _ => 1
    undef := fun d _ _ => FP.Structural.defaultValue d }).isSome

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    let .str _ "mirror" := name | continue
    unless info.type.getForallBody.isConstOf ``QKernel do continue
    let mut kernel : TSyntax `term := mkIdent name
    let mut ty := info.type
    repeat
      let .forallE binder domain body _ := ty | break
      let arg ← match domain.getAppFn.constName? with
        | some ``Nat => `(2)
        | some ``Rat => `((1/2 : ℚ))
        | some ``Region | some ``RegionName => do
          let regionName := Syntax.mkStrLit binder.toString
          `(Region.mk $regionName)
        | _ => throwError "unsupported parameter {binder} of {name}: {domain}"
      kernel ← `($kernel $arg)
      ty := body
    elabCommand (← `(command| #guard completes $kernel))
    count := count + 1
  let actual := Syntax.mkNumLit (toString count)
  elabCommand (← `(command| #guard $actual = 64))

-- InterpInterface §2 specifies a Lean Float approximation. For unordered
-- operands Lean's max keeps the first and min keeps the second.
#guard
  let maximum := Binary64.algebra.binary none .real .max
  match Binary64.algebra.minimum none .real with
  | some minimum =>
    (maximum Float.nan 1).isNaN && maximum 1 Float.nan == 1 &&
      minimum Float.nan 1 == 1 && (minimum 1 Float.nan).isNaN
  | none => Bool.false

end VeriTile.Tests.InterpFloatCensus
