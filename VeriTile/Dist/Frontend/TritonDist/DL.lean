import VeriTile.Dist.Frontend.TritonDist.Syntax
import VeriTile.Dist.Event

/-! The `dl.*` rows of the signed `documents/dist/TritonDistSubset.md`.
Operands retain their Triton source for evaluation by the enclosing program.
The resulting locations and events use the signed S1 and S2 interface. -/

namespace VeriTile.Dist.Frontend.TritonDist.DL
open Lean Elab Term
open VeriTile.Triton.DSL
open scoped VeriTile.Dist.Frontend.TritonDist

/-- D6 requires both the equality and the greater-or-equal readings. -/
inductive WaitReading where
  | eq
  | ge
  deriving DecidableEq

/-- The inputs to `dl.wait` once its operands have been evaluated. -/
structure Wait where
  base : Addr
  count : Nat
  threshold : Nat
  scope : Scope
  order : MemOrder

/-- E-TD1–3, D5, D6, and A1(a). M3 gives each word its own event. -/
def Wait.event (w : Wait) (reading : WaitReading) (i : Fin w.count) : Event :=
  let word := { w.base with offset := w.base.offset + i.val }
  let cmp := match reading with | .eq => Cmp.eq | .ge => Cmp.ge
  .wait (.word word) cmp w.threshold (.atomic w.scope w.order)

/-- Each word has a distinct observation by this agent during this invocation.
The positions may occur in any order and may be interleaved with other events. -/
def Wait.Observed (w : Wait) (agent : Agent) (reading : WaitReading) (startedAt : Nat)
    (before : Trace) : Prop :=
  startedAt ≤ before.length ∧
  ∃ index : Fin w.count → Fin before.length, Function.Injective index ∧
    ∀ i, startedAt ≤ (index i).val ∧ before.get (index i) = (agent, w.event reading i)

/-- A token for a completed wait of the same agent, indexed by the point at
which that invocation began and the trace prefix before the continuation. -/
structure WaitToken (wait : Wait) (agent : Agent) (reading : WaitReading)
    (startedAt : Nat) (before : Trace) where
  observed : wait.Observed agent reading startedAt before

/-- E-TD2 and E-TD4. Using a completed token leaves the value unchanged. -/
def consumeToken {α : Type} {wait : Wait} {reading : WaitReading}
    {agent : Agent} {startedAt : Nat} {before : Trace}
    (value : α) (_token : WaitToken wait agent reading startedAt before) : α := value

/-- The notification scopes with a signed interpretation in A2. -/
inductive NotifyScope where
  | intraNode
  | gpu
  deriving DecidableEq

/-- A2 (and A8 for cross-GPU atomics). Emit a release update to the destination word. -/
def notify (symm : VeriTile.Triton.RegionName → Bool) (ptr : Addr) (rank : Rank) (signal : Nat)
    (scope : NotifyScope) (op : SignalOp := .set) : Option Event := do
  let word ← symmAt symm ptr rank
  let atomicScope := match scope with | .intraNode => Scope.sys | .gpu => Scope.gpu
  return .bump ⟨.word word, op, signal, .atomic atomicScope .release⟩

/-- E-TD9. Entering a SIMT region binds the executing thread's index and launch
block size. Entry has no event. -/
def simtBindings (agent : Agent) (blockSize : Nat) : Option (Nat × Nat) :=
  match agent with
  | .thread _ _ index => some (index, blockSize)
  | _ => none

/-- A checked distributed call with its original operand expressions. -/
inductive Call where
  /-- E-TD6. Read `Agent.rankOf` from the caller. -/
  | rank
  /-- E-TD6. Read the launch's number of participating ranks. -/
  | numRanks
  /-- E-TD5. Apply S1's `symmAt` to the evaluated operands. -/
  | symmAt (ptr rank : Syntax)
  | wait (ptr count threshold : Syntax) (scope : Scope) (order : MemOrder)
  | consumeToken (value token : Syntax)
  | notify (ptr rank signal : Syntax) (scope : NotifyScope) (op : SignalOp)
  | simtRegion (index size : Name)


/-- Values of the current launch and the enclosing Triton evaluator. -/
structure CallContext where
  agent : Agent
  numRanks : Nat
  blockSize : Nat
  symmetric : VeriTile.Triton.RegionName → Bool
  evalAddr : Syntax → Option Addr
  evalNat : Syntax → Option Nat

/-- A pure result, an S2 event, or an operation with a local continuation. -/
inductive Result where
  | scalar (value : Nat)
  | address (value : Addr)
  | event (value : Event)
  | wait (request : Wait)
  | afterWait (value token : Syntax)
  | simt (index size : Name) (thread blockSize : Nat)

/-- Lower a single call after evaluating its operands in the enclosing program.
Wait and token continuations remain distinct until the observations are supplied. -/
def Call.lower (ctx : CallContext) : Call → Option Result
  | .rank => some (.scalar ctx.agent.rankOf)
  | .numRanks => some (.scalar ctx.numRanks)
  | .symmAt ptr targetRank => do
    let ptr ← ctx.evalAddr ptr
    let rank ← ctx.evalNat targetRank
    guard (rank < ctx.numRanks)
    return .address (← VeriTile.Dist.symmAt ctx.symmetric ptr rank)
  | .wait ptr count threshold scope order => do
    let ptr ← ctx.evalAddr ptr
    let count ← ctx.evalNat count
    let threshold ← ctx.evalNat threshold
    return .wait ⟨ptr, count, threshold, scope, order⟩
  | .consumeToken value token => some (.afterWait value token)
  | .notify ptr targetRank signal scope op => do
    let ptr ← ctx.evalAddr ptr
    let rank ← ctx.evalNat targetRank
    let signal ← ctx.evalNat signal
    guard (rank < ctx.numRanks)
    return .event (← DL.notify ctx.symmetric ptr rank signal scope op)
  | .simtRegion index size => do
    let (thread, blockSize) ← simtBindings ctx.agent ctx.blockSize
    return .simt index size thread blockSize

/-- The path identifies a call in the source tree, including operand calls and
calls inside branches or loops. The path records syntax tree position only. -/
structure Site where
  path : List Nat
  call : Call

/-- The original block and its checked DL call sites. The enclosing frontend
still evaluates operands and control flow. -/
structure Source where
  block : Syntax
  sites : List Site

private partial def quoteSource (stx : Syntax) : TermElabM (TSyntax `term) := do
  match stx with
  | .missing => `(Syntax.missing)
  | .atom _ token =>
    let token := quote token
    `(Syntax.atom SourceInfo.none $token)
  | .ident _ spelling name _ =>
    let spelling := quote spelling.toString
    let name := quote name.eraseMacroScopes
    `(Syntax.ident SourceInfo.none (String.toRawSubstring $spelling) $name [])
  | .node _ kind args =>
    let args ← args.mapM quoteSource
    let kind := quote kind
    `(Syntax.node SourceInfo.none $kind #[$args,*])

private def literal (parameter : String) (arg : TSyntax `tritonExpr) : TermElabM String := do
  let `(tritonExpr| $s:str) := arg
    | throwErrorAt arg "{parameter} must be a string literal"
  return s.getString

private def waitScope (arg : TSyntax `tritonExpr) : TermElabM (TSyntax `term) := do
  match ← literal "dl.wait scope" arg with
  | "cta" => `(Scope.cta)
  | "gpu" => `(Scope.gpu)
  | "sys" => `(Scope.sys)
  | scope => throwErrorAt arg "dl.wait: unsupported scope '{scope}'"

private def waitOrder (arg : TSyntax `tritonExpr) : TermElabM (TSyntax `term) := do
  match ← literal "dl.wait semantic" arg with
  | "relaxed" => `(MemOrder.relaxed)
  | "acquire" => `(MemOrder.acquire)
  | "release" => `(MemOrder.release)
  | "acq_rel" => `(MemOrder.acqRel)
  | order => throwErrorAt arg "dl.wait: unsupported semantic '{order}'"

private def quoteWait (ptr count scope order : TSyntax `tritonExpr)
    (threshold : TSyntax `tritonExpr) : TermElabM (TSyntax `term) := do
  let scope ← waitScope scope
  let order ← waitOrder order
  let ptr ← quoteSource ptr
  let count ← quoteSource count
  let threshold ← quoteSource threshold
  `(Call.wait $ptr $count $threshold $scope $order)

private def notifyScope (arg : TSyntax `tritonExpr) : TermElabM (TSyntax `term) := do
  match ← literal "dl.notify comm_scope" arg with
  | "intra_node" => `(NotifyScope.intraNode)
  | "gpu" => `(NotifyScope.gpu)
  | scope => throwErrorAt arg "dl.notify: unsupported comm_scope '{scope}'"

private def signalOp (arg : TSyntax `tritonExpr) : TermElabM (TSyntax `term) := do
  match ← literal "dl.notify sig_op" arg with
  | "set" => `(SignalOp.set)
  | "add" => `(SignalOp.add)
  | op => throwErrorAt arg "dl.notify: unsupported sig_op '{op}'"

private def quoteNotify (ptr rank signal scope : TSyntax `tritonExpr)
    (op : TSyntax `term) : TermElabM (TSyntax `term) := do
  let scope ← notifyScope scope
  let ptr ← quoteSource ptr
  let rank ← quoteSource rank
  let signal ← quoteSource signal
  `(Call.notify $ptr $rank $signal $scope $op)

private def quoteCall (raw : Syntax) : TermElabM (Option (TSyntax `term)) := do
  if raw.isOfKind ``dlExpr then
    let expr : TSyntax `distributedCallExpr := ⟨raw[0]⟩
    return some (← match expr with
      | `(distributedCallExpr| dl.rank()) => `(Call.rank)
      | `(distributedCallExpr| dl.num_ranks()) => `(Call.numRanks)
      | `(distributedCallExpr| dl.symm_at($ptr:tritonExpr, $rank:tritonExpr)) => do
        let ptr ← quoteSource ptr
        let rank ← quoteSource rank
        `(Call.symmAt $ptr $rank)
      | `(distributedCallExpr| dl.consume_token($value:tritonExpr, $token:tritonExpr)) => do
        let value ← quoteSource value
        let token ← quoteSource token
        `(Call.consumeToken $value $token)
      | `(distributedCallExpr| dl.wait($ptr:tritonExpr, $count:tritonExpr, $scope:tritonExpr, $order:tritonExpr)) => do
        quoteWait ptr count scope order (← `(tritonExpr| 1))
      | `(distributedCallExpr| dl.wait($ptr:tritonExpr, $count:tritonExpr, $scope:tritonExpr, $order:tritonExpr, waitValue=$value:tritonExpr))
      | `(distributedCallExpr| dl.wait($ptr:tritonExpr, $count:tritonExpr, scope=$scope:tritonExpr, semantic=$order:tritonExpr, waitValue=$value:tritonExpr)) =>
        quoteWait ptr count scope order value
      | _ => throwErrorAt raw "unsupported dl expression")
  if raw.isOfKind ``dlStmt then
    let stmt : TSyntax `distributedCallStmt := ⟨raw[0]⟩
    return some (← match stmt with
      | `(distributedCallStmt| dl.notify($ptr:tritonExpr, $rank:tritonExpr, signal=$signal:tritonExpr, comm_scope=$scope:tritonExpr)) => do
        quoteNotify ptr rank signal scope (← `(SignalOp.set))
      | `(distributedCallStmt| dl.notify($ptr:tritonExpr, $rank:tritonExpr, signal=$signal:tritonExpr, sig_op=$op:tritonExpr, comm_scope=$scope:tritonExpr)) => do
        quoteNotify ptr rank signal scope (← signalOp op)
      | `(distributedCallStmt| with dl.simt_exec_region() as ($index:ident, $size:ident) { $_:tritonStmt* }) => do
        let index := quote index.getId.eraseMacroScopes
        let size := quote size.getId.eraseMacroScopes
        `(Call.simtRegion $index $size)
      | _ => throwErrorAt raw "unsupported dl statement")
  return none

-- Volatile loads are explicitly outside the signed A2.1 source subset.
private def checkVolatileLoads (stx : Syntax) : TermElabM Unit := do
  let hasVolatile (raw : Syntax) := match (⟨raw⟩ : TSyntax `tritonMemKwarg) with
    | `(tritonMemKwarg| $name:ident = $_:tritonExpr)
    | `(tritonMemKwarg| $name:ident = $_:tritonDType) => name.getId.eraseMacroScopes == `volatile
    | _ => Bool.false
  if let some load := stx.find? (fun raw =>
      raw.getArgs.any (fun arg => arg.isAtom && arg.getAtomVal == "tl.load(") &&
        (raw.find? hasVolatile).isSome) then
    let message := "tl.load: unknown kwarg `volatile`. Only `mask`, `other`, `dtype`, " ++
      "`boundary_check`, `padding_option`, and `eviction_policy` are recognized."
    throwErrorAt load message

-- These are the same source-helper passes used by the ordinary Triton block.
-- Run them for validation only and retain the original syntax and tree paths.
private def checkSourceCalls (stx : Syntax) : TermElabM Unit := do
  let `(triton { $stmts:tritonStmt* }) := stx | throwUnsupportedSyntax
  let checked ← liftMacroM do
    let normalized ← stmts.toList.mapM fun stmt =>
      return (⟨← Inference.normalizeControlFlow stmt.raw⟩ : TSyntax `tritonStmt)
    RandomProfile.prepare (← FiniteHelperSource.prepare normalized)
  -- The dotted zero-argument parser also admits excluded names. The finite
  -- helper pass consumes the supported dtype predicate in its declaration.
  if checked.any fun stmt =>
      (stmt.raw.find? (·.isOfKind ``tritonSourceIsFP64Dotted)).isSome then
    throwErrorAt stx "unexpected syntax{indentD stx}"

private partial def quoteSites (stx : Syntax) (path : List Nat)
    (sites : Array (TSyntax `term)) : TermElabM (Array (TSyntax `term)) := do
  let mut result := sites
  if let some call ← quoteCall stx then
    let path := quote path.reverse
    result := result.push (← `(Site.mk $path $call))
  for i in [:stx.getNumArgs] do
    result ← quoteSites stx[i] (i :: path) result
  return result

end VeriTile.Dist.Frontend.TritonDist.DL

namespace VeriTile.Dist.Frontend.TritonDist
open Lean Elab Term

@[scoped term_elab VeriTile.Triton.DSL.tritonBlock]
def elaborateDL : TermElab := fun stx expected => do
  let sites ← DL.quoteSites stx [] #[]
  if sites.isEmpty then throwUnsupportedSyntax
  checkPendingCalls stx
  DL.checkSourceCalls stx
  DL.checkVolatileLoads stx
  let block ← DL.quoteSource stx
  elabTerm (← `(DL.Source.mk $block [$sites,*])) expected

end VeriTile.Dist.Frontend.TritonDist
