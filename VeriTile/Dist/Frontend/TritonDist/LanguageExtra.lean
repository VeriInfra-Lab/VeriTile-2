import VeriTile.Dist.Frontend.TritonDist.Syntax
import VeriTile.Dist.Event.Access

/-!
The #81 rows of `documents/dist/TritonDistSubset.md`, at TD 7908e4ea9010.
The source evaluator supplies values and locations. These plans project to the
signed S1 locations and S2 events, with evidence from the signed call table:

| Lowering | Evidence |
| --- | --- |
| `tid` | E-TD8 |
| `laneid` | W3 |
| `__shfl_sync_i32` and `__shfl_up_sync_i32` | W4 → W3, M7 |
| `__syncthreads` | E-TD8, E-CU7, D8, M2 |
| `ld` and its empty spin | D5, A1(a), A3 |
| `ld_acquire` and its plain waits | A3, W1, `PrimitiveSources.md` §9 item 10 |
| `membar` | W2 |
| `st` | D5, A1(a), A8 for cross-GPU system-scope accesses |
| `atomic_add` | D5, A1(a,b) |
| `atomic_cas` and its grouped spin | D5, A1(a,b), A3, A8 for cross-GPU system-scope accesses |
| `tl.atomic_add` | E-TR1, A1(d) |

A proof relying on native atomicity for a system-scope operation on a word
accessed by threads on different GPUs must name A8, the platform condition
recorded in `documents/dist/PrimitiveSources.md` §7 (see I10 and E-CU5).
-/

namespace VeriTile.Dist.Frontend.TritonDist.LanguageExtra
open Lean Elab Term
open VeriTile.Triton.DSL
open scoped VeriTile.Dist.Frontend.TritonDist

inductive Axis where
  | x | y | z
  deriving DecidableEq

inductive Shuffle where
  | index | up

inductive MemoryOp (α : Type) where
  | load
  | store (value : α)
  | add (value : α)
  | compareExchange (expected replacement : α)

inductive Call where
  | tid (direction : Axis)
  | laneid
  | shuffle (kind : Shuffle) (mask value lane : Syntax)
  | barrier
  | membar
  | memory (ptr : Syntax) (mask : Option Syntax) (mode : Mode) (op : MemoryOp Syntax)
  | wait (ptr threshold : Syntax) (cmp : Cmp) (mode : Mode)
  | compareExchangeSpin (ptr expected replacement : Syntax) (mode : Mode)

/-- For a single CTA barrier invocation, the caller supplies the M2 phase and
the number of participating threads. The execution relation checks the roster. -/
structure CtaRound where
  phase : Nat
  threadCount : Nat

/-- Evaluated source operands at a call site. The lane count is the pointer
shape's size. The value lookup resolves scalar broadcasting at that shape.
A mask lookup must return precisely one boolean per pointer lane. Inactive
lanes never evaluate their pointer or value. -/
structure Context (α : Type) where
  agent : Agent
  symmetric : VeriTile.Triton.RegionName → Bool
  laneCount : Syntax → Option Nat
  evalAddr : Syntax → Nat → Option Addr
  evalValue : Syntax → Nat → Option α
  evalMask : Syntax → Option (List Bool)
  evalWordValue : Syntax → Option Nat
  threadCoord : Axis → Option Nat
  round : Option CtaRound := none

/-- The operation is one signed access per lane. The payload is retained for
the evaluator, since an S2 access event carries only the kind, location and
mode. -/
structure AccessPlan (α : Type) where
  lane : Nat
  addr : Addr
  mode : Mode
  op : MemoryOp α

/-- Project the access, optional write and optional return from the one
observed value. Addition uses the caller's arithmetic at the source dtype.
A failed strong CAS reads the observed value and leaves the cell unchanged. -/
def AccessPlan.observe [DecidableEq α] (p : AccessPlan α) (add : α → α → α) (old : α) :
    Event × Option α × Option α :=
  let event := fun kind => Event.access kind p.addr p.mode
  match p.op with
  | .load => (event .load, none, some old)
  | .store value => (event .store, some value, none)
  | .add value => (event .update, some (add old value), some old)
  | .compareExchange expected replacement =>
    if old = expected then (event .update, some replacement, some old)
    else (event .load, none, some old)

structure Barrier where
  cta : Cta
  round : CtaRound

def Barrier.events (b : Barrier) : List Event :=
  let counter := Counter.phase b.cta 0
  [.bump ⟨counter, .add, 1, .atomic .cta .release⟩,
   .wait counter .ge (b.round.phase * b.round.threadCount) (.atomic .cta .acquire)]

inductive Result (α : Type) where
  | scalar (value : Nat)
  | unspecified
  | accesses (plans : List (AccessPlan α))
  | barrier (plan : Barrier)
  | step (events : List Event)

private def evalAddr (ctx : Context α) (ptr : Syntax) (lane : Nat) : Option Addr := do
  let addr ← ctx.evalAddr ptr lane
  guard (AccessibleAt ctx.symmetric ctx.agent addr)
  return addr

private def evalOp (ctx : Context α) (lane : Nat) : MemoryOp Syntax → Option (MemoryOp α)
  | .load => some .load
  | .store value => (ctx.evalValue value lane).map .store
  | .add value => (ctx.evalValue value lane).map .add
  | .compareExchange expected replacement => do
    return .compareExchange (← ctx.evalValue expected lane) (← ctx.evalValue replacement lane)

private def scalarWord (ctx : Context α) (ptr : Syntax) : Option Counter := do
  guard ((← ctx.laneCount ptr) = 1)
  return .word (← evalAddr ctx ptr 0)

/-- Lower an evaluated source call. The two events of an A3 CAS spin
belong to one step; a CTA barrier's arrival and wait remain separate. -/
def Call.lower (ctx : Context α) : Call → Option (Result α)
  | .tid direction => do
    let .thread .. := ctx.agent | none
    return .scalar (← ctx.threadCoord direction)
  | .laneid => some .unspecified
  | .shuffle _ mask value lane => do
    discard (ctx.evalValue mask 0)
    discard (ctx.evalValue value 0)
    discard (ctx.evalValue lane 0)
    return .unspecified
  | .barrier => do
    let .thread c _ t := ctx.agent | none
    let round ← ctx.round
    guard (round.phase > 0 ∧ t < round.threadCount)
    return .barrier ⟨c, round⟩
  | .membar => some (.step [.fence .plain])
  | .memory ptr mask mode op => do
    let count ← ctx.laneCount ptr
    let active ← match mask with
      | some mask => ctx.evalMask mask
      | none => some (List.replicate count Bool.true)
    guard (active.length = count)
    let lanes := active.zipIdx.filterMap fun (enabled, i) => if enabled then some i else none
    let plans ← lanes.mapM fun lane => do
      return ⟨lane, ← evalAddr ctx ptr lane, mode, ← evalOp ctx lane op⟩
    return .accesses plans
  | .wait ptr threshold cmp mode => do
    let word ← scalarWord ctx ptr
    let n ← ctx.evalWordValue threshold
    return .step [.wait word cmp n mode]
  | .compareExchangeSpin ptr expected replacement mode => do
    let word ← scalarWord ctx ptr
    let expected ← ctx.evalWordValue expected
    let replacement ← ctx.evalWordValue replacement
    return .step [.wait word .eq expected mode, .bump ⟨word, .set, replacement, mode⟩]

structure Site where
  path : List Nat
  call : Call

structure Source where
  block : Syntax
  sites : List Site

private def literal (op field : String) (arg : TSyntax `tritonExpr) : TermElabM String := do
  let `(tritonExpr| $s:str) := arg | throwErrorAt arg "{op}: {field} must be a string literal"
  return s.getString

private inductive ScopedOp where
  | load | plainLoad | store | add | cas | tritonAdd

private def ScopedOp.label : ScopedOp → String
  | .load => "ld"
  | .plainLoad => "ld_acquire"
  | .store => "st"
  | .add => "atomic_add"
  | .cas => "atomic_cas"
  | .tritonAdd => "tl.atomic_add"

private def scopeTerm (op : ScopedOp) (arg : TSyntax `tritonExpr) : TermElabM (TSyntax `term) := do
  match op, ← literal op.label "scope" arg with
  | _, "gpu" => `(Scope.gpu)
  | _, "sys" => `(Scope.sys)
  | .cas, "cta" | .tritonAdd, "cta" => `(Scope.cta)
  | _, scope => throwErrorAt arg "{op.label}: unsupported scope '{scope}'"

private def atomicMode (op : ScopedOp) (scope semantic : TSyntax `tritonExpr) :
    TermElabM (TSyntax `term) := do
  let scope ← scopeTerm op scope
  let field := match op with | .tritonAdd => "sem" | _ => "semantic"
  let order ← match op, ← literal op.label field semantic with
    | _, "relaxed" => `(MemOrder.relaxed)
    | .store, "release" => `(MemOrder.release)
    | .load, "acquire" => `(MemOrder.acquire)
    | .add, "release" | .cas, "release" | .tritonAdd, "release" => `(MemOrder.release)
    | .add, "acquire" | .cas, "acquire" | .tritonAdd, "acquire" => `(MemOrder.acquire)
    | .add, "acq_rel" | .cas, "acq_rel" | .tritonAdd, "acq_rel" => `(MemOrder.acqRel)
    | _, order => throwErrorAt semantic "{op.label}: unsupported {field} '{order}'"
  `(Mode.atomic $scope $order)

private def quoteMemory (operand : QuoteOperand) (ptr : TSyntax `tritonExpr) (mode : TSyntax `term)
    (op : TermElabM (TSyntax `term)) (mask : Option (TSyntax `tritonExpr) := none) : TermElabM (TSyntax `term) := do
  let ptr ← operand .address ptr
  let op ← op
  let mask ← match mask with
    | none => `(none)
    | some mask => do
      let mask ← operand .value mask
      `(some $mask)
  `(Call.memory $ptr $mask $mode $op)

private def quoteAdd (operand : QuoteOperand) (op : ScopedOp) (ptr value scope semantic : TSyntax `tritonExpr)
    (mask : Option (TSyntax `tritonExpr) := none) : TermElabM (TSyntax `term) := do
  let mode ← atomicMode op scope semantic
  quoteMemory operand ptr mode (do
    let value ← operand .value value
    `(MemoryOp.add $value)) mask

private def quoteStore (operand : QuoteOperand) (ptr value : TSyntax `tritonExpr) (mode : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  quoteMemory operand ptr mode (do
    let value ← operand .value value
    `(MemoryOp.store $value))

private def quoteTid (direction : TSyntax `tritonExpr) : TermElabM (TSyntax `term) := do
  let `(tritonExpr| $n:num) := direction | throwErrorAt direction "tid: axis must be a literal 0, 1 or 2"
  match n.getNat with
  | 0 => `(Call.tid Axis.x)
  | 1 => `(Call.tid Axis.y)
  | 2 => `(Call.tid Axis.z)
  | _ => throwErrorAt direction "tid: axis must be a literal 0, 1 or 2"

private def quoteShuffle (operand : QuoteOperand) (kind : TSyntax `term) (mask value lane : TSyntax `tritonExpr) :
    TermElabM (TSyntax `term) := do
  let mask ← operand .value mask
  let value ← operand .value value
  let lane ← operand .nat lane
  `(Call.shuffle $kind $mask $value $lane)

def quoteExpr (operand : QuoteOperand) (expr : TSyntax `extraCallExpr) : TermElabM (TSyntax `term) := do
  match expr with
  | `(extraCallExpr| __shfl_sync_i32($m:tritonExpr, $v:tritonExpr, $i:tritonExpr)) =>
    quoteShuffle operand (← `(Shuffle.index)) m v i
  | `(extraCallExpr| __shfl_up_sync_i32($m:tritonExpr, $v:tritonExpr, $i:tritonExpr)) =>
    quoteShuffle operand (← `(Shuffle.up)) m v i
  | `(extraCallExpr| atomic_add($p:tritonExpr, $v:tritonExpr, semantic=$o:tritonExpr, scope=$s:tritonExpr))
  | `(extraCallExpr| atomic_add($p:tritonExpr, $v:tritonExpr, scope=$s:tritonExpr, semantic=$o:tritonExpr)) =>
    quoteAdd operand .add p v s o
  | `(extraCallExpr| atomic_cas($p:tritonExpr, $old:tritonExpr, $new:tritonExpr,
      $s:tritonExpr, $o:tritonExpr)) =>
    let mode ← atomicMode .cas s o
    quoteMemory operand p mode (do
      let old ← operand .value old
      let new ← operand .value new
      `(MemoryOp.compareExchange $old $new))
  | `(extraCallExpr| laneid()) => `(Call.laneid)
  | `(extraCallExpr| ld($p:tritonExpr)) =>
    quoteMemory operand p (← `(Mode.atomic Scope.gpu MemOrder.relaxed)) `(MemoryOp.load)
  | `(extraCallExpr| ld($p:tritonExpr, scope=$s:tritonExpr, semantic=$o:tritonExpr)) =>
    quoteMemory operand p (← atomicMode .load s o) `(MemoryOp.load)
  | `(extraCallExpr| ld_acquire($p:tritonExpr, $s:tritonExpr)) =>
    discard (scopeTerm .plainLoad s)
    quoteMemory operand p (← `(Mode.plain)) `(MemoryOp.load)
  | `(extraCallExpr| tid($a:tritonExpr)) | `(extraCallExpr| tid(axis=$a:tritonExpr)) =>
    quoteTid a
  | `(extraCallExpr| tl.atomic_add($p:tritonExpr, $v:tritonExpr, mask=$m:tritonExpr,
      sem=$o:tritonExpr, scope=$s:tritonExpr)) =>
    quoteAdd operand .tritonAdd p v s o (some m)
  | `(extraCallExpr| tl.atomic_add($p:tritonExpr, $v:tritonExpr, sem=$o:tritonExpr, scope=$s:tritonExpr)) =>
    quoteAdd operand .tritonAdd p v s o
  | _ => throwErrorAt expr "unsupported language_extra expression"

def quoteStmt (operand : QuoteOperand) (stmt : TSyntax `extraCallStmt) : TermElabM (TSyntax `term) := do
  match stmt with
  | `(extraCallStmt| __syncthreads()) => `(Call.barrier)
  | `(extraCallStmt| membar(scope=$s:tritonExpr)) =>
    let scope ← literal "membar" "scope" s
    unless ["cta", "gl", "sys"].contains scope do throwErrorAt s "membar: unsupported scope '{scope}'"
    `(Call.membar)
  | `(extraCallStmt| st($p:tritonExpr, $v:tritonExpr)) =>
    quoteStore operand p v (← `(Mode.atomic Scope.gpu MemOrder.relaxed))
  | `(extraCallStmt| st($p:tritonExpr, $v:tritonExpr, scope=$s:tritonExpr, semantic=$o:tritonExpr))
  | `(extraCallStmt| st($p:tritonExpr, $v:tritonExpr, semantic=$o:tritonExpr, scope=$s:tritonExpr)) =>
    quoteStore operand p v (← atomicMode .store s o)
  | `(extraCallStmt| atomic_add($p:tritonExpr, $v:tritonExpr, semantic=$o:tritonExpr, scope=$s:tritonExpr))
  | `(extraCallStmt| atomic_add($p:tritonExpr, $v:tritonExpr, scope=$s:tritonExpr, semantic=$o:tritonExpr)) =>
    quoteAdd operand .add p v s o
  | `(extraCallStmt| tl.atomic_add($p:tritonExpr, $v:tritonExpr, mask=$m:tritonExpr,
      sem=$o:tritonExpr, scope=$s:tritonExpr)) =>
    quoteAdd operand .tritonAdd p v s o (some m)
  | `(extraCallStmt| tl.atomic_add($p:tritonExpr, $v:tritonExpr, sem=$o:tritonExpr, scope=$s:tritonExpr)) =>
    quoteAdd operand .tritonAdd p v s o
  | _ => throwErrorAt stmt "unsupported language_extra statement"

private partial def unparen (expr : TSyntax `tritonExpr) : TSyntax `tritonExpr :=
  match expr with
  | `(tritonExpr| ($x:tritonExpr)) => unparen x
  | _ => expr

private def exitTest (cond : TSyntax `tritonExpr) :
    TermElabM (TSyntax `tritonExpr × TSyntax `tritonExpr × TSyntax `term) := do
  match unparen cond with
  | `(tritonExpr| $a:tritonExpr != $b:tritonExpr) => return (a, b, ← `(Cmp.eq))
  | `(tritonExpr| $a:tritonExpr == $b:tritonExpr) => return (a, b, ← `(Cmp.ne))
  | `(tritonExpr| $a:tritonExpr < $b:tritonExpr) => return (a, b, ← `(Cmp.ge))
  | `(tritonExpr| $a:tritonExpr <= $b:tritonExpr) => return (a, b, ← `(Cmp.gt))
  | `(tritonExpr| $a:tritonExpr > $b:tritonExpr) => return (a, b, ← `(Cmp.le))
  | `(tritonExpr| $a:tritonExpr >= $b:tritonExpr) => return (a, b, ← `(Cmp.lt))
  | _ => throwErrorAt cond "language_extra spin: expected a comparison with the loaded word"

def quoteSpin (operand : QuoteOperand) (cond : TSyntax `tritonExpr) : TermElabM (TSyntax `term) := do
  let (lhs, threshold, cmp) ← exitTest cond
  let poll := unparen lhs
  unless poll.raw.isOfKind ``pendingExtraExpr do
    throwErrorAt lhs "language_extra spin: expected ld, ld_acquire or atomic_cas on the left"
  let hasExtraCall (raw : Syntax) := (raw.find? (·.isOfKind ``pendingExtraExpr)).isSome
  -- The spin replaces the whole condition, so only the polling call may occur in it.
  if hasExtraCall threshold.raw || hasExtraCall poll.raw[0] then
    throwErrorAt cond "language_extra spin: condition must contain exactly one language_extra call"
  let call : TSyntax `extraCallExpr := ⟨poll.raw[0]⟩
  let wait := fun ptr mode => do
    let ptr ← operand .address ptr
    let threshold ← operand .nat threshold
    `(Call.wait $ptr $threshold $cmp $mode)
  match call with
  | `(extraCallExpr| ld($p:tritonExpr)) => wait p (← `(Mode.atomic Scope.gpu MemOrder.relaxed))
  | `(extraCallExpr| ld($p:tritonExpr, scope=$s:tritonExpr, semantic=$o:tritonExpr)) =>
    wait p (← atomicMode .load s o)
  | `(extraCallExpr| ld_acquire($p:tritonExpr, $s:tritonExpr)) =>
    discard (scopeTerm .plainLoad s)
    wait p (← `(Mode.plain))
  | `(extraCallExpr| atomic_cas($p:tritonExpr, $old:tritonExpr, $new:tritonExpr,
      $s:tritonExpr, $o:tritonExpr)) =>
    let `(tritonExpr| $_:tritonExpr != $_:tritonExpr) := unparen cond
      | throwErrorAt cond "atomic_cas spin: expected != comparison"
    unless (unparen old).raw == (unparen threshold).raw do
      throwErrorAt threshold "atomic_cas spin: compare against the CAS expected value"
    let mode ← atomicMode .cas s o
    let ptr ← operand .address p
    let old ← operand .nat old
    let new ← operand .nat new
    `(Call.compareExchangeSpin $ptr $old $new $mode)
  | _ => throwErrorAt cond "language_extra spin: expected ld, ld_acquire or atomic_cas"

private partial def quoteSites (stx : Syntax) (path : List Nat)
    (sites : Array (TSyntax `term)) : TermElabM (Array (TSyntax `term)) := do
  if stx.isOfKind ``extraSpinStmt && (stx[1].find? (·.isOfKind ``pendingExtraExpr)).isSome then
    let call ← quoteSpin quoteSourceOperand ⟨stx[1]⟩
    let pathTerm := quote path.reverse
    return sites.push (← `(Site.mk $pathTerm $call))
  let mut sites := sites
  if stx.isOfKind ``pendingExtraExpr then
    let call ← quoteExpr quoteSourceOperand ⟨stx[0]⟩
    let pathTerm := quote path.reverse
    sites := sites.push (← `(Site.mk $pathTerm $call))
  else if stx.isOfKind ``pendingExtraStmt then
    let call ← quoteStmt quoteSourceOperand ⟨stx[0]⟩
    let pathTerm := quote path.reverse
    sites := sites.push (← `(Site.mk $pathTerm $call))
  for i in [:stx.getNumArgs] do
    sites ← quoteSites stx[i] (i :: path) sites
  return sites

end VeriTile.Dist.Frontend.TritonDist.LanguageExtra

namespace VeriTile.Dist.Frontend.TritonDist
open Lean Elab Term

@[scoped term_elab VeriTile.Triton.DSL.tritonBlock]
def elaborateLanguageExtra : TermElab := fun stx expected => do
  checkFamilySource stx expected ``LanguageExtra.Source .extra
  let sites ← LanguageExtra.quoteSites stx [] #[]
  if sites.isEmpty then throwUnsupportedSyntax
  checkDistSourceCalls stx
  let block ← quoteDistSyntax stx
  elabTerm (← `(LanguageExtra.Source.mk $block [$sites,*])) expected

end VeriTile.Dist.Frontend.TritonDist
