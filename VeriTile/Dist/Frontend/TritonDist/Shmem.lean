import VeriTile.Dist.Frontend.TritonDist.Syntax
import VeriTile.Dist.Event

/-! NVSHMEM calls in the signed A2.1 mapping in documents/dist/TritonDistSubset.md.
Evidence IDs refer to PrimitiveSources.md §4.2 and NVSHMEM 3.6.5.
The enclosing program evaluates the addresses, byte counts and launch operands. -/

namespace VeriTile.Dist.Frontend.TritonDist.Shmem
open Lean Elab Term
open VeriTile.Triton.DSL
open scoped VeriTile.Dist.Frontend.TritonDist

inductive CopyKind where
  | get (nbi : Bool)
  | put (nbi : Bool)
  | signalBlock (nbi : Bool) (word value : Syntax) (op : SignalOp)
  | signalWarp (word value : Syntax) (op : SignalOp)

inductive Call where
  | barrier
  | fence
  | copy (kind : CopyKind) (dst src bytes pe : Syntax)
  | signalOp (word value pe : Syntax) (op : SignalOp)
  | signalWait (word value : Syntax) (cmp : Cmp)

/-- The team key identifies this team in this invocation. Phases start at one. -/
structure TeamRound where
  key : Nat
  phase : Nat

/-- Operands from the calling program. A byte range resolves to complete
model cells in transfer order. The signal resolver checks the 64-bit word.
collectiveReady supplies the E-NV16 participation and uniform-arguments check
for this collective invocation. -/
structure Context where
  issuer : Agent
  peCount : Nat
  symmetric : VeriTile.Triton.RegionName → Bool
  evalNat : Syntax → Option Nat
  evalByteRange : Syntax → Nat → Option (List Addr)
  evalSignalWord : Syntax → Option Addr
  collectiveReady : Call → Bool
  teamRound : Option TeamRound := none

/-- One transfer issued by the collective agent (D4). Only blocking gets
return with their matching completion in the initiation step (M1, E-NV6). -/
structure TransferPlan where
  issuer : Agent
  transfer : Transfer
  completesInCall : Bool

def TransferPlan.callStep (p : TransferPlan) : List Event :=
  if p.completesInCall then [.initiate p.transfer, .complete p.transfer]
  else [.initiate p.transfer]

/-- A PE rendezvous with successive phase thresholds (M2). D2 and D7
apply through the signed synchronization relation. -/
structure Barrier where
  issuer : Agent
  round : TeamRound
  peCount : Nat

def Barrier.counter (b : Barrier) : Counter :=
  .rendezvous (2 * b.round.key + 1)

def Barrier.events (b : Barrier) : List Event :=
  [.bump ⟨b.counter, .add, 1, .shmem .release⟩,
   .wait b.counter .ge (b.round.phase * b.peCount) (.shmem .acquire)]

/-- M6 requires each earlier transfer of the same issuer to have its own
matching completion. The caller supplies occurrence identities, including
those of signalling puts, and the relation to their matching completions. -/
def Barrier.ReturnsAfterTransfers {Occurrence : Type} (b : Barrier)
    (earlier : List (Agent × Occurrence)) (completed : Occurrence → Prop) : Prop :=
  ∀ op, (b.issuer, op) ∈ earlier → completed op

inductive Result where
  | transfer (plan : TransferPlan)
  | event (event : Event)
  | barrier (plan : Barrier)

private def isBlock : Agent → Bool
  | .cta _ => Bool.true
  | _ => Bool.false

private def isWarp : Agent → Bool
  | .group _ _ => Bool.true
  | _ => Bool.false

private def localCell (issuer : Agent) (addr : Addr) : Bool :=
  match addr.space with
  | .global rank => rank == issuer.rankOf
  | _ => decide (Accessible issuer addr.space)

private def remoteWord (ctx : Context) (p : Syntax) (pe : Rank) : Option Addr := do
  let addr ← ctx.evalSignalWord p
  guard (addr.space = .global ctx.issuer.rankOf)
  symmAt ctx.symmetric addr pe

private def delivered (issuer : Agent) : Bump :=
  ⟨.delivered issuer, .add, 1, .shmem .release⟩

private def lowerCopy (ctx : Context) (kind : CopyKind) (dst src bytes pe : Syntax) :
    Option TransferPlan := do
  let usesWarp := match kind with | .signalWarp .. => Bool.true | _ => Bool.false
  guard ((if usesWarp then isWarp ctx.issuer else isBlock ctx.issuer) &&
    ctx.collectiveReady (.copy kind dst src bytes pe))
  let pe ← ctx.evalNat pe
  guard (pe < ctx.peCount)
  let bytes ← ctx.evalNat bytes
  let dst ← ctx.evalByteRange dst bytes
  let src ← ctx.evalByteRange src bytes
  guard (src.length = dst.length)
  guard (src.all (localCell ctx.issuer) && dst.all (localCell ctx.issuer))
  let peer := fun cells : List Addr => cells.mapM fun addr => symmAt ctx.symmetric addr pe
  match kind with
  | .get nbi =>
    return ⟨ctx.issuer, ⟨← peer src, dst, nbi, some (delivered ctx.issuer)⟩, !nbi⟩
  | .put nbi =>
    return ⟨ctx.issuer, ⟨src, ← peer dst, nbi, some (delivered ctx.issuer)⟩, Bool.false⟩
  | .signalBlock nbi word value op =>
    let word ← remoteWord ctx word pe
    let value ← ctx.evalNat value
    return ⟨ctx.issuer, ⟨src, ← peer dst, nbi, some ⟨.word word, op, value, .shmem .release⟩⟩,
      Bool.false⟩
  | .signalWarp word value op =>
    let word ← remoteWord ctx word pe
    let value ← ctx.evalNat value
    return ⟨ctx.issuer,
      ⟨src, ← peer dst, Bool.true, some ⟨.word word, op, value, .shmem .release⟩⟩, Bool.false⟩

/-- The signed S1/S2 interpretation. Fence ordering and matching of completions
are obligations of the caller's execution relation. -/
def Call.lower (ctx : Context) : Call → Option Result
  | .copy kind dst src bytes pe => (lowerCopy ctx kind dst src bytes pe).map Result.transfer
  | .fence => some (.event (.fence (.shmem .release)))
  | .barrier => do
    guard (isBlock ctx.issuer && ctx.collectiveReady .barrier)
    let round ← ctx.teamRound
    guard (0 < round.phase ∧ 0 < ctx.peCount)
    return .barrier ⟨ctx.issuer, round, ctx.peCount⟩
  | .signalOp word value pe op => do
    let pe ← ctx.evalNat pe
    guard (pe < ctx.peCount)
    let word ← remoteWord ctx word pe
    let value ← ctx.evalNat value
    return .event (.bump ⟨.word word, op, value, .shmem .release⟩)
  | .signalWait word value cmp => do
    let word ← remoteWord ctx word ctx.issuer.rankOf
    let value ← ctx.evalNat value
    return .event (.wait (.word word) cmp value (.shmem .acquire))

/-- Calls are keyed by their syntax-tree paths for the segment frontend (#82). -/
structure Site where
  path : List Nat
  call : Call

structure Source where
  block : Syntax
  sites : List Site

private def constantName (label : String) (arg : TSyntax `tritonExpr) : TermElabM Name := do
  let `(tritonExpr| $name:ident) := arg
    | throwErrorAt arg "{label} must be a named NVSHMEM constant"
  return name.getId.eraseMacroScopes

private def signalOpTerm (arg : TSyntax `tritonExpr) : TermElabM (TSyntax `term) := do
  match ← constantName "NVSHMEM signal operation" arg with
  | `libshmem_device.NVSHMEM_SIGNAL_SET => `(SignalOp.set)
  | `libshmem_device.NVSHMEM_SIGNAL_ADD => `(SignalOp.add)
  | op => throwErrorAt arg "unsupported NVSHMEM signal operation '{op}'"

private def cmpTerm (arg : TSyntax `tritonExpr) : TermElabM (TSyntax `term) := do
  match ← constantName "NVSHMEM signal comparison" arg with
  | `libshmem_device.NVSHMEM_CMP_EQ => `(Cmp.eq)
  | `libshmem_device.NVSHMEM_CMP_NE => `(Cmp.ne)
  | `libshmem_device.NVSHMEM_CMP_GE => `(Cmp.ge)
  | `libshmem_device.NVSHMEM_CMP_LE => `(Cmp.le)
  | `libshmem_device.NVSHMEM_CMP_GT => `(Cmp.gt)
  | `libshmem_device.NVSHMEM_CMP_LT => `(Cmp.lt)
  | cmp => throwErrorAt arg "unsupported NVSHMEM signal comparison '{cmp}'"

private def ptrSyntax (ptr : TSyntax `shmemPtr) : Syntax :=
  match ptr with
  | `(shmemPtr| $expr:tritonExpr) => expr.raw
  | _ => ptr.raw

private def quoteCopy (dst src : TSyntax `shmemPtr) (bytes pe : TSyntax `tritonExpr) (kind : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let dst ← quoteDistSyntax (ptrSyntax dst)
  let src ← quoteDistSyntax (ptrSyntax src)
  let bytes ← quoteDistSyntax bytes
  let pe ← quoteDistSyntax pe
  `(Call.copy $kind $dst $src $bytes $pe)

private def quoteSignalCopy (dst src : TSyntax `shmemPtr) (bytes word value op pe : TSyntax `tritonExpr)
    (kind : TSyntax `term) : TermElabM (TSyntax `term) := do
  let word ← quoteDistSyntax word
  let value ← quoteDistSyntax value
  let op ← signalOpTerm op
  let kind ← `($kind $word $value $op)
  quoteCopy dst src bytes pe kind

private def quoteCall (st : TSyntax `shmemCallStmt) : TermElabM (TSyntax `term) := do
  match st with
  | `(shmemCallStmt| libshmem_device.barrier_all_block()) => `(Call.barrier)
  | `(shmemCallStmt| libshmem_device.fence()) => `(Call.fence)
  | `(shmemCallStmt| libshmem_device.getmem_block(
      $dst:shmemPtr, $src:shmemPtr, $bytes:tritonExpr, $pe:tritonExpr)) => do
    quoteCopy dst src bytes pe (← `(CopyKind.get Bool.false))
  | `(shmemCallStmt| libshmem_device.getmem_nbi_block(
      $dst:shmemPtr, $src:shmemPtr, $bytes:tritonExpr, $pe:tritonExpr)) => do
    quoteCopy dst src bytes pe (← `(CopyKind.get Bool.true))
  | `(shmemCallStmt| libshmem_device.putmem_block(
      $dst:shmemPtr, $src:shmemPtr, $bytes:tritonExpr, $pe:tritonExpr)) => do
    quoteCopy dst src bytes pe (← `(CopyKind.put Bool.false))
  | `(shmemCallStmt| libshmem_device.putmem_nbi_block(
      $dst:shmemPtr, $src:shmemPtr, $bytes:tritonExpr, $pe:tritonExpr)) => do
    quoteCopy dst src bytes pe (← `(CopyKind.put Bool.true))
  | `(shmemCallStmt| libshmem_device.putmem_signal_block(
      $dst:shmemPtr, $src:shmemPtr, $bytes:tritonExpr, $word:tritonExpr,
      $value:tritonExpr, $op:tritonExpr, $pe:tritonExpr)) => do
    quoteSignalCopy dst src bytes word value op pe (← `(CopyKind.signalBlock Bool.false))
  | `(shmemCallStmt| libshmem_device.putmem_signal_nbi_block(
      $dst:shmemPtr, $src:shmemPtr, $bytes:tritonExpr, $word:tritonExpr,
      $value:tritonExpr, $op:tritonExpr, $pe:tritonExpr)) => do
    quoteSignalCopy dst src bytes word value op pe (← `(CopyKind.signalBlock Bool.true))
  | `(shmemCallStmt| libshmem_device.putmem_signal_nbi_warp(
      $dst:shmemPtr, $src:shmemPtr, $bytes:tritonExpr, $word:tritonExpr,
      $value:tritonExpr, $op:tritonExpr, $pe:tritonExpr)) => do
    quoteSignalCopy dst src bytes word value op pe (← `(CopyKind.signalWarp))
  | `(shmemCallStmt| libshmem_device.signal_op(
      $word:tritonExpr, $value:tritonExpr, $op:tritonExpr, $pe:tritonExpr)) => do
    let word ← quoteDistSyntax word
    let value ← quoteDistSyntax value
    let pe ← quoteDistSyntax pe
    let op ← signalOpTerm op
    `(Call.signalOp $word $value $pe $op)
  | `(shmemCallStmt| libshmem_device.signal_wait_until(
      $word:tritonExpr, $cmp:tritonExpr, $value:tritonExpr)) => do
    let word ← quoteDistSyntax word
    let value ← quoteDistSyntax value
    let cmp ← cmpTerm cmp
    `(Call.signalWait $word $value $cmp)
  | _ => throwErrorAt st "unsupported NVSHMEM call"

private partial def quoteSites (stx : Syntax) (path : List Nat)
    (sites : Array (TSyntax `term)) : TermElabM (Array (TSyntax `term)) := do
  let mut sites := sites
  if stx.isOfKind ``pendingShmemStmt then
    let call ← quoteCall ⟨stx[0]⟩
    let path := quote path.reverse
    sites := sites.push (← `(Site.mk $path $call))
  for i in [:stx.getNumArgs] do
    sites ← quoteSites stx[i] (i :: path) sites
  return sites

end VeriTile.Dist.Frontend.TritonDist.Shmem

namespace VeriTile.Dist.Frontend.TritonDist
open Lean Elab Term

@[scoped term_elab VeriTile.Triton.DSL.tritonBlock]
def elaborateShmem : TermElab := fun stx expected => do
  let sites ← Shmem.quoteSites stx [] #[]
  if sites.isEmpty then throwUnsupportedSyntax
  checkPendingCalls stx (some "#80")
  if let some dl := stx.find? (fun s => s.isOfKind ``dlExpr || s.isOfKind ``dlStmt) then
    throwErrorAt dl "mixed dl and NVSHMEM blocks require the segment frontend (#82)"
  checkDistSourceCalls stx
  let block ← quoteDistSyntax stx
  elabTerm (← `(Shmem.Source.mk $block [$sites,*])) expected

end VeriTile.Dist.Frontend.TritonDist
