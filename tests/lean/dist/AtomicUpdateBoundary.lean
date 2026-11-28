import VeriTile.Dist.Frontend.TritonDist.LanguageExtra
import VeriTile.Dist.Frontend.TritonDist.Shmem
import VeriTile.Dist.Frontend.TritonDist.DL
import VeriTile.Triton.DSL.CallSignature
import VeriTile.Meta.StatementAudit

namespace VeriTile.Tests.AtomicUpdateBoundary

open Lean VeriTile.Dist
open VeriTile.Dist.Frontend.TritonDist
open scoped VeriTile.Dist.Frontend.TritonDist

-- The real source collector and per-call lowering stop at S2. The caller
-- evaluates operands at each lane; no S3 emission or payload is invented here.
private def cta : Cta := ⟨0, [1]⟩
private def issuer : Agent := .thread cta 0 3
private def word0 : Addr := ⟨.global 0, ⟨"data"⟩, 4⟩
private def word2 : Addr := ⟨.global 0, ⟨"data"⟩, 6⟩

private def extraContext (values : Name → Nat → Option α) : LanguageExtra.Context α where
  agent := issuer
  symmetric := fun _ => Bool.false
  laneCount := fun ptr => some (if ptr[0].getId == `tile then 3 else 1)
  evalAddr := fun _ lane => match lane with
    | 0 => some word0
    | 2 => some word2
    | _ => none
  evalValue := fun raw lane => values raw[0].getId lane
  evalMask := fun mask => if mask[0].getId == `active then
    some [Bool.true, Bool.false, Bool.true] else none
  evalWordValue := fun _ => none
  threadCoord := fun _ => none

private def oneOperand (name : Name) (value : α) : Name → Nat → Option α :=
  fun n lane => if n == name && lane == 0 then some value else none

private def laneOperands (value0 value2 : α) : Name → Nat → Option α :=
  fun n lane => if n == `amount then
    match lane with
    | 0 => some value0
    | 2 => some value2
    | _ => none
  else none

private def observes [DecidableEq α] (source : LanguageExtra.Source)
    (ctx : LanguageExtra.Context α) (add : α → α → α) (old : Nat → α) :
    List (Option (List (Nat × Event × Option α × Option α))) :=
  source.sites.map fun site => do
    let .accesses plans ← site.call.lower ctx | none
    return plans.map fun p => (p.lane, p.observe add (old p.lane))

-- A1(b) and E-TD8/E-TD14: the adopted fetch-add reads the old value and
-- applies the source evaluator's addition to old and operand in that order.
theorem scopedAddUsesOldAndOperand {α : Type} [DecidableEq α]
    (add : α → α → α) (old amount : α) :
    observes (triton {
      previous = atomic_add(p, amount, semantic="acq_rel", scope="sys")
      atomic_add(p, amount, scope="sys", semantic="acq_rel")
    }) (extraContext (oneOperand `amount amount)) add (fun _ => old) =
    [some [(0, .access .update word0 (.atomic .sys .acqRel), some (add old amount), some old)],
     some [(0, .access .update word0 (.atomic .sys .acqRel), some (add old amount), some old)]] := rfl

-- E-TR1/A1(d): lane 1 has neither an evaluated address nor an operand. The
-- other two lanes use their own operands and observed values, not a scalar
-- copied from the first lane. The statement spelling is checked separately.
theorem maskedAddUsesEachLane {α : Type} [DecidableEq α]
    (add : α → α → α) (old0 old2 amount0 amount2 : α) :
    observes (triton {
      previous = tl.atomic_add(tile, amount, mask=active, sem="relaxed", scope="gpu")
      tl.atomic_add(p, amount, sem="release", scope="cta")
    }) (extraContext (laneOperands amount0 amount2)) add
      (fun lane => if lane == 0 then old0 else old2) =
    [some [(0, .access .update word0 (.atomic .gpu .relaxed), some (add old0 amount0), some old0),
           (2, .access .update word2 (.atomic .gpu .relaxed), some (add old2 amount2), some old2)],
     some [(0, .access .update word0 (.atomic .cta .release), some (add old0 amount0), some old0)]] := rfl

theorem noActiveLaneNoUpdate :
    observes (triton { previous = tl.atomic_add(tile, amount, mask=active, sem="relaxed", scope="gpu") })
      { extraContext (α := Nat) (fun _ _ => none) with
        evalAddr := fun _ _ => none,
        evalMask := fun _ => some [Bool.false, Bool.false, Bool.false] }
      Nat.add (fun _ => 17) = [some []] := rfl

private def casOperands (expected replacement : α) : Name → Nat → Option α :=
  fun n lane => if lane == 0 then
    if n == `expected then some expected
    else if n == `replacement then some replacement else none
  else none

private def casSource : LanguageExtra.Source :=
  triton { previous = atomic_cas(p, expected, replacement, "sys", "acquire") }

-- A1(b): a strong CAS writes the replacement only on success, returning the
-- observed value rather than the expected value or the replacement.
theorem casUsesExpectedAndReplacement {α : Type} [DecidableEq α]
    (add : α → α → α) (old expected replacement : α) :
    observes casSource (extraContext (casOperands expected replacement)) add (fun _ => old) =
    [some [(0, if old = expected then
      (.access .update word0 (.atomic .sys .acquire), some replacement, some old)
      else (.access .load word0 (.atomic .sys .acquire), none, some old))]] := rfl

theorem casSuccess {α : Type} [DecidableEq α]
    (add : α → α → α) (old replacement : α) :
    observes casSource (extraContext (casOperands old replacement)) add (fun _ => old) =
    [some [(0, .access .update word0 (.atomic .sys .acquire), some replacement, some old)]] := by
  rw [casUsesExpectedAndReplacement]
  simp

theorem casFailure {α : Type} [DecidableEq α]
    (add : α → α → α) (old expected replacement : α) (h : old ≠ expected) :
    observes casSource (extraContext (casOperands expected replacement)) add (fun _ => old) =
    [some [(0, .access .load word0 (.atomic .sys .acquire), none, some old)]] := by
  rw [casUsesExpectedAndReplacement]
  simp [h]

private def spinAccesses (source : LanguageExtra.Source) (expected replacement : Nat) :
    List (Option (List Event × List (AccessKind × Addr × Mode))) :=
  source.sites.map fun site => do
    let .step events ← site.call.lower
      { extraContext (casOperands expected replacement) with
        evalWordValue := fun raw => casOperands expected replacement raw[0].getId 0 } | none
    return (events, events.flatMap Event.accesses)

-- A3 uses the separately signed grouped wait/set pattern for an empty CAS spin.
theorem casSpinUsesWaitAndSet (expected replacement : Nat) :
    spinAccesses (triton {
      while (atomic_cas(p, expected, replacement, "sys", "release") != expected) { pass }
    }) expected replacement =
    [some ([.wait (.word word0) .eq expected (.atomic .sys .release),
      .bump ⟨.word word0, .set, replacement, .atomic .sys .release⟩],
      [(.load, word0, .atomic .sys .release), (.store, word0, .atomic .sys .release)])] := rfl

-- The independent compute is evaluated by the enclosing source evaluator.
-- Even with a release store, following a plain load by arithmetic and a store
-- at the same address does not turn the two calls into one RMW event.
theorem separateReadComputeWrite {α : Type} [DecidableEq α]
    (add : α → α → α) (old amount : α) :
    observes (triton {
      previous = ld_acquire(p, "sys")
      computed = previous + amount
      st(p, computed, scope="sys", semantic="release")
    }) (extraContext (oneOperand `computed (add old amount))) add (fun _ => old) =
    [some [(0, .access .load word0 .plain, none, some old)],
     some [(0, .access .store word0 (.atomic .sys .release), some (add old amount), none)]] := rfl

-- The base Triton frontend is also inspected; #82 still owns its projection
-- to distributed segments. These are the actual source-lowered core bodies.
open VeriTile.Triton

private def ordinarySignature : CallSignature where
  pointers := [("p", .fp32)]
  scalars := []
  constexpr := []

private def ordinaryRmw (p : RegionName) : ComputeKernel :=
  with_triton_signature ordinarySignature in triton {
    previous = tl.load(p)
    computed = previous + 1.0
    tl.store(p, computed)
  }

private def ordinaryAtomicAdd (p : RegionName) : ComputeKernel :=
  with_triton_signature ordinarySignature in triton {
    tl.atomic_add(p, 1.0)
  }

private def isSeparateRmw (k : ComputeKernel) : Bool :=
  match k.surfaceBody with
  | [.assign _ _ _ (.compute (.load .fp32 ..)),
     .assign _ _ _ (.compute (.alg .fp32 (.add ..))), .store ..] => Bool.true
  | _ => Bool.false

theorem ordinaryLoadComputeStore : isSeparateRmw (ordinaryRmw "p") = Bool.true := rfl
theorem ordinaryAtomicNotSeparate : isSeparateRmw (ordinaryAtomicAdd "p") = Bool.false := rfl

theorem ordinaryAtomicAddMarker (p : RegionName) :
    (match (ordinaryAtomicAdd p).surfaceBody with
      | [.atomicAdd ..] => Bool.true
      | _ => Bool.false) = Bool.true := rfl

-- These five documented base atomics elaborate to effect markers, not to
-- an executable algorithm. Pin the precise projection error for each.
theorem atomicMaxRejected (p : RegionName) :
    (triton {
      x := 1
      tl.atomic_max($(p), x)
    } : ComputeKernel).toAlgorithm? =
      Except.error (.requiresEffectProjection "tl.atomic_max") := rfl

theorem atomicMinRejected (p : RegionName) :
    (triton {
      x := 1
      tl.atomic_min($(p), x)
    } : ComputeKernel).toAlgorithm? =
      Except.error (.requiresEffectProjection "tl.atomic_min") := rfl

theorem atomicAndRejected (p : RegionName) :
    (triton {
      x := 1
      tl.atomic_and($(p), x)
    } : ComputeKernel).toAlgorithm? =
      Except.error (.requiresEffectProjection "tl.atomic_and") := rfl

theorem atomicOrRejected (p : RegionName) :
    (triton {
      x := 1
      tl.atomic_or($(p), x)
    } : ComputeKernel).toAlgorithm? =
      Except.error (.requiresEffectProjection "tl.atomic_or") := rfl

theorem atomicXorRejected (p : RegionName) :
    (triton {
      x := 1
      tl.atomic_xor($(p), x)
    } : ComputeKernel).toAlgorithm? =
      Except.error (.requiresEffectProjection "tl.atomic_xor") := rfl

-- Signals use the distinct S2 counter pattern, not a general MemCell function.
private def flag0 : Addr := ⟨.global 0, ⟨"flag"⟩, 3⟩
private def flag2 : Addr := ⟨.global 2, ⟨"flag"⟩, 3⟩
private def src0 : Addr := ⟨.global 0, ⟨"src"⟩, 0⟩
private def dst0 : Addr := ⟨.global 0, ⟨"dst"⟩, 0⟩
private def dst2 : Addr := ⟨.global 2, ⟨"dst"⟩, 0⟩

private def natOperand (amount : Nat) (raw : Syntax) : Option Nat :=
  match raw[0].getId with
  | `target => some 2
  | `amount => some amount
  | `nbytes => some 4
  | _ => none

private def dlContext (amount : Nat) : DL.CallContext where
  agent := issuer
  numRanks := 3
  blockSize := 32
  symmetric := fun _ => Bool.true
  evalAddr := fun raw => if raw[0].getId == `signal then some flag0 else none
  evalNat := natOperand amount

private def shmemContext (agent : Agent) (amount : Nat) : Shmem.Context where
  issuer := agent
  peCount := 3
  symmetric := fun _ => Bool.true
  evalNat := natOperand amount
  evalByteRange := fun raw bytes => do
    guard (bytes == 4)
    match raw[0].getId with
    | `src => some [src0]
    | `dst => some [dst0]
    | _ => none
  evalSignalWord := fun raw => if raw[0].getId == `signal then some flag0 else none
  collectiveReady := fun _ => Bool.true

private def bumpObservation (event : Event) (old : Nat) : Option (List (AccessKind × Addr × Mode) × Nat) := do
  let .bump b := event | none
  return (event.accesses, b.op.apply old b.amount)

private def dlObservations (source : DL.Source) (old amount : Nat) :
    List (Option (List (AccessKind × Addr × Mode) × Nat)) :=
  source.sites.map fun site => do
    let .event event ← site.call.lower (dlContext amount) | none
    bumpObservation event old

theorem notifyAddAndSet (old amount : Nat) :
    dlObservations (triton {
      dl.notify(signal, target, signal=amount, sig_op="add", comm_scope="gpu")
      dl.notify(signal, target, signal=amount, sig_op="set", comm_scope="intra_node")
    }) old amount =
    [some ([(.update, flag2, .atomic .gpu .release)], old + amount),
     some ([(.store, flag2, .atomic .sys .release)], amount)] := rfl

private def shmemLower (source : Shmem.Source) (agent : Agent) (amount : Nat) : Option Shmem.Result := do
  let [site] := source.sites | none
  site.call.lower (shmemContext agent amount)

private def signalObservation (source : Shmem.Source) (old amount : Nat) :
    Option (List (AccessKind × Addr × Mode) × Nat) := do
  let .event event ← shmemLower source (.cta cta) amount | none
  bumpObservation event old

theorem signalAdd (old amount : Nat) :
    signalObservation (triton {
      libshmem_device.signal_op(signal, amount, libshmem_device.NVSHMEM_SIGNAL_ADD, target)
    }) old amount = some ([(.update, flag2, .shmem .release)], old + amount) := rfl

theorem signalSet (old amount : Nat) :
    signalObservation (triton {
      libshmem_device.signal_op(signal, amount, libshmem_device.NVSHMEM_SIGNAL_SET, target)
    }) old amount = some ([(.store, flag2, .shmem .release)], amount) := rfl

private def completionObservation (source : Shmem.Source) (agent : Agent) (old amount : Nat) :
    Option (List (AccessKind × Addr × Mode) × List (AccessKind × Addr × Mode) × Nat) := do
  let .transfer plan ← shmemLower source agent amount | none
  let b ← plan.transfer.completion
  return ((Event.initiate plan.transfer).accesses, (Event.complete plan.transfer).accesses,
    b.op.apply old b.amount)

theorem blockingSignalAdd (old amount : Nat) :
    completionObservation (triton {
      libshmem_device.putmem_signal_block(dst, src, nbytes, signal, amount,
        libshmem_device.NVSHMEM_SIGNAL_ADD, target)
    }) (.cta cta) old amount =
    some ([(.load, src0, .plain)], [(.store, dst2, .plain), (.update, flag2, .shmem .release)],
      old + amount) := rfl

theorem nonblockingSignalAdd (old amount : Nat) :
    completionObservation (triton {
      libshmem_device.putmem_signal_nbi_block(dst, src, nbytes, signal, amount,
        libshmem_device.NVSHMEM_SIGNAL_ADD, target)
    }) (.cta cta) old amount =
    some ([], [(.store, dst2, .plain), (.load, src0, .plain), (.update, flag2, .shmem .release)],
      old + amount) := rfl

theorem warpSignalAdd (old amount : Nat) :
    completionObservation (triton {
      libshmem_device.putmem_signal_nbi_warp(dst, src, nbytes, signal, amount,
        libshmem_device.NVSHMEM_SIGNAL_ADD, target)
    }) (.group cta 0) old amount =
    some ([], [(.store, dst2, .plain), (.load, src0, .plain), (.update, flag2, .shmem .release)],
      old + amount) := rfl

theorem nonblockingSignalSet (old amount : Nat) :
    completionObservation (triton {
      libshmem_device.putmem_signal_nbi_block(dst, src, nbytes, signal, amount,
        libshmem_device.NVSHMEM_SIGNAL_SET, target)
    }) (.cta cta) old amount =
    some ([], [(.store, dst2, .plain), (.load, src0, .plain), (.store, flag2, .shmem .release)],
      amount) := rfl

#axiomsClean scopedAddUsesOldAndOperand
#axiomsClean maskedAddUsesEachLane
#axiomsClean noActiveLaneNoUpdate
#axiomsClean casUsesExpectedAndReplacement
#axiomsClean casSuccess
#axiomsClean casFailure
#axiomsClean casSpinUsesWaitAndSet
#axiomsClean separateReadComputeWrite
#axiomsClean ordinaryLoadComputeStore
#axiomsClean ordinaryAtomicNotSeparate
#axiomsClean ordinaryAtomicAddMarker
#axiomsClean atomicMaxRejected
#axiomsClean atomicMinRejected
#axiomsClean atomicAndRejected
#axiomsClean atomicOrRejected
#axiomsClean atomicXorRejected
#axiomsClean notifyAddAndSet
#axiomsClean signalAdd
#axiomsClean signalSet
#axiomsClean blockingSignalAdd
#axiomsClean nonblockingSignalAdd
#axiomsClean warpSignalAdd
#axiomsClean nonblockingSignalSet

end VeriTile.Tests.AtomicUpdateBoundary
