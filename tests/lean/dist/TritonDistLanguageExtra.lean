import VeriTile.Staging.Dist.TritonDistProgram
import VeriTile.Meta.StatementAudit

namespace VeriTile.Tests.TritonDistLanguageExtra
open Lean Elab Command
open VeriTile.Dist
open VeriTile.Dist.Frontend.TritonDist
open scoped VeriTile.Dist.Frontend.TritonDist

private def cta : Cta := ⟨1, [2]⟩
private def thread : Agent := .thread cta 0 3
private def word : Addr := ⟨.global 1, ⟨"signal"⟩, 5⟩
private def otherWord : Addr := ⟨.global 1, ⟨"signal"⟩, 7⟩

private def context : LanguageExtra.Context Nat where
  agent := thread
  symmetric := fun _ => Bool.false
  laneCount := fun raw => some (if raw[0].getId == `tile then 3 else 1)
  evalAddr := fun _ lane =>
    match lane with
    | 0 => some word
    | 2 => some otherWord
    | _ => none
  evalValue := fun raw lane =>
    if lane == 1 then none
    else match raw[0][0].getAtomVal with
      | "0" => some 0
      | "1" => some 1
      | "2" => some 2
      | _ => some 6
  evalMask := fun _ => some [Bool.true, Bool.false, Bool.true]
  evalWordValue := fun raw =>
    match raw[0][0].getAtomVal with
    | "0" => some 0
    | "1" => some 1
    | _ => some 8
  threadCoord := fun
    | .x => some 3
    | .y => some 1
    | .z => some 0
  round := some ⟨2, 32⟩

private def lower (source : LanguageExtra.Source)
    (ctx : LanguageExtra.Context Nat := context) : List (Option (LanguageExtra.Result Nat)) :=
  source.sites.map fun site => site.call.lower ctx

private def observe (source : LanguageExtra.Source) (old : Nat := 19) :
    List (Option (List (Nat × Event × Option Nat × Option Nat))) :=
  (lower source).map fun
    | some (.accesses plans) => some (plans.map fun plan => (plan.lane, plan.observe Nat.add old))
    | _ => none

-- E-TD8: the axis selects a coordinate, not a lane ID. W3/M7 returns no
-- information about either shuffle result or laneid.
example : lower (triton {
    x = tid(0)
    y = tid(axis=1)
    z = tid(2)
    lane = laneid()
    a = __shfl_sync_i32(0xFFFFFFFF, value, 1)
    b = __shfl_up_sync_i32(0xFFFFFFFF, value, 2)
  }) = [some (.scalar 3), some (.scalar 1), some (.scalar 0),
    some .unspecified, some .unspecified, some .unspecified] := rfl

example : lower
    (triton { a = __shfl_sync_i32(mask, value, 1) b = __shfl_up_sync_i32(mask, value, 1) })
    { context with evalValue := fun _ _ => none } = [none, none] := rfl

/-- E-TD8, E-CU7, D8 and M2: the next CTA phase has its own threshold. -/
theorem syncthreadsCtaPhase :
    ((lower (triton { __syncthreads() })).head?).bind
      (·.bind fun result => match result with | .barrier plan => some plan.events | _ => none) =
    some [.bump ⟨.phase cta 0, .add, 1, .atomic .cta .release⟩,
      .wait (.phase cta 0) .ge 64 (.atomic .cta .acquire)] := rfl

example : lower (triton { __syncthreads() })
    { context with round := some ⟨0, 32⟩ } = [none] := rfl

example : lower (triton { __syncthreads() })
    { context with agent := .cta cta } = [none] := rfl

private theorem barrierRequiresParticipant :
    lower (triton { __syncthreads() }) { context with round := some ⟨2, 3⟩ } = [none] := rfl

private theorem loadRequiresAccessibleAddress :
    lower (triton { x = ld(p) })
      { context with evalAddr := fun _ _ => some { word with space := .global 2 } } = [none] := rfl

private theorem spinRequiresSingleLane :
    lower (triton { while ld(tile) != 1 {} }) = [none] := rfl

example : lower (triton { membar(scope="gl") membar(scope="sys") }) =
    [some (.step [.fence .plain]), some (.step [.fence .plain])] := rfl

-- D5 and A1(a): ld/st default to GPU/relaxed, preserving explicit modes.
private theorem loadAndStoreModes : observe (triton {
    a = ld(p)
    b = ld(p, scope="sys", semantic="acquire")
    st(p, 1)
    st(p, 2, semantic="release", scope="sys")
    st(p, 1, scope="gpu", semantic="release")
  }) =
    [some [(0, .access .load word (.atomic .gpu .relaxed), none, some 19)],
     some [(0, .access .load word (.atomic .sys .acquire), none, some 19)],
     some [(0, .access .store word (.atomic .gpu .relaxed), some 1, none)],
     some [(0, .access .store word (.atomic .sys .release), some 2, none)],
     some [(0, .access .store word (.atomic .gpu .release), some 1, none)]] := rfl

-- D5 and A1(b): binding or discarding an add does not change the operation.
example : observe (triton {
    previous = atomic_add(p, 1, semantic="release", scope="gpu")
    atomic_add(p, 1, scope="gpu", semantic="release")
  }) = List.replicate 2 (some [(0, .access .update word (.atomic .gpu .release), some 20, some 19)]) := rfl

-- E-TR1 and A1(d): the mask skips lane 1 entirely and preserves lane
-- indices for the returned old values.
theorem maskedAtomicAddReturnsPrevious :
    observe (triton { previous = tl.atomic_add(tile, 1, mask=active, sem="relaxed", scope="gpu") }) =
    [some [(0, .access .update word (.atomic .gpu .relaxed), some 20, some 19),
           (2, .access .update otherWord (.atomic .gpu .relaxed), some 20, some 19)]] := rfl

example : observe (triton { tl.atomic_add(p, 1, sem="release", scope="gpu") }) =
    [some [(0, .access .update word (.atomic .gpu .release), some 20, some 19)]] := rfl

example : lower (triton { x = tl.atomic_add(tile, 1, mask=active, sem="relaxed", scope="gpu") })
    { context with evalMask := fun _ => some [Bool.true] } = [none] := rfl

example : lower (triton { x = tl.atomic_add(tile, 1, mask=active, sem="relaxed", scope="gpu") })
    { context with evalMask := fun _ => some [Bool.true, Bool.true, Bool.true] } = [none] := rfl

-- Strong CAS observes and returns the old value on both branches.
example : observe (triton { previous = atomic_cas(p, 0, 1, "sys", "acquire") }) 0 =
    [some [(0, .access .update word (.atomic .sys .acquire), some 1, some 0)]] := rfl
example : observe (triton { previous = atomic_cas(p, 0, 1, "sys", "acquire") }) 2 =
    [some [(0, .access .load word (.atomic .sys .acquire), none, some 2)]] := rfl

/-- A3: the CAS spin's wait and successful set are one step. -/
theorem groupedCasSpin :
    lower (triton { while (atomic_cas(p, 0, 1, "sys", "release") != 0) { pass } }) =
    [some (.step [.wait (.word word) .eq 0 (.atomic .sys .release),
      .bump ⟨.word word, .set, 1, .atomic .sys .release⟩])] := rfl

private theorem explicitPollingMode :
    lower (triton { while ld(p, scope="sys", semantic="acquire") != 1 {} }) =
    [some (.step [.wait (.word word) .eq 1 (.atomic .sys .acquire)])] := rfl

-- W1/A3: neither polling compare adds CUDA acquire semantics.
theorem ldAcquirePlainWaits :
    lower (triton {
      while ld_acquire(p, "sys") != 2 * world_size { pass }
      while ld_acquire(p, "sys") < num_push_pids { pass }
    }) = [some (.step [.wait (.word word) .eq 8 .plain]),
          some (.step [.wait (.word word) .ge 8 .plain])] := rfl

example : observe (triton { value = ld_acquire(p, "sys") }) =
    [some [(0, .access .load word .plain, none, some 19)]] := rfl

section InterNodePolling
open VeriTile.Triton

set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

-- Reduced polling and writer shapes from Triton-distributed 7908e4ea,
-- all_to_all_vdev_2d_offset_inter_node.py:183–202,203–231,235–237,288–292.
-- Use two nodes with two ranks each. Rank 3 writes the data flag on relay
-- rank 1, which rank 0 polls at the slot for source node 1.
private def exchangePoll (flag : RegionName) (worldSize : Nat) : Body := triton {
  while ld_acquire(flag, "sys") != $((2 : Nat)) * $(worldSize) { pass }
}

private def dataPoll (flags : RegionName) (relay node pushPids : Nat) : Body := triton {
  remote = dl.symm_at(flags, $(relay))
  while ld_acquire(remote + $(node), "sys") < $(pushPids) { pass }
}

private noncomputable def projectPoll (reader : Agent) (body : Body) : Option (Agent × Event) := do
  let args : LaunchArgs := {
    agent := reader, numRanks := 4, symmetric := fun _ => Bool.true
    waitReading := .eq, order := fun _ _ => Equiv.refl _, wholeCta := Bool.false }
  let flat ← projectFlat args 1 body.start default
  let [emission] := flat.filterMap Sum.getRight? | none
  return (emission.actor, emission.event)

private def exchangeFlag : Addr := ⟨.global 1, "metadata", 0⟩
private def dataFlag : Addr := ⟨.global 1, "data", 1⟩

private noncomputable def exchangeReader : Agent × Event :=
  (projectPoll (.cta ⟨1, [0]⟩) (exchangePoll exchangeFlag.region 4)).get (by rfl')

private noncomputable def dataReader : Agent × Event :=
  (projectPoll (.thread ⟨0, [2]⟩ 0 0) (dataPoll dataFlag.region 1 1 8)).get (by rfl')

private def writerContext (issuer : Agent) (flag : Addr) : Shmem.Context where
  issuer := issuer
  peCount := 4
  symmetric := fun _ => Bool.true
  evalNat := fun expr =>
    match expr[0][0].getAtomVal with
    | "1" => some 1
    | "8" => some 8
    | _ => none
  evalByteRange := fun expr bytes => do
    guard (bytes = 8)
    match expr[0].getId with
    | `dst => some [⟨.global issuer.rankOf, "recv", 0⟩]
    | `src => some [⟨.global issuer.rankOf, "send", 0⟩]
    | _ => none
  evalSignalWord := fun expr =>
    if expr[0].getId == `flag then some { flag with space := .global issuer.rankOf } else none
  collectiveReady := fun _ => Bool.true

private def lowerSignalWriter (ctx : Shmem.Context) (source : Shmem.Source) :
    Option (Agent × Event) := do
  let [site] := source.sites | none
  match ← site.call.lower ctx with
  | .event event => return (ctx.issuer, event)
  -- The asynchronous transfer writes the signal when it completes.
  | .transfer plan => return (plan.issuer, .complete plan.transfer)
  | .barrier _ => none

private def exchangeWriter : Agent × Event :=
  (lowerSignalWriter (writerContext (.group ⟨0, [0]⟩ 1) exchangeFlag) (triton {
    libshmem_device.putmem_signal_nbi_warp(dst, src, 8, flag, 1,
      libshmem_device.NVSHMEM_SIGNAL_ADD, 1)
  })).get (by rfl)

private def dataWriter : Agent × Event :=
  (lowerSignalWriter (writerContext (.thread ⟨3, [1]⟩ 0 0) dataFlag) (triton {
    libshmem_device.signal_op(flag, 1, libshmem_device.NVSHMEM_SIGNAL_ADD, 1)
  })).get (by rfl)

theorem ldAcquireNoSync (reach : ShmemReach) :
    (¬ SyncEdge reach exchangeFlag exchangeWriter exchangeReader) ∧
    (¬ SyncEdge reach dataFlag dataWriter dataReader) := by
  constructor
  · exact not_syncEdge_of_plain (c := .word exchangeFlag) (Or.inr (by rfl'))
  · exact not_syncEdge_of_plain (c := .word dataFlag) (Or.inr (by rfl'))

theorem ldAcquireConflictsWithSignal :
    Conflict exchangeReader exchangeWriter ∧ Conflict dataReader dataWriter := by
  constructor
  · exact conflict_of_plain (kind := .load) (kind' := .update) (p := exchangeFlag)
      (mode := .shmem .release)
      (by rw [show exchangeReader.2.accesses = [(.load, exchangeFlag, .plain)] by rfl']; simp)
      (by decide) (Or.inr rfl)
  · exact conflict_of_plain (kind := .load) (kind' := .update) (p := dataFlag)
      (mode := .shmem .release)
      (by rw [show dataReader.2.accesses = [(.load, dataFlag, .plain)] by rfl']; simp)
      (by decide) (Or.inr rfl)

end InterNodePolling

/-- error: tid: axis must be a literal 0, 1 or 2 -/
#guard_msgs in
#check (triton { x = tid(3) } : LanguageExtra.Source)

/-- error: membar: unsupported scope 'cluster' -/
#guard_msgs in
#check (triton { membar(scope="cluster") } : LanguageExtra.Source)

/-- error: ld: unsupported scope 'cluster' -/
#guard_msgs in
#check (triton { x = ld(p, scope="cluster", semantic="acquire") } : LanguageExtra.Source)

/-- error: ld_acquire: unsupported scope 'cluster' -/
#guard_msgs in
#check (triton { x = ld_acquire(p, "cluster") } : LanguageExtra.Source)

/-- error: st: unsupported semantic 'seq_cst' -/
#guard_msgs in
#check (triton { st(p, 1, scope="sys", semantic="seq_cst") } : LanguageExtra.Source)

/-- error: atomic_add: unsupported semantic 'seq_cst' -/
#guard_msgs in
#check (triton { x = atomic_add(p, 1, scope="gpu", semantic="seq_cst") } : LanguageExtra.Source)

/-- error: tl.atomic_add: unsupported sem 'seq_cst' -/
#guard_msgs in
#check (triton { x = tl.atomic_add(p, 1, sem="seq_cst", scope="gpu") } : LanguageExtra.Source)

/-- error: atomic_cas: unsupported scope 'cluster' -/
#guard_msgs in
#check (triton { x = atomic_cas(p, 0, 1, "cluster", "acquire") } : LanguageExtra.Source)

/-- error: ld: unsupported scope 'cta' -/
#guard_msgs in
#check (triton { x = ld(p, scope="cta", semantic="relaxed") } : LanguageExtra.Source)

/-- error: ld: unsupported semantic 'acq_rel' -/
#guard_msgs in
#check (triton { while ld(p, scope="gpu", semantic="acq_rel") != 1 {} } : LanguageExtra.Source)

/-- error: ld_acquire: unsupported scope 'cta' -/
#guard_msgs in
#check (triton { x = ld_acquire(p, "cta") } : LanguageExtra.Source)

/-- error: st: unsupported semantic 'acq_rel' -/
#guard_msgs in
#check (triton { st(p, 1, scope="sys", semantic="acq_rel") } : LanguageExtra.Source)

/-- error: st: unsupported scope 'cta' -/
#guard_msgs in
#check (triton { st(p, 1, scope="cta", semantic="release") } : LanguageExtra.Source)

/-- error: atomic_add: unsupported scope 'cta' -/
#guard_msgs in
#check (triton { x = atomic_add(p, 1, scope="cta", semantic="release") } : LanguageExtra.Source)

/-- error: language_extra spin: condition must contain exactly one language_extra call -/
#guard_msgs in
#check (triton { while ld(p) < ld(q) {} } : LanguageExtra.Source)

/-- error: language_extra spin: condition must contain exactly one language_extra call -/
#guard_msgs in
#check (triton { while ld(ld(p)) != 1 {} } : LanguageExtra.Source)

/-- error: atomic_cas spin: compare against the CAS expected value -/
#guard_msgs in
#check (triton { while atomic_cas(p, 0, 1, "sys", "acquire") != 1 { pass } } : LanguageExtra.Source)

#guard_msgs in
run_cmd do
  for body in ["x = laneid(1)", "x = __shfl_sync_i32(mask, value)",
      "x = __shfl_up_sync_i32(mask, value)", "__syncthreads(1)"] do
    if let .ok stx := Parser.runParserCategory (← getEnv) `term ("triton { " ++ body ++ " }") then
      if (stx.find? fun n => n.isOfKind ``pendingExtraExpr || n.isOfKind ``pendingExtraStmt).isSome then
        throwError "unexpected language_extra form: {body}"
      let error? ← liftTermElabM do
        try
          discard <| Term.withoutErrToSorry
            (Term.elabTermAndSynthesize stx (some (mkConst ``LanguageExtra.Source)))
          return none
        catch e => return some (← e.toMessageData.toString)
      unless error?.any (fun message => !message.isEmpty) do
        throwError "expected a diagnostic for {body}"

#guard_msgs in
run_cmd do
  let .error message := Parser.runParserCategory (← getEnv) `term
      "triton { __fence(\"acq_rel\", \"sys\") }"
    | throwError "unexpected __fence parse"
  unless message.startsWith "<input>:1:16: expected " do
    throwError "unexpected __fence parser diagnostic: {message}"

/-- error: random source helper requires an explicit tl.source_helper binding -/
#guard_msgs in
#check (triton { x = load_v4_u32(p) } : LanguageExtra.Source)

#guard_msgs in
run_cmd do
  if let .ok stx := Parser.runParserCategory (← getEnv) `term
      "triton { x = ld(p, semantic=\"acquire\", scope=\"sys\") }" then
    if (stx.find? (·.isOfKind ``pendingExtraExpr)).isSome then
      throwError "unexpected semantic-first ld surface"

#axiomsClean syncthreadsCtaPhase
#axiomsClean maskedAtomicAddReturnsPrevious
#axiomsClean groupedCasSpin
#axiomsClean ldAcquirePlainWaits
#axiomsClean ldAcquireNoSync
#axiomsClean ldAcquireConflictsWithSignal

end VeriTile.Tests.TritonDistLanguageExtra
