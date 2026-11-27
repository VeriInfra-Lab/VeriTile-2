import VeriTile.Dist.Frontend.TritonDist.LanguageExtra
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

example : lower (triton { membar(scope="gl") membar(scope="sys") }) =
    [some (.step [.fence .plain]), some (.step [.fence .plain])] := rfl

-- D5 and A1(a): ld/st default to GPU/relaxed, preserving explicit modes.
example : observe (triton {
    a = ld(p)
    b = ld(p, semantic="acquire", scope="sys")
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

example : lower (triton { while ld(p, semantic="acquire", scope="sys") != 1 {} }) =
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

theorem ldAcquireNoSync (reach : ShmemReach) (writer : Agent × Event) :
    ¬ SyncEdge reach word writer (thread, .wait (.word word) .ge 8 .plain) :=
  not_syncEdge_of_plain (Or.inr rfl)

theorem ldAcquireConflictsWithSignal (writer : Agent) :
    Conflict
      (thread, .wait (.word word) .ge 8 .plain)
      (writer, .bump ⟨.word word, .set, 8, .shmem .release⟩) :=
  conflict_of_plain (kind := .load) (kind' := .store) (p := word)
    (mode := .shmem .release) (by simp [Event.accesses])
    (by simp [Event.accesses, Bump.accesses, SignalOp.kind]) (Or.inr rfl)

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

/-- error: atomic_cas spin: compare against the CAS expected value -/
#guard_msgs in
#check (triton { while atomic_cas(p, 0, 1, "sys", "acquire") != 1 { pass } } : LanguageExtra.Source)

#guard_msgs in
run_cmd do
  for body in ["x = laneid(1)", "x = __shfl_sync_i32(mask, value)",
      "x = __shfl_up_sync_i32(mask, value)", "__syncthreads(1)",
      "__fence(\"acq_rel\", \"sys\")", "x = load_v4_u32(p)"] do
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

#axiomsClean syncthreadsCtaPhase
#axiomsClean maskedAtomicAddReturnsPrevious
#axiomsClean groupedCasSpin
#axiomsClean ldAcquirePlainWaits
#axiomsClean ldAcquireNoSync
#axiomsClean ldAcquireConflictsWithSignal

end VeriTile.Tests.TritonDistLanguageExtra
