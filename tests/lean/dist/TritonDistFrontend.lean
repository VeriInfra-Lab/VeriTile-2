-- Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a tutorials/01-distributed-notify-wait.py:83-116,123-146
-- Licence: MIT
-- Changes: transcribed to Lean; producer and consumer excerpts for two inputs and one scalar slot
import VeriTile.Dist.Frontend.TritonDist.Segments
import VeriTile.Triton.DSL.CallSignature
import VeriTile.Staging.Dist.TritonDistProgram
import tests.lean.dist.Tutorial01

namespace VeriTile.Tests.TritonDistFrontend

open Lean Elab Command Term
open VeriTile.Triton VeriTile.Triton.DSL VeriTile.Dist

private def parseBlock (env : Environment) (s : String) :=
  Parser.runParserCategory env `term ("triton { " ++ s ++ " }")

-- RawBodyControl is imported by CallSignature. Exercise the same normalization
-- pass as its call-signature elaborator with the distributed scope closed.
/-- error: affine while requires a final counter increment -/
#guard_msgs in
run_cmd do
  let `(triton { $stmts:tritonStmt* }) ← `(triton { while x < n { } })
    | throwError "expected the base while production"
  liftTermElabM <| liftMacroM <| discard (RawBodyControl.normalize stmts[0]!.raw)

/-- error: affine while requires a final counter increment -/
#guard_msgs in
#check (with_triton_signature ({} : CallSignature) in
  triton { while x < n { } } : ComputeKernel)

#guard_msgs in
run_cmd do
  let .error diagnostic := parseBlock (← getEnv) "while flag != 1 { pass }"
    | throwError "unexpected base pass production"
  unless diagnostic.endsWith "expected '%', '*=', '+=', ',', '-=', '/=', ':', ':=' or '='" do
    throwError "unexpected base pass diagnostic: {diagnostic}"

section
open VeriTile.Dist.Frontend.TritonDist
open scoped VeriTile.Dist.Frontend.TritonDist

private def mixed (p : RegionName) : Body := triton {
  tl.region p = tl.int32
  r = dl.rank()
  offset = r + $((1 : Nat))
  value = ld(p + offset)
  tl.debug_barrier()
  libshmem_device.fence()
  next = value
}

private def siteSummary (site : CallSite) : Nat × String × List RegName × Option RegName :=
  let tag := match site.call with
    | .dl .rank => "rank"
    | .extra (.memory _ _ _ .load) => "ld"
    | .shmem .fence => "fence"
    | _ => "unexpected"
  (site.id, tag, site.operands, site.dest.map (·.name))

private def flatSites (body : Body) : List CallSite :=
  body.nodes.filterMap fun node => match node with | .site site => some site | _ => none

theorem mixedSites (p : RegionName) :
    (flatSites (mixed p)).map siteSummary =
      [(0, "rank", [], some "__triton_dist_site0_result"),
       (1, "ld", ["__triton_dist_site1_arg0"], some "__triton_dist_site1_result"),
       (2, "fence", [], none)] := rfl

private def registerFlow (nodes : List Node) : Bool :=
  match nodes with
  | .site _ :: .code
      [.assign .nat [] "r" (.ref .nat [] "__triton_dist_site0_result"),
       .assign .nat [] "offset" _,
       .assign .ptr [] "__triton_dist_site1_arg0" _] :: .site _ :: rest =>
    (rest.any fun node => match node with
      | .code (.assign _ _ "value" (.ref _ _ "__triton_dist_site1_result") :: _) => Bool.true
      | _ => Bool.false)
  | _ => Bool.false

theorem mixedRegisterFlow (p : RegionName) : registerFlow (mixed p).nodes = Bool.true := rfl

private def nested (n : Nat) : Body := triton {
  tl.for i in $(n) {
    if i == 0 {
      libshmem_device.fence()
    } else {
      tl.debug_barrier()
    }
  }
  tl.for j in 1 { k = j }
}

private def nestedShape (nodes : List Node) : Bool :=
  match nodes with
  | [.code [.assign .nat [] "__triton_dist_control_0_stop" _],
     .loop "i" (.counted "__triton_dist_control_0_stop") [
       .code [.assign .bool [] "__triton_dist_control_0_0_0_condition" _],
       .branch "__triton_dist_control_0_0_0_condition" [.site ⟨0, .shmem .fence, [], none, none, []⟩] _],
     .code [.forLoop "j" 1 _]] => Bool.true
  | _ => Bool.false

theorem controlRegisters (n : Nat) : nestedShape (nested n).nodes = Bool.true := rfl

private def byteCopy (dst src : RegionName) : Body := triton {
  rank = dl.rank()
  libshmem_device.getmem_nbi_block(tl.cast(dst, tl.pointer_type(tl.int8)) + 4, src, 16, rank)
}

private def copyRegisters (site : CallSite) : Option (Name × List RegName) :=
  match site.call with
  | .shmem (.copy (.get Bool.true) dst _ _ _) => some (dst.getKind, site.operands)
  | _ => none

theorem byteViewRegisters (dst src : RegionName) :
    (flatSites (byteCopy dst src)).map copyRegisters =
      [none, some (``shmemByteView, ["__triton_dist_site1_arg0", "__triton_dist_site1_arg1",
        "__triton_dist_site1_arg2", "__triton_dist_site1_arg3", "__triton_dist_site1_arg4"])] := rfl

private def nestedOperands (p : RegionName) : Body := triton {
  prior = atomic_add(dl.symm_at(p, 0), dl.rank(), semantic="release", scope="gpu")
}

private def nestedSiteKind (site : CallSite) : String :=
  match site.call with
  | .dl (.symmAt ..) => "symm_at"
  | .dl .rank => "rank"
  | .extra (.memory _ _ _ (.add _)) => "atomic_add"
  | _ => "unexpected"

theorem operandEvaluationOrder (p : RegionName) :
    (flatSites (nestedOperands p)).map nestedSiteKind = ["symm_at", "rank", "atomic_add"] := rfl

-- C1 exercises the base kwarg checker on a mixed block.
/-- error: tl.load: unknown kwarg `foo`. Only `mask`, `other`, `dtype`, `boundary_check`, `padding_option`, and `eviction_policy` are recognized. -/
#guard_msgs in
example (p : RegionName) : Body := triton {
  rank = dl.rank()
  x = tl.load(p + 0, foo=1)
}

-- C2 and D4 distinguish a parser rejection from an elaboration rejection.
#guard_msgs in
run_cmd for (src, suffix) in [
    ("r = dl.rank() tok = dl.wait(p, 1, \"gpu\", \"acquire\", 2)", "expected 'waitValue'"),
    ("r = dl.rank() libshmem_device.quiet()", "expected '%', '*=', '+=', ',', '-=', '/=', ':', ':=' or '='")] do
  let .error diagnostic := parseBlock (← getEnv) src
    | throwError "unexpected parser acceptance: {src}"
  unless diagnostic.endsWith suffix do
    throwError "unexpected parser diagnostic: {diagnostic}"

/-- error: random source helper requires an explicit tl.source_helper binding -/
#guard_msgs in
example : Body := triton {
  r = dl.rank()
  x = dl.allocate_smem(1)
}

/-- error: random source helper requires an explicit tl.source_helper binding -/
#guard_msgs in
example : Body := triton {
  r = dl.rank()
  x = dl.rank(1)
}

/-- error: dl.consume_token: expected a token bound by an earlier dl.wait in this agent -/
#guard_msgs in
example : Body := triton { x = dl.consume_token(2, missingToken) }

/-- error: dl.consume_token: expected a token bound by an earlier dl.wait in this agent -/
#guard_msgs in
example (p : RegionName) : Body := triton {
  tok = dl.wait(p, 1, "gpu", "acquire")
  tok = 0
  x = dl.consume_token(2, tok)
}

private def linked (p : RegionName) : Body := triton {
  tok = dl.wait(p, 2, scope="gpu", semantic="acquire", waitValue=7)
  x = dl.consume_token(3, tok)
}

theorem waitLink (p : RegionName) :
    (flatSites (linked p)).map (·.waitSource) = [none, some 0] := rfl

/-- error: TritonDist: empty while requires a language_extra polling call -/
#guard_msgs in
example : Body := triton { while x < n { } }

/-- error: TritonDist: empty while requires a language_extra polling call -/
#guard_msgs in
example : Body := triton { while flag != 1 { pass } }

private def spins (p : RegionName) : Body := triton {
  while ld(p) < 1 { }
  while ld_acquire(p, "gpu") != 2 { pass }
  while atomic_cas(p, 3, 4, "gpu", "acq_rel") != 3 { }
}

private def addr : Addr := ⟨.global 0, ⟨"test"⟩, 1⟩

private def spinContext : LanguageExtra.Context Nat where
  agent := .cta ⟨0, [0]⟩
  symmetric := fun _ => Bool.true
  evalValue := fun _ _ => some 0
  evalMask := fun _ => some [Bool.true]
  evalWordValue := fun stx =>
    match stx[0].getId with
    | `__triton_dist_site0_arg1 => some 1
    | `__triton_dist_site1_arg1 => some 2
    | `__triton_dist_site2_arg1 => some 3
    | `__triton_dist_site2_arg2 => some 4
    | _ => none
  laneCount := fun _ => some 1
  evalAddr := fun _ _ => some addr
  threadCoord := fun _ => none

private def spinEvents (s : CallSite) : Option (List Event) := do
  let .extra call := s.call | none
  let .step events ← call.lower spinContext | none
  return events

private def nestedToken (p : RegionName) : Body := triton {
  tok = dl.wait(p, 1, "gpu", "acquire")
  for i in range(1) {
    x = dl.consume_token(i, tok)
  }
}

theorem enclosingWaitLink (p : RegionName) :
    (nestedToken p).nodes.any (fun n => match n with
      | .loop _ _ ns => ns.any fun child => match child with
        | .site site => site.waitSource == some 0
        | _ => Bool.false
      | _ => Bool.false) = Bool.true := rfl

/-- error: dl.consume_token: expected a token bound by an earlier dl.wait in this agent -/
#guard_msgs in
example (p : RegionName) : Body := triton {
  for i in range(1) { tok = dl.wait(p, 1, "gpu", "acquire") }
  x = dl.consume_token(2, tok)
}

/-- error: dl.consume_token: expected a token bound by an earlier dl.wait in this agent -/
#guard_msgs in
example (p : RegionName) : Body := triton {
  tok = dl.wait(p, 1, "gpu", "acquire")
  for tok in range(1) { x = dl.consume_token(2, tok) }
}

private def implicitPorts (p : RegionName) : Body := triton {
  v = ld(p)
  st(p, v)
}

theorem basePortMetadata (p : RegionName) :
    ((implicitPorts p).inputs, (implicitPorts p).outputs) = ([p], []) := rfl

/--
error: unexpected syntax
  triton {r = dl.rank()x = dl.extract()}
-/
#guard_msgs in
example : Body := triton {
  r = dl.rank()
  x = dl.extract()
}

/-- error: TritonDist: duplicate cut marker for site 1 -/
#guard_msgs in
run_cmd do
  -- Marker 1 is present at two positions in the recovered base list.
  match checkCutCoverage [0, 1] [0, 1, 1] with
  | .ok () => pure ()
  | .error msg => throwError "{msg}"

/-- error: TritonDist: missing cut marker for site 1 -/
#guard_msgs in
run_cmd do
  match checkCutCoverage [0, 1] [0] with
  | .ok () => pure ()
  | .error msg => throwError "{msg}"

set_option maxRecDepth 4096 in
theorem a3Spins (p : RegionName) :
    (flatSites (spins p)).map spinEvents =
      [some [.wait (.word addr) .ge 1 (.atomic .gpu .relaxed)],
       some [.wait (.word addr) .eq 2 .plain],
       some [.wait (.word addr) .eq 3 (.atomic .gpu .acqRel),
         .bump ⟨.word addr, .set, 4, .atomic .gpu .acqRel⟩]] := rfl

/--
error: TritonDist: base kernel cannot project to algorithm statements
  Except.error (EraseDTypeError.requiresEffectProjection "tl.async_wait")
-/
#guard_msgs in
example : Body := triton {
  r = dl.rank()
  tl.async_wait()
}

-- Q8 excludes mixed CTA and thread-program granularity.
/-- error: TritonDist: CTA-level __syncthreads requires a whole-CTA agent -/
#guard_msgs in
example : Body := triton {
  __syncthreads()
  with dl.simt_exec_region() as (lane, size) {
    __syncthreads()
  }
}

private def launchArgs (a : Agent) (reading : DL.WaitReading := .eq) : LaunchArgs :=
  { agent := a, numRanks := 2, symmetric := fun _ => Bool.true
    waitReading := reading, order := fun _ _ => Equiv.refl _, wholeCta := Bool.true }

private def flatEvents (program : List (Stmt ⊕ Emission)) : List Event :=
  program.filterMap fun item => item.getRight?.map (·.event)

private def twoWords (p : RegionName) : Body := triton {
  token = dl.wait(p, 2, "gpu", "acquire", waitValue=3)
}

private def signalWord (offset : Nat) : Counter := .word ⟨.global 0, "signal", offset⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem waitBothOrders :
    let cfg := launchArgs Tutorial01.producer .ge
    let reversed := { cfg with order := fun _ _ => ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩ }
    let cursor := (twoWords "signal").start
    let first := Event.wait (signalWord 0) .ge 3 (.atomic .gpu .acquire)
    let second := Event.wait (signalWord 1) .ge 3 (.atomic .gpu .acquire)
    (projectFlat cfg 2 cursor default).map flatEvents = some [first, second] ∧
    (projectFlat reversed 2 cursor default).map flatEvents = some [second, first] :=
  by constructor <;> rfl'

private def symmLoad (p : RegionName) : Body := triton {
  peerPtr = dl.symm_at(p, 1)
  v = tl.load(peerPtr, dtype=tl.uint64)
}

private def readDistinctRanks : BlockState :=
  { (default : BlockState) with mem := fun region _ =>
      ⟨TileDType.nat, if (ViewName.address Tutorial01.producer region 0).space = Space.global 1
        then 19 else 7⟩ }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem peerLoad :
    (((symmLoad "queue").start.prepare (launchArgs Tutorial01.producer) readDistinctRanks).bind
      fun cut => (cut.evaluated.state.regs .nat [] "v").map (·.data PUnit.unit)) = some 19 := by rfl'

private def producerBody (inputPtr queuePtr signalPtr : RegionName) : Body := triton {
  rank = dl.rank()
  numRanks = dl.num_ranks()
  peer = (rank + $((1 : Nat))) % numRanks
  input = inputPtr + $((0 : Nat))
  tl.for i in 2 {
    queueOffset = i % $((1 : Nat))
    queueRepeat = i // $((1 : Nat))
    token = dl.wait(dl.symm_at(signalPtr, peer) + queueOffset, 1, "gpu", "acquire",
      waitValue=queueRepeat * $((2 : Nat)))
    input = dl.consume_token(input, token)
    data = tl.load(input + i)
    tl.store(dl.symm_at(queuePtr, peer) + queueOffset, data)
    __syncthreads()
    libshmem_device.fence()
    dl.notify(signalPtr + queueOffset, peer, signal=queueRepeat * $((2 : Nat)) + $((1 : Nat)),
      sig_op="set", comm_scope="intra_node")
  }
}

private def consumerBody (outputPtr queuePtr signalPtr : RegionName) : Body := triton {
  rank = dl.rank()
  queueBase = queuePtr + $((0 : Nat))
  tl.for i in 2 {
    queueOffset = i % $((1 : Nat))
    queueRepeat = i // $((1 : Nat))
    token = dl.wait(signalPtr + queueOffset, 1, "gpu", "acquire",
      waitValue=queueRepeat * $((2 : Nat)) + $((1 : Nat)))
    queueBase = dl.consume_token(queueBase, token)
    data = tl.load(queueBase + queueOffset)
    tl.store(outputPtr + i, data)
    __syncthreads()
    libshmem_device.fence()
    dl.notify(signalPtr + queueOffset, rank, signal=queueRepeat * $((2 : Nat)) + $((2 : Nat)),
      sig_op="set", comm_scope="intra_node")
  }
}

private def t01Events (cmp : Cmp) (a : Agent) : List Event :=
  (Tutorial01.events cmp (fun _ => 0) a).filterMap (fun item =>
    match item.event with
    | .access .. => none
    | event => some event)

private noncomputable def producerFlat (r : DL.WaitReading) : Option (List (Stmt ⊕ Emission)) :=
  projectFlat (launchArgs Tutorial01.producer r) 10
    (producerBody "input" "queue" "signal").start default

private noncomputable def consumerFlat (r : DL.WaitReading) : Option (List (Stmt ⊕ Emission)) :=
  projectFlat (launchArgs Tutorial01.consumer r) 10
    (consumerBody "output" "queue" "signal").start default

-- K1 represents its queue accesses by explicit access events. The composed
-- source keeps the queue load/store as Triton code, so compare the waits,
-- CTA phase pairs, fences and notifies to the synchronization skeleton.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem tutorial01Producer :
    (producerFlat .eq).map flatEvents = some (t01Events .eq Tutorial01.producer) ∧
    (producerFlat .ge).map flatEvents = some (t01Events .ge Tutorial01.producer) :=
  by constructor <;> rfl'

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem tutorial01Consumer :
    (consumerFlat .eq).map flatEvents = some (t01Events .eq Tutorial01.consumer) ∧
    (consumerFlat .ge).map flatEvents = some (t01Events .ge Tutorial01.consumer) :=
  by constructor <;> rfl'

private def plainKernel : Kernel :=
  ⟨[], [], [.assign .nat [] "x" (.constNat 3)]⟩

theorem singlePlainSegment :
    (projectPlain plainKernel).map (slice Tutorial01.producer) =
      some [.inl (Segment.ofStmts Tutorial01.producer plainKernel.body)] :=
  projectPlain_noSync Tutorial01.prodCta plainKernel rfl

private def atomicKernel : Kernel :=
  ⟨[], [], [.forLoop "i" 1 [.atomicAdd .nat [] (.region "counter" (.constNat 0))
    (.constNat 1) .none]]⟩

theorem plainProjectionRejectsAtomic : (projectPlain atomicKernel).isNone = Bool.true := rfl

#print axioms singlePlainSegment
#print axioms plainProjectionRejectsAtomic

#print axioms waitBothOrders
#print axioms peerLoad
#print axioms tutorial01Producer
#print axioms tutorial01Consumer

#print axioms mixedSites
#print axioms mixedRegisterFlow
#print axioms controlRegisters
#print axioms byteViewRegisters
#print axioms operandEvaluationOrder
#print axioms waitLink
#print axioms a3Spins
#print axioms enclosingWaitLink
#print axioms basePortMetadata

end
end VeriTile.Tests.TritonDistFrontend
