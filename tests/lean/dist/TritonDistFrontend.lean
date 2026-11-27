import VeriTile.Dist.Frontend.TritonDist.Segments
import VeriTile.Triton.DSL.CallSignature

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
       .branch "__triton_dist_control_0_0_0_condition" [.site ⟨0, .shmem .fence, [], none, none⟩] _],
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

/-- error: dl.consume_token: expected a token bound by an earlier dl.wait in this block -/
#guard_msgs in
example : Body := triton { x = dl.consume_token(2, missingToken) }

/-- error: dl.consume_token: expected a token bound by an earlier dl.wait in this block -/
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

#print axioms mixedSites
#print axioms mixedRegisterFlow
#print axioms controlRegisters
#print axioms byteViewRegisters
#print axioms operandEvaluationOrder
#print axioms waitLink
#print axioms a3Spins

end
end VeriTile.Tests.TritonDistFrontend
