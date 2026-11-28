import VeriTile.Staging.Dist.SegmentSpec
import VeriTile.Dist.Frontend.TritonDist.Segments

/-! Bridge from composed Triton-distributed bodies to the signed S3 program.
This is the one staging module that kernel transcriptions may import while
the S3 execution types live in staging (decision Q1 of #82, gate #704).
Main frontend modules depend only on S1/S2, never on this bridge. -/

namespace VeriTile.Dist.Frontend.TritonDist

open VeriTile.Triton

def SiteEvent.emission (a : Agent) (e : SiteEvent) : Emission :=
  ⟨a, e.event, e.store.map AccessValue.store |>.getD .noValue⟩

private noncomputable def enterDist (args : LaunchArgs) (pc : Cursor) (σ : DistState) :
    Option DistState := do
  if pc.returned.isNone then return σ
  let entered ← pc.enter (σ.view args.agent)
  return σ.setView args.agent entered

private noncomputable def prepareIn (args : LaunchArgs) (pc : Cursor) (σ : DistState) :
    Option CutResult := do
  guard args.agent.cta?.isSome
  guard (σ.numRanks = args.numRanks)
  pc.prepare args (σ.view args.agent)

/-- Build the segment selected by the same preparation that produces its
next event. A failed projection has a failed run. The signed Next type has
no error case, and Step tests the run before taking the continuation. -/
noncomputable def agentProgram (args : LaunchArgs) : AgentProgram Cursor where
  segment pc := {
    agent := args.agent
    run := fun σ => do
      let cut ← prepareIn args pc σ
      let start ← enterDist args pc σ
      (Segment.ofStmts args.agent cut.evaluated.code).run start
    reads := fun σ => match prepareIn args pc σ, enterDist args pc σ with
      | some cut, some start => (Segment.ofStmts args.agent cut.evaluated.code).reads start
      | _, _ => ∅
    writes := fun σ => match prepareIn args pc σ, enterDist args pc σ with
      | some cut, some start => (Segment.ofStmts args.agent cut.evaluated.code).writes start
      | _, _ => ∅ }
  next pc σ := match (prepareIn args pc σ).bind (·.next) with
    | none => .finish
    | some (group, rest) =>
      .emitGroup (group.head.emission args.agent) (group.tail.map (·.emission args.agent))
        (rest.resume group)

/-- A finite projection of a closed path. A bound counts cuts, rather than
ordinary statements. Paths that need a runtime event return or an indivisible
multi-event group use the cursor program. -/
private noncomputable def projectFlatGo (args : LaunchArgs) :
    Nat → Cursor → BlockState → Option (List (Stmt ⊕ Emission))
  | 0, pc, state => do
    let prepared ← pc.prepare args state
    guard prepared.next.isNone
    return prepared.evaluated.code.map Sum.inl
  | remaining + 1, pc, state => do
    let prepared ← pc.prepare args state
    let code := prepared.evaluated.code.map Sum.inl
    match prepared.next with
    | none => return code
    | some (group, rest) =>
      guard (group.tail.isEmpty && group.readLane.isNone)
      let suffix ← projectFlatGo args remaining rest prepared.evaluated.state
      return code ++ [.inr (group.head.emission args.agent)] ++ suffix

noncomputable def projectFlat (args : LaunchArgs)
    (cuts : Nat) (pc : Cursor) (state : BlockState) : Option (List (Stmt ⊕ Emission)) := do
  let c ← args.agent.cta?
  projectFlatGo args cuts pc { state with pids := DistState.programIds c.pid }

/-- A successful flat projection supplies the body run by `AgentProgram.ofBody`.
Its traces are the slices of that body, using the signed S3.3 statement (#45).
Agreement with the cursor program is tracked by #724. -/
theorem flat_steps (args : LaunchArgs) (pc : Cursor) (state : BlockState) (cuts : Nat)
    (trace : List (Segment ⊕ Event)) :
    (projectFlat args cuts pc state).map
      (fun flat => (AgentProgram.ofBody args.agent).Steps flat trace) =
    (projectFlat args cuts pc state).map (fun flat => trace = slice args.agent flat) := by
  cases projectFlat args cuts pc state with
  | none => rfl
  | some flat => exact congrArg some (propext (AgentProgram.ofBody_steps args.agent flat trace))

/-- The plain-kernel entry point uses the existing algorithm body directly.
Atomics are left to the S3 bridge in #696. -/
def projectPlain (k : Kernel) : Option (List (Stmt ⊕ Emission)) :=
  if noAtomicStmts k.body then some (k.body.map Sum.inl) else none

theorem projectPlain_noSync (c : Cta) (k : Kernel) (h : noAtomicStmts k.body = Bool.true) :
    (projectPlain k).map (slice (.cta c)) = some [.inl (Segment.ofStmts (.cta c) k.body)] := by
  simp [projectPlain, h, slice_noSync]

private theorem inr_not_mem_stmts (body : List Stmt) (e : Emission) :
    Sum.inr e ∉ body.map Sum.inl := by
  simp

/-- The S3.4 semantic corollary keeps the signed #46 dependency. -/
theorem projectPlain_step (c : Cta) (k : Kernel) (h : noAtomicStmts k.body = Bool.true)
    (σ σ' : DistState) (next : Next (List (Stmt ⊕ Emission))) :
    ((projectPlain k).map fun flat => (AgentProgram.ofBody (.cta c)).Step flat σ σ' next) =
      some ((exec k (σ.block c.rank c.pid)).map (σ.setBlock c.rank c.pid) = some σ' ∧
        next = .finish) := by
  have proj : projectPlain k = some (k.body.map Sum.inl) := by simp [projectPlain, h]
  rw [proj]
  change some ((AgentProgram.ofBody (.cta c)).Step (k.body.map Sum.inl) σ σ' next) = some _
  congr 1
  apply propext
  exact exec_noSync_eq_exec c k _ (by simp) (inr_not_mem_stmts k.body) σ σ' next

#print axioms flat_steps
#print axioms projectPlain_noSync
#print axioms inr_not_mem_stmts
#print axioms projectPlain_step

end VeriTile.Dist.Frontend.TritonDist
