import VeriTile.Staging.Dist.SegmentSpec
import VeriTile.Dist.Frontend.TritonDist.LanguageExtra

/-! S3.3 clients of the signed flat-body slice. The ordinary frontend and the
distributed call frontend provide their respective inputs. Joining arbitrary
mixed source blocks and preserving atomic groups is the frontend task #82. -/
namespace VeriTile.Tests.SegmentSlicing
open VeriTile.Triton VeriTile.Dist
open VeriTile.Dist.Frontend.TritonDist
open scoped VeriTile.Dist.Frontend.TritonDist

private def plain : ComputeKernel := triton { x = tl.program_id(0) }
private def body : List Stmt := [.assign .nat [] "x" (.programId 0)]

theorem projectedBody : plain.toAlgorithm? = .ok ⟨[],[],body⟩ := rfl

theorem noSyncKernel (a : Agent) :
    plain.toAlgorithm?.map (fun k => slice a (k.body.map Sum.inl)) =
      .ok [.inl (Segment.ofStmts a body)] := by
  rw [projectedBody]
  exact congrArg Except.ok (slice_noSync a body)

private def fenceSource : LanguageExtra.Source := triton { membar(scope="cta") membar(scope="sys") }

/-- Each of the two actual source sites lowers to a singleton fence with no payload. -/
private def cuts (ctx : LanguageExtra.Context Nat) : Option (List Emission) :=
  fenceSource.sites.mapM fun site => do
    let .step [event] ← site.call.lower ctx | none
    return ⟨ctx.agent,event,.noValue⟩

private def pairedBody (events : List Emission) : List (Stmt ⊕ Emission) :=
  body.map Sum.inl ++ events.map Sum.inr

theorem adjacentCuts (ctx : LanguageExtra.Context Nat) :
    (cuts ctx).map (fun es => slice ctx.agent (pairedBody es)) = some
      [.inl (Segment.ofStmts ctx.agent body), .inr (.fence .plain),
       .inl (Segment.ofStmts ctx.agent []), .inr (.fence .plain),
       .inl (Segment.ofStmts ctx.agent [])] := rfl

theorem cannotSkipCut (ctx : LanguageExtra.Context Nat) (es : List Emission) (atCuts : cuts ctx = some es) :
    ¬ (AgentProgram.ofBody ctx.agent).Steps (pairedBody es)
        [.inl (Segment.ofStmts ctx.agent body),.inr (.fence .plain),.inl (Segment.ofStmts ctx.agent [])] := by
  intro path
  have eq := (AgentProgram.ofBody_steps _ _ _).mp path
  have counts := congrArg (Option.map List.length) (adjacentCuts ctx)
  rw [atCuts] at counts
  simp only [Option.map_some] at counts
  rw [← eq] at counts
  exact (by decide : some 3 ≠ some 5) counts

#print axioms AgentProgram.Step.deterministic
#print axioms AgentProgram.ofBody_steps
#print axioms noSyncKernel
#print axioms adjacentCuts
#print axioms cannotSkipCut
end VeriTile.Tests.SegmentSlicing
