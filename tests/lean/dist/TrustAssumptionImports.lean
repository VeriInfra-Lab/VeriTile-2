import tests.lean.dist.TrustAssumptions

namespace VeriTile.Dist.Assumption

theorem proofWithUnregisteredType : unregisteredFixture := True.intro

opaque rewriteFixture._proof_3 : Prop
opaque rewriteFixture.eq_def.match_4 : Prop
opaque rewriteFixture._sparseCasesOn_2 : Prop
opaque rewriteFixture._unary : Prop
inductive rewriteFixture.match_8 : Prop
def rewriteFixture.match_7 : Prop := unregisteredFixture

end VeriTile.Dist.Assumption

namespace VeriTile.Tests.TrustAssumptionImports

open VeriTile.Dist

theorem usingImportedRewrite (h : Assumption.rewriteFixture 0) : True :=
  TrustAssumptions.usingRewrite h

/--
info: Trust assumptions used by usingImportedRewrite:
  rewriteFixture (translation correctness)
-/
#guard_msgs in
#print_trust_assumptions usingImportedRewrite

theorem usingImportedSplit (n : Nat) (h : Assumption.rewriteFixture n) : n = 0 :=
  TrustAssumptions.usingSplit n h

/--
info: Trust assumptions used by usingImportedSplit:
  rewriteFixture (translation correctness)
-/
#guard_msgs in
#print_trust_assumptions usingImportedSplit

theorem usingImportedProof (_h : Assumption.proofFixture) : True := True.intro

/--
info: Trust assumptions used by usingImportedProof:
  proofFixture (translation correctness)
-/
#guard_msgs in
#print_trust_assumptions usingImportedProof

theorem usingImportedBadProof (_h : Assumption.badProofFixture) : True := True.intro

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.unregisteredProof' -/
#guard_msgs (error) in
#print_trust_assumptions usingImportedBadProof

theorem usingImportedFakeMatcher (h : Assumption.notify_atomic_release.match_9) : True :=
  TrustAssumptions.usingFakeMatcher h

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.notify_atomic_release.match_9' -/
#guard_msgs (error) in
#print_trust_assumptions usingImportedFakeMatcher

theorem usingImportedFakeMatcherDefinition (h : Assumption.translationFixture.match_9) : True :=
  TrustAssumptions.usingFakeMatcherDefinition h

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.translationFixture.match_9' -/
#guard_msgs (error) in
#print_trust_assumptions usingImportedFakeMatcherDefinition

theorem usingImportedForwardOpaque (h : Assumption.forwardOpaque.eq_2) : True :=
  TrustAssumptions.usingForwardOpaque h

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.forwardOpaque.eq_2' -/
#guard_msgs (error) in
#print_trust_assumptions usingImportedForwardOpaque

theorem usingImportedForwardInductive (h : Assumption.forwardInductive.eq_2) : True :=
  TrustAssumptions.usingForwardInductive h

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.forwardInductive.eq_2' -/
#guard_msgs (error) in
#print_trust_assumptions usingImportedForwardInductive

theorem usingImportedForwardCongruence (h : Assumption.forwardCongruence.congr_simp) : True :=
  TrustAssumptions.usingForwardCongruence h

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.forwardCongruence.congr_simp' -/
#guard_msgs (error) in
#print_trust_assumptions usingImportedForwardCongruence

theorem usingImportedForwardData (h : Assumption.forwardData.eq_2 = 0) : True :=
  TrustAssumptions.usingForwardData h

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.forwardData.eq_2' -/
#guard_msgs (error) in
#print_trust_assumptions usingImportedForwardData

theorem usingProofWithUnregisteredType : True := Assumption.proofWithUnregisteredType

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.unregisteredFixture' -/
#guard_msgs (error) in
#print_trust_assumptions usingProofWithUnregisteredType

theorem usingFakeProof (_h : Assumption.rewriteFixture._proof_3) : True := True.intro

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.rewriteFixture._proof_3' -/
#guard_msgs (error) in
#print_trust_assumptions usingFakeProof

theorem usingFakeEquationMatcher (_h : Assumption.rewriteFixture.eq_def.match_4) : True := True.intro

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.rewriteFixture.eq_def.match_4' -/
#guard_msgs (error) in
#print_trust_assumptions usingFakeEquationMatcher

theorem usingFakeSparseCases (_h : Assumption.rewriteFixture._sparseCasesOn_2) : True := True.intro

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.rewriteFixture._sparseCasesOn_2' -/
#guard_msgs (error) in
#print_trust_assumptions usingFakeSparseCases

theorem usingFakeUnary (_h : Assumption.rewriteFixture._unary) : True := True.intro

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.rewriteFixture._unary' -/
#guard_msgs (error) in
#print_trust_assumptions usingFakeUnary

theorem usingFakeInductive (_h : Assumption.rewriteFixture.match_8) : True := True.intro

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.rewriteFixture.match_8' -/
#guard_msgs (error) in
#print_trust_assumptions usingFakeInductive

theorem usingFakeDefinition (_h : Assumption.rewriteFixture.match_7) : True := True.intro

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.rewriteFixture.match_7' -/
#guard_msgs (error) in
#print_trust_assumptions usingFakeDefinition

end VeriTile.Tests.TrustAssumptionImports
