import VeriTile.Dist.Meta.PrintTrustAssumptions

namespace VeriTile.Dist.Assumption

def unregisteredFixture : Prop := True

def translationFixture (programsAgree : Prop) : Prop := programsAgree

def translationMetadata (programsAgree : Prop) : TrustAssumption where
  name := `translationFixture
  statement := translationFixture programsAgree
  sourceOrRationale := "Regression fixture"
  affectedKernels := []
  assumptionClass := .translationCorrectness

attribute [trust_assumption translationMetadata] translationFixture

end VeriTile.Dist.Assumption

namespace VeriTile.Tests.TrustAssumptions

open VeriTile.Dist

theorem usingA2 (claim : Prop) (h : Assumption.notify_atomic_release claim) :
    Assumption.notify_atomic_release claim := h

/--
info: Trust assumptions used by usingA2:
  notify_atomic_release (semantic source)
-/
#guard_msgs in
#print_trust_assumptions usingA2

theorem usingA2AndA9 (notifyContract gridContract : Prop)
    (hNotify : Assumption.notify_atomic_release notifyContract)
    (hGrid : Assumption.grid_barrier_cooperative_sync gridContract)
    (hAgain : Assumption.notify_atomic_release notifyContract) :
    Assumption.notify_atomic_release notifyContract ∧
      Assumption.grid_barrier_cooperative_sync gridContract ∧
      Assumption.notify_atomic_release notifyContract :=
  ⟨hNotify, hGrid, hAgain⟩

/--
info: Trust assumptions used by usingA2AndA9:
  grid_barrier_cooperative_sync (semantic source)
  notify_atomic_release (semantic source)
-/
#guard_msgs in
#print_trust_assumptions usingA2AndA9

theorem usingNone : True := True.intro

/--
info: Trust assumptions used by usingNone:
  none
-/
#guard_msgs in
#print_trust_assumptions usingNone

theorem usingTranslation (claim : Prop) (h : Assumption.translationFixture claim) : claim := h

/--
info: Trust assumptions used by usingTranslation:
  translationFixture (translation correctness)
-/
#guard_msgs in
#print_trust_assumptions usingTranslation

theorem usingUnregistered (h : Assumption.unregisteredFixture) : True := h

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.unregisteredFixture' -/
#guard_msgs (error) in
#print_trust_assumptions usingUnregistered

/-- error: trust assumption 'notify_atomic_release' is already registered -/
#guard_msgs (error) in
attribute [trust_assumption TrustAssumptions.A2] Assumption.notify_atomic_release

def naturalFixture : Nat := 0

/-- error: trust assumption 'VeriTile.Tests.TrustAssumptions.naturalFixture' must be Prop-valued -/
#guard_msgs (error) in
attribute [trust_assumption TrustAssumptions.A2] naturalFixture

def falseFixture : Prop := False

def mismatchedMetadata : TrustAssumption where
  name := `falseFixture
  statement := True
  sourceOrRationale := "Regression fixture"
  affectedKernels := []
  assumptionClass := .semanticSource

/--
error: trust metadata 'VeriTile.Tests.TrustAssumptions.mismatchedMetadata' does not state 'VeriTile.Tests.TrustAssumptions.falseFixture'
-/
#guard_msgs (error) in
attribute [trust_assumption mismatchedMetadata] falseFixture

#axiomsClean usingA2AndA9
#axiomsClean usingTranslation

end VeriTile.Tests.TrustAssumptions
