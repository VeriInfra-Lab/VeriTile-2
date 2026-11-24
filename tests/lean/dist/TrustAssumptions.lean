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

theorem usingA2 (h : Assumption.notify_atomic_release) :
    Assumption.notify_atomic_release := h

/--
info: Trust assumptions used by usingA2:
  notify_atomic_release (semantic source)
-/
#guard_msgs in
#print_trust_assumptions usingA2

theorem usingA2AndA9
    (hNotify : Assumption.notify_atomic_release)
    (hGrid : Assumption.grid_barrier_cooperative_sync)
    (hAgain : Assumption.notify_atomic_release) :
    Assumption.notify_atomic_release ∧
      Assumption.grid_barrier_cooperative_sync ∧
      Assumption.notify_atomic_release :=
  ⟨hNotify, hGrid, hAgain⟩

/--
info: Trust assumptions used by usingA2AndA9:
  grid_barrier_cooperative_sync (semantic source)
  notify_atomic_release (semantic source)
-/
#guard_msgs in
#print_trust_assumptions usingA2AndA9

theorem quantified (_h : ∀ _ : Nat, Assumption.notify_atomic_release) : True := True.intro

/--
info: Trust assumptions used by quantified:
  notify_atomic_release (semantic source)
-/
#guard_msgs in
#print_trust_assumptions quantified

theorem bundled (_h : Assumption.notify_atomic_release ∧ Assumption.grid_barrier_cooperative_sync) :
    True := True.intro

/--
info: Trust assumptions used by bundled:
  grid_barrier_cooperative_sync (semantic source)
  notify_atomic_release (semantic source)
-/
#guard_msgs in
#print_trust_assumptions bundled

def NotifyBundle : Prop := Assumption.notify_atomic_release

theorem definedBundle (_h : NotifyBundle) : True := True.intro

/--
info: Trust assumptions used by definedBundle:
  notify_atomic_release (semantic source)
-/
#guard_msgs in
#print_trust_assumptions definedBundle

class HasNotify : Prop where
  premise : Assumption.notify_atomic_release

theorem classPremise [_h : HasNotify] : True := True.intro

/--
info: Trust assumptions used by classPremise:
  notify_atomic_release (semantic source)
-/
#guard_msgs in
#print_trust_assumptions classPremise

theorem implyNotify (_h : Assumption.notify_atomic_release → True) : True := True.intro

theorem throughLemma : True := implyNotify (fun _ => True.intro)

/--
info: Trust assumptions used by throughLemma:
  notify_atomic_release (semantic source)
-/
#guard_msgs in
#print_trust_assumptions throughLemma

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

theorem unregisteredQuantified
    (h : ∀ n : Nat, n = n → Assumption.unregisteredFixture) : True := h 0 rfl

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.unregisteredFixture' -/
#guard_msgs (error) in
#print_trust_assumptions unregisteredQuantified

def UnregisteredBundle : Prop := Assumption.unregisteredFixture ∧ True

theorem unregisteredWrapped (h : UnregisteredBundle) : True := h.2

/-- error: unregistered trust assumption 'VeriTile.Dist.Assumption.unregisteredFixture' -/
#guard_msgs (error) in
#print_trust_assumptions unregisteredWrapped

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
