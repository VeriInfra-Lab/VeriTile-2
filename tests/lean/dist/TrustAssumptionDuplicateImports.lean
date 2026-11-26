import tests.lean.dist.TrustAssumptions
import tests.lean.dist.TrustAssumptionCollision

/-- error: trust assumption 'translationFixture' is already registered -/
#guard_msgs (error) in
#print_trust_assumptions VeriTile.Tests.TrustAssumptions.usingNone
