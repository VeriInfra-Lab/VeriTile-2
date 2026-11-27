import VeriTile.Dist.Meta.PrintTrustAssumptions

namespace VeriTile.Tests.TrustAssumptionCollision

open VeriTile.Dist

def translationFixture : Prop := True

def metadata : TrustAssumption where
  name := `translationFixture
  statement := translationFixture
  sourceOrRationale := "Independent registration regression"
  affectedKernels := []
  assumptionClass := .translationCorrectness

attribute [trust_assumption metadata] translationFixture

end VeriTile.Tests.TrustAssumptionCollision
