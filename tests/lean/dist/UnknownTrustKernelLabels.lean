import VeriTile.Dist.Meta.PrintTrustAssumptions

namespace UnknownTrustKernelLabels
open VeriTile.Dist

def fixture (p : Prop) : Prop := p

def metadata (p : Prop) : TrustAssumption where
  name := `fixture
  statement := fixture p
  sourceOrRationale := "Kernel label checker regression"
  affectedKernels := ["D4 reduce_topk_allreduce_kernel", "D5 " ++ "reduce_topk_reduce_ar_intra_node_kernel"]
  assumptionClass := .translationCorrectness

attribute [trust_assumption metadata] fixture

end UnknownTrustKernelLabels
