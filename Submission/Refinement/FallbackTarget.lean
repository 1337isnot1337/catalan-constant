module

public import Submission.Refinement.EndpointBridge
public import Submission.Refinement.Fallback5318833

@[expose] public section

/-! Named fallback target. The root Submission.lean selects the strongest compiled result. -/

namespace CatalanMeasure.Refinement

theorem fallback_bound : BigOSpeedrun.Catalan.Bound ((5318833 : ℚ) / 10000) := by
  apply bound_of_endpoint (by norm_num)
  simpa [BigOSpeedrun.Catalan.Endpoint, BigOSpeedrun.Catalan.constant] using
    CatalanMeasure.GenD.Refinement.catalan_irrationalityMeasure_5318833

end CatalanMeasure.Refinement

#print axioms CatalanMeasure.Refinement.fallback_bound
