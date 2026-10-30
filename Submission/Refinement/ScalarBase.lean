module

public import Submission.Refinement.PreciseLogTwo
public import Submission.Refinement.FinalReal
public import Submission.CatalanMeasure.GenD.D58.Budget590

@[expose] public section

/-!
# Numerical denominator exponent used by the scalar certificates

The final arithmetic assembly identifies this rational gain with the area of
the upstream Bank532 profile. The scalar budgets do not depend on that host
construction, so they can be checked independently of it.
-/

namespace CatalanMeasure.GenD.Refinement

noncomputable def exactProfileGain : ℝ :=
  36235515874601938601596598 / 1642609663271115992578125

noncomputable def denominatorExponent : ℝ :=
  24733 / 4 + (2673 / 8) * Real.log 2 - exactProfileGain

end CatalanMeasure.GenD.Refinement
