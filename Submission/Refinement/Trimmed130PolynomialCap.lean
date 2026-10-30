module

public import Submission.Refinement.Trimmed130Degree

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

open Polynomial

noncomputable def polynomialCap : ℝ := 2 * (hornerNormBound powerCoefficients radius : ℝ) + 1

theorem realP_complex_map :
    realP.map (algebraMap ℝ ℂ) = rationalP.map (algebraMap ℚ ℂ) := by
  rw [realP, Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ ℝ ℂ]

theorem polynomialCap_bound (z : ℂ) (hz : ‖z‖ = (radius : ℝ)) :
    2 * ‖(realP.map (algebraMap ℝ ℂ)).eval z‖ + 1 ≤ polynomialCap := by
  have hn := norm_eval_polynomialFromCoeffs_le powerCoefficients
    (by norm_num [radius] : (0 : ℚ) ≤ radius) z hz.le
  rw [realP_complex_map]
  change 2 * ‖((polynomialFromCoeffs powerCoefficients).map (algebraMap ℚ ℂ)).eval z‖ + 1 ≤
    2 * (hornerNormBound powerCoefficients radius : ℝ) + 1
  linarith only [hn]

end CatalanMeasure.Refinement.Trimmed130
