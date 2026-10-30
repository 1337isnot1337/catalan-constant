module

public import Submission.Refinement.Trimmed130Data
public import Submission.Refinement.PreciseLogTwo

@[expose] public section

/-! A circle certificate using rational coefficient norms and a Taylor lower
bound for the exponential. All finite comparisons use kernel reduction. -/

namespace CatalanMeasure.Refinement.Trimmed130

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem rationalQ_eq : rationalQ = rationalP * (1 - X) ^ 14 := by decide

theorem radius_nonneg : (0 : ℚ) ≤ radius := by decide
theorem normCap_nonneg : (0 : ℚ) ≤ normCap := by decide
theorem coefficient_norm_le : hornerNormBound filteredCoefficients radius ≤ normCap := by decide
theorem filterCap_le : (radius + 1) ^ 14 ≤ filterCap := by decide

def taylorArgument : ℚ := 12303972077711049 / 100000000000000000

theorem taylorArgument_nonneg : (0 : ℚ) ≤ taylorArgument := by decide

theorem finite_exp_comparison :
    (2 * normCap + filterCap) ^ 53 * (radius + 1) ^ 38 ≤
      (2 : ℚ) ^ 9821 * expTaylorRat taylorArgument 16 := by decide

theorem filtered_norm_le (z : ℂ) (hz : ‖z‖ = (radius : ℝ)) :
    ‖((realP.map (algebraMap ℝ ℂ)) * (1 - X) ^ 14).eval z‖ ≤ (normCap : ℝ) := by
  have h := norm_eval_polynomialFromCoeffs_le filteredCoefficients radius_nonneg z hz.le
  have hc : (hornerNormBound filteredCoefficients radius : ℝ) ≤ normCap := by
    exact_mod_cast coefficient_norm_le
  have he : ((realP.map (algebraMap ℝ ℂ)) * (1 - X) ^ 14) =
      rationalQ.map (algebraMap ℚ ℂ) := by
    rw [rationalQ_eq]
    simp [realP, Polynomial.map_map]
  rw [he]
  exact h.trans hc

theorem finite_real_exp_comparison :
    (2 * (normCap : ℝ) + ((radius : ℝ) + 1) ^ 14) ^ 53 *
      ((radius : ℝ) + 1) ^ 38 ≤ Real.exp (130 * (circleCap : ℝ)) := by
  have hlog := CatalanMeasure.GenD.Refinement.log_two_bounds.2
  have hdecomp : (9821 : ℝ) * Real.log 2 + (taylorArgument : ℝ) ≤
      ((130 * circleCap : ℚ) : ℝ) := by
    norm_num [CatalanMeasure.GenD.Refinement.logTwoHi] at hlog
    norm_num [taylorArgument, circleCap]
    linarith
  have he := rational_le_exp_of_binary_taylor
    ((2 * normCap + filterCap) ^ 53 * (radius + 1) ^ 38)
    (130 * circleCap) taylorArgument 9821 16
    taylorArgument_nonneg hdecomp finite_exp_comparison
  have hf : ((radius : ℝ) + 1) ^ 14 ≤ (filterCap : ℝ) := by
    exact_mod_cast filterCap_le
  have hr : (0 : ℝ) ≤ radius := by exact_mod_cast radius_nonneg
  have hM : (0 : ℝ) ≤ normCap := by exact_mod_cast normCap_nonneg
  push_cast at he
  refine le_trans ?_ he
  gcongr

theorem circle_bound (z : ℂ) (hz : ‖z‖ = (radius : ℝ)) :
    (2 * ‖(realP.map (algebraMap ℝ ℂ)).eval z‖ + 1) ^ 53 *
      ‖(1 : ℂ) - z‖ ^ (6 * 130) ≤ Real.exp (130 * (circleCap : ℝ)) := by
  exact weighted_circle_of_filtered_norm
    (realP.map (algebraMap ℝ ℂ)) 53 6 130 14 38
    (radius : ℝ) (normCap : ℝ) (circleCap : ℝ)
    (by exact_mod_cast radius_nonneg) (by exact_mod_cast normCap_nonneg)
    (by norm_num) filtered_norm_le finite_real_exp_comparison z hz

end CatalanMeasure.Refinement.Trimmed130

#print axioms CatalanMeasure.Refinement.Trimmed130.circle_bound
