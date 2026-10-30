module

public import Submission.Refinement.Sharp130CircleCore
public import Submission.Refinement.Trimmed130ZeroRoots

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace CatalanMeasure.Refinement.Trimmed130.Sharp

open Polynomial Finset

def indexedFactor (i : Fin 130) : ℚ × ℚ :=
  (radius ^ 2 + zeroLeft i ^ 2 + 2 * (zeroRight i - zeroLeft i) * (radius+1), -2 * zeroLeft i)

theorem distanceFactors_ofFn : distanceFactors = List.ofFn indexedFactor := by decide +kernel

theorem base_eq_prod (x : ℝ) :
    base x = (leadingCoefficient : ℝ)^2 * ∏ i : Fin 130,
      ((radius : ℝ)^2 + (zeroLeft i : ℝ)^2 +
        2*((zeroRight i : ℝ)-(zeroLeft i : ℝ))*((radius : ℝ)+1) - 2*(zeroLeft i : ℝ)*x) := by
  rw [base, distanceFactors_ofFn, affineProduct_ofFn]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  dsimp [indexedFactor]
  push_cast
  ring

theorem norm_sq_le_base (z : ℂ) (hz : ‖z‖ = (radius : ℝ)) :
    ‖(realP.map (algebraMap ℝ ℂ)).eval z‖^2 ≤ base z.re := by
  rw [base_eq_prod, polynomial_norm_sq_factorization realP (leadingCoefficient : ℝ)
    zeroRoots realP_factorization z]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.prod_le_prod₀ (fun i _ => sq_nonneg _)
  intro i _
  have ha : (-1 : ℝ) ≤ (zeroLeft i : ℝ) := by exact_mod_cast (zero_geometry i).1
  have hb : (zeroRight i : ℝ) ≤ (1 : ℝ) := by exact_mod_cast (zero_geometry i).2
  exact sq_norm_sub_real_upper z (radius : ℝ) (zeroLeft i : ℝ) (zeroRight i : ℝ)
    (zeroRoots i) hz ha ((zeroRoots_location i).2.trans hb)
    (zeroRoots_location i).1 (zeroRoots_location i).2

theorem central_norm_minimum (z : ℂ) (hz : ‖z‖ = (radius : ℝ))
    (hx : |z.re| ≤ (halfWidth : ℝ)) :
    (minimumNorm : ℝ) ≤ ‖(realP.map (algebraMap ℝ ℂ)).eval z‖ := by
  have h := polynomial_norm_sq_lower realP (leadingCoefficient : ℝ) zeroRoots
    realP_factorization z (radius : ℝ) (halfWidth : ℝ) hz halfWidth_positive.le hx
    (by norm_num [radius, halfWidth])
  have hsq := minimum_norm.trans h
  have hM : 0 ≤ (minimumNorm : ℝ) := by norm_num [minimumNorm]
  nlinarith [norm_nonneg ((realP.map (algebraMap ℝ ℂ)).eval z)]

/-- The fixed-degree circle certificate at the sharp weight cap 52.18435. -/
theorem circle_bound (z : ℂ) (hz : ‖z‖ = (radius : ℝ)) :
    (2*‖(realP.map (algebraMap ℝ ℂ)).eval z‖+1)^53 * ‖(1 : ℂ)-z‖^780 ≤
      Real.exp (130*(sharpWeightCap : ℝ)) :=
  circle_bound_of_norms norm_sq_le_base central_norm_minimum z hz

end CatalanMeasure.Refinement.Trimmed130.Sharp

#print axioms CatalanMeasure.Refinement.Trimmed130.Sharp.circle_bound
