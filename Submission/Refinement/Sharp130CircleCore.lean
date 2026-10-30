module

public import Submission.Refinement.Sharp130Tangent

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace CatalanMeasure.Refinement.Trimmed130.Sharp

open Polynomial Finset

theorem circleDistance_norm (z : ℂ) (hz : ‖z‖ = (radius : ℝ)) :
    circleDistance z.re = ‖(1 : ℂ)-z‖^2 := by
  have h := sq_norm_sub_real z 1
  rw [hz, norm_sub_rev] at h
  simp only [Complex.ofReal_one, mul_one, one_pow] at h
  dsimp [circleDistance]
  nlinarith

theorem re_bounds (z : ℂ) (hz : ‖z‖ = (radius : ℝ)) :
    -(radius : ℝ) ≤ z.re ∧ z.re ≤ (radius : ℝ) := by
  exact abs_le.mp (by simpa [hz] using Complex.abs_re_le_norm z)

theorem weighted_norm_le_base (hbase : ∀ z : ℂ, ‖z‖ = (radius : ℝ) →
      ‖(realP.map (algebraMap ℝ ℂ)).eval z‖^2 ≤ base z.re)
    (z : ℂ) (hz : ‖z‖ = (radius : ℝ)) :
    ‖(realP.map (algebraMap ℝ ℂ)).eval z‖^106 * circleDistance z.re^780 ≤ weightedBase z.re := by
  have h := pow_le_pow_left₀ (sq_nonneg _) (hbase z hz) 53
  have hp : (‖(realP.map (algebraMap ℝ ℂ)).eval z‖^2)^53 =
      ‖(realP.map (algebraMap ℝ ℂ)).eval z‖^106 := by rw [← pow_mul]
  rw [hp] at h
  exact mul_le_mul_of_nonneg_right h
    (pow_nonneg (circleDistance_positive (re_bounds z hz).2).le _)

theorem circleDistance_power_le (z : ℂ) (hz : ‖z‖ = (radius : ℝ)) :
    circleDistance z.re^780 ≤ ((radius : ℝ)+1)^1560 := by
  have hnorm : ‖(1 : ℂ)-z‖ ≤ (radius : ℝ)+1 := by
    simpa [hz, add_comm] using norm_sub_le (1 : ℂ) z
  rw [circleDistance_norm z hz, ← pow_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 1560

theorem squared_circle_bound (hbase : ∀ z : ℂ, ‖z‖ = (radius : ℝ) →
      ‖(realP.map (algebraMap ℝ ℂ)).eval z‖^2 ≤ base z.re)
    (hminimum : ∀ z : ℂ, ‖z‖ = (radius : ℝ) → |z.re| ≤ (halfWidth : ℝ) →
      (minimumNorm : ℝ) ≤ ‖(realP.map (algebraMap ℝ ℂ)).eval z‖)
    (z : ℂ) (hz : ‖z‖ = (radius : ℝ)) :
    (2*‖(realP.map (algebraMap ℝ ℂ)).eval z‖+1)^106 * circleDistance z.re^780 ≤
      Real.exp (260*(sharpWeightCap : ℝ)) := by
  have hx := re_bounds z hz
  have hD := (circleDistance_positive hx.2).le
  have hp := norm_nonneg ((realP.map (algebraMap ℝ ℂ)).eval z)
  by_cases hl : z.re ≤ -(halfWidth : ℝ)
  · apply outer_weighted_estimate _ _
      ((leftCap : ℝ)^53 * circleDistance (-(halfWidth : ℝ))^780)
      (((radius : ℝ)+1)^1560) _ hp hD
      ((weighted_norm_le_base hbase z hz).trans (left_tangent hx.1 hl))
      (circleDistance_power_le z hz)
    simpa only [leftBound, Rat.cast_mul, Rat.cast_pow, Rat.cast_add,
      Rat.cast_ofNat, Rat.cast_one, circleDistance_cast, Rat.cast_neg] using left_exp
  by_cases hr : (halfWidth : ℝ) ≤ z.re
  · apply outer_weighted_estimate _ _
      ((rightCap : ℝ)^53 * circleDistance (halfWidth : ℝ)^780)
      (((radius : ℝ)+1)^1560) _ hp hD
      ((weighted_norm_le_base hbase z hz).trans (right_tangent hr hx.2))
      (circleDistance_power_le z hz)
    simpa only [rightBound, Rat.cast_mul, Rat.cast_pow, Rat.cast_add,
      Rat.cast_ofNat, Rat.cast_one, circleDistance_cast] using right_exp
  · have habs : |z.re| ≤ (halfWidth : ℝ) :=
      abs_le.mpr ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hr).le⟩
    apply central_weighted_estimate _ _ (minimumNorm : ℝ)
      ((centreCap : ℝ)^53 * circleDistance (centre : ℝ)^780)
      (epsilon : ℝ) _ hp hD (by norm_num [minimumNorm]) (hminimum z hz habs)
      ((weighted_norm_le_base hbase z hz).trans (central_tangent hx.1 hx.2))
    simpa only [centreBound, Rat.cast_mul, Rat.cast_pow, Rat.cast_add,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, circleDistance_cast, mul_assoc] using centre_exp

/-- The fixed-degree circle certificate at the sharp weight cap 52.18435. -/
theorem circle_bound_of_norms (hbase : ∀ z : ℂ, ‖z‖ = (radius : ℝ) →
      ‖(realP.map (algebraMap ℝ ℂ)).eval z‖^2 ≤ base z.re)
    (hminimum : ∀ z : ℂ, ‖z‖ = (radius : ℝ) → |z.re| ≤ (halfWidth : ℝ) →
      (minimumNorm : ℝ) ≤ ‖(realP.map (algebraMap ℝ ℂ)).eval z‖)
    (z : ℂ) (hz : ‖z‖ = (radius : ℝ)) :
    (2*‖(realP.map (algebraMap ℝ ℂ)).eval z‖+1)^53 * ‖(1 : ℂ)-z‖^780 ≤
      Real.exp (130*(sharpWeightCap : ℝ)) := by
  have hs := squared_circle_bound hbase hminimum z hz
  rw [circleDistance_norm z hz] at hs
  have he : (Real.exp (130*(sharpWeightCap : ℝ)))^2 = Real.exp (260*(sharpWeightCap : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hh : ((2*‖(realP.map (algebraMap ℝ ℂ)).eval z‖+1)^53 * ‖(1 : ℂ)-z‖^780)^2 ≤
      (Real.exp (130*(sharpWeightCap : ℝ)))^2 := by
    rw [he, mul_pow, ← pow_mul, ← pow_mul]
    simpa only [← pow_mul] using hs
  exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (Real.exp_pos _).le hh

end CatalanMeasure.Refinement.Trimmed130.Sharp
