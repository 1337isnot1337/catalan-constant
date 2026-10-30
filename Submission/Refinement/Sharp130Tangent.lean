module

public import Submission.Refinement.RootCircle
public import Submission.Refinement.Sharp130Finite

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130.Sharp

theorem radius_positive : 0 < (radius : ℝ) := by norm_num [radius]
theorem centre_mem : -(radius : ℝ) ≤ (centre : ℝ) ∧ (centre : ℝ) ≤ (radius : ℝ) := by
  norm_num [radius, centre]
theorem halfWidth_mem : (halfWidth : ℝ) ≤ (radius : ℝ) := by norm_num [halfWidth, radius]
theorem halfWidth_positive : 0 < (halfWidth : ℝ) := by norm_num [halfWidth]

theorem circleDistance_positive {x : ℝ} (hx : x ≤ (radius : ℝ)) :
    0 < circleDistance x := by
  norm_num [circleDistance, radius] at hx ⊢
  linarith

theorem base_nonnegative {x : ℝ} (hlo : -(radius : ℝ) ≤ x) (hhi : x ≤ (radius : ℝ)) :
    0 ≤ base x := by
  exact mul_nonneg (sq_nonneg _) (affineProduct_nonneg _ _
    (fun f hf => (factor_positive f hf hlo hhi).le))

theorem weightedBase_nonnegative {x : ℝ} (hlo : -(radius : ℝ) ≤ x)
    (hhi : x ≤ (radius : ℝ)) : 0 ≤ weightedBase x := by
  exact mul_nonneg (pow_nonneg (base_nonnegative hlo hhi) _)
    (pow_nonneg (circleDistance_positive hhi).le _)

theorem weightedBase_tangent {c x : ℝ}
    (hclo : -(radius : ℝ) ≤ c) (hchi : c ≤ (radius : ℝ))
    (hxlo : -(radius : ℝ) ≤ x) (hxhi : x ≤ (radius : ℝ)) :
    weightedBase x ≤ weightedBase c * Real.exp (slope c * (x-c)) := by
  have hdc : (radius : ℝ) ^ 2 + 1 + (-2)*c = circleDistance c := by
    dsimp [circleDistance]; ring
  have hdx : (radius : ℝ) ^ 2 + 1 + (-2)*x = circleDistance x := by
    dsimp [circleDistance]; ring
  have h := weighted_affine_tangent distanceFactors (leadingCoefficient : ℝ)
    ((radius : ℝ)^2+1) (-2) c x 53 780
    (fun f hf => factor_positive f hf hclo hchi)
    (fun f hf => (factor_positive f hf hxlo hxhi).le)
    (by rw [hdc]; exact circleDistance_positive hchi)
    (by rw [hdx]; exact (circleDistance_positive hxhi).le)
  rw [hdc, hdx] at h
  have hs : (53 : ℝ) * affineSlope distanceFactors c + 780 * (-2 / circleDistance c) =
      slope c := by dsimp [slope]; ring
  norm_num only [Nat.cast_ofNat] at h
  rw [hs] at h
  exact h

theorem central_tangent {x : ℝ} (hxlo : -(radius : ℝ) ≤ x) (hxhi : x ≤ (radius : ℝ)) :
    weightedBase x ≤
      ((centreCap : ℝ)^53 * circleDistance (centre : ℝ)^780) * Real.exp (epsilon : ℝ) := by
  have hxc : |x-(centre : ℝ)| ≤ 2*(radius : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [centre_mem.1, centre_mem.2]
  have hs : slope (centre : ℝ) * (x-(centre : ℝ)) ≤ (epsilon : ℝ) := by
    calc
      _ ≤ |slope (centre : ℝ) * (x-(centre : ℝ))| := le_abs_self _
      _ = |slope (centre : ℝ)| * |x-(centre : ℝ)| := abs_mul _ _
      _ ≤ |slope (centre : ℝ)| * (2*(radius : ℝ)) :=
        mul_le_mul_of_nonneg_left hxc (abs_nonneg _)
      _ ≤ (epsilon : ℝ) := by simpa only [mul_assoc] using centre_slope
  have hb : weightedBase (centre : ℝ) ≤
      (centreCap : ℝ)^53 * circleDistance (centre : ℝ)^780 := by
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (base_nonnegative centre_mem.1 centre_mem.2) centre_base 53)
      (pow_nonneg (circleDistance_positive centre_mem.2).le _)
  exact (weightedBase_tangent centre_mem.1 centre_mem.2 hxlo hxhi).trans
    (mul_le_mul hb (Real.exp_le_exp.mpr hs) (Real.exp_pos _).le
      ((weightedBase_nonnegative centre_mem.1 centre_mem.2).trans hb))

theorem left_tangent {x : ℝ} (hxlo : -(radius : ℝ) ≤ x) (hxhi : x ≤ -(halfWidth : ℝ)) :
    weightedBase x ≤ (leftCap : ℝ)^53 * circleDistance (-(halfWidth : ℝ))^780 := by
  have hclo : -(radius : ℝ) ≤ -(halfWidth : ℝ) := neg_le_neg halfWidth_mem
  have hchi : -(halfWidth : ℝ) ≤ (radius : ℝ) := by linarith [radius_positive, halfWidth_positive]
  have hxhi' : x ≤ (radius : ℝ) := hxhi.trans hchi
  have hs : slope (-(halfWidth : ℝ)) * (x-(-(halfWidth : ℝ))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos left_slope (sub_nonpos.mpr hxhi)
  have h := weightedBase_tangent hclo hchi hxlo hxhi'
  have hw : weightedBase x ≤ weightedBase (-(halfWidth : ℝ)) := by
    calc
      _ ≤ weightedBase (-(halfWidth : ℝ)) *
          Real.exp (slope (-(halfWidth : ℝ))*(x-(-(halfWidth : ℝ)))) := h
      _ ≤ weightedBase (-(halfWidth : ℝ)) * Real.exp 0 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) (weightedBase_nonnegative hclo hchi)
      _ = _ := by rw [Real.exp_zero, mul_one]
  exact hw.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (base_nonnegative hclo hchi) left_base 53)
    (pow_nonneg (circleDistance_positive hchi).le _))

theorem right_tangent {x : ℝ} (hxlo : (halfWidth : ℝ) ≤ x) (hxhi : x ≤ (radius : ℝ)) :
    weightedBase x ≤ (rightCap : ℝ)^53 * circleDistance (halfWidth : ℝ)^780 := by
  have hclo : -(radius : ℝ) ≤ (halfWidth : ℝ) := by linarith [radius_positive, halfWidth_positive]
  have hxlo' : -(radius : ℝ) ≤ x := hclo.trans hxlo
  have hs : slope (halfWidth : ℝ) * (x-(halfWidth : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg right_slope (sub_nonneg.mpr hxlo)
  have h := weightedBase_tangent hclo halfWidth_mem hxlo' hxhi
  have hw : weightedBase x ≤ weightedBase (halfWidth : ℝ) := by
    calc
      _ ≤ weightedBase (halfWidth : ℝ) *
          Real.exp (slope (halfWidth : ℝ)*(x-(halfWidth : ℝ))) := h
      _ ≤ weightedBase (halfWidth : ℝ) * Real.exp 0 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs)
          (weightedBase_nonnegative hclo halfWidth_mem)
      _ = _ := by rw [Real.exp_zero, mul_one]
  exact hw.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (base_nonnegative hclo halfWidth_mem) right_base 53)
    (pow_nonneg (circleDistance_positive halfWidth_mem).le _))

end CatalanMeasure.Refinement.Trimmed130.Sharp
