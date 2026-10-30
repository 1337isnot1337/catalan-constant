module

public import Submission.Refinement.Sharp130Data
public import Submission.Refinement.PreciseLogTwo

@[expose] public section

/-!
# Exact comparisons for the three-tangent circle certificate

The rational comparisons use kernel reduction. The real exponential bounds
follow from the proved enclosure for log 2 and a 16-term Taylor lower bound.
-/

namespace CatalanMeasure.Refinement.Trimmed130.Sharp

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem factor_endpoints_rat : ∀ f ∈ distanceFactors,
    0 < f.1 + f.2 * (-radius) ∧ 0 < f.1 + f.2 * radius := by decide +kernel

theorem centre_base_rat : baseRat centre ≤ centreCap := by decide +kernel
theorem left_base_rat : baseRat (-halfWidth) ≤ leftCap := by decide +kernel
theorem right_base_rat : baseRat halfWidth ≤ rightCap := by decide +kernel

theorem centre_slope_rat : |slopeRat centre| * 2 * radius ≤ epsilon := by decide +kernel
theorem left_slope_rat : 0 ≤ slopeRat (-halfWidth) := by decide +kernel
theorem right_slope_rat : slopeRat halfWidth ≤ 0 := by decide +kernel

theorem minimum_norm_rat :
    minimumNorm ^ 2 ≤ leadingCoefficient ^ 2 * (radius ^ 2 - halfWidth ^ 2) ^ 130 := by
  decide +kernel

theorem centre_finite_exp :
    centreBound ≤ (2 : ℚ) ^ binaryExponent * expTaylorRat centralTaylorArgument 16 := by
  decide +kernel

theorem left_finite_exp :
    leftBound ≤ (2 : ℚ) ^ binaryExponent * expTaylorRat outerTaylorArgument 16 := by
  decide +kernel

theorem right_finite_exp :
    rightBound ≤ (2 : ℚ) ^ binaryExponent * expTaylorRat outerTaylorArgument 16 := by
  decide +kernel

theorem factor_endpoints (f : ℚ × ℚ) (hf : f ∈ distanceFactors) :
    0 < (f.1 : ℝ) + (f.2 : ℝ) * (-(radius : ℝ)) ∧
      0 < (f.1 : ℝ) + (f.2 : ℝ) * (radius : ℝ) := by
  exact_mod_cast factor_endpoints_rat f hf

theorem factor_positive (f : ℚ × ℚ) (hf : f ∈ distanceFactors) {x : ℝ}
    (hxlo : -(radius : ℝ) ≤ x) (hxhi : x ≤ (radius : ℝ)) :
    0 < (f.1 : ℝ) + (f.2 : ℝ) * x := by
  obtain ⟨hl, hh⟩ := factor_endpoints f hf
  exact affine_positive_between _ _ _ _ _ hl hh hxlo hxhi

theorem centre_base : base (centre : ℝ) ≤ (centreCap : ℝ) := by
  rw [← base_cast]
  exact_mod_cast centre_base_rat

theorem left_base : base (-(halfWidth : ℝ)) ≤ (leftCap : ℝ) := by
  have h : (baseRat (-halfWidth) : ℝ) ≤ (leftCap : ℝ) := by
    exact_mod_cast left_base_rat
  simpa only [base_cast, Rat.cast_neg] using h

theorem right_base : base (halfWidth : ℝ) ≤ (rightCap : ℝ) := by
  rw [← base_cast]
  exact_mod_cast right_base_rat

theorem centre_slope : |slope (centre : ℝ)| * 2 * (radius : ℝ) ≤ (epsilon : ℝ) := by
  have h : |(slopeRat centre : ℝ)| * 2 * (radius : ℝ) ≤ (epsilon : ℝ) := by
    exact_mod_cast centre_slope_rat
  simpa only [slope_cast] using h

theorem left_slope : 0 ≤ slope (-(halfWidth : ℝ)) := by
  have h : (0 : ℝ) ≤ (slopeRat (-halfWidth) : ℝ) := by exact_mod_cast left_slope_rat
  simpa only [slope_cast, Rat.cast_neg] using h

theorem right_slope : slope (halfWidth : ℝ) ≤ 0 := by
  rw [← slope_cast]
  exact_mod_cast right_slope_rat

theorem minimum_norm :
    (minimumNorm : ℝ) ^ 2 ≤ (leadingCoefficient : ℝ) ^ 2 *
      ((radius : ℝ) ^ 2 - (halfWidth : ℝ) ^ 2) ^ 130 := by
  exact_mod_cast minimum_norm_rat

theorem central_decomposition :
    (binaryExponent : ℝ) * Real.log 2 + (centralTaylorArgument : ℝ) ≤
      ((260 * sharpWeightCap - epsilon : ℚ) : ℝ) := by
  have hlog := CatalanMeasure.GenD.Refinement.log_two_bounds.2
  norm_num [CatalanMeasure.GenD.Refinement.logTwoHi] at hlog
  norm_num [binaryExponent, centralTaylorArgument, sharpWeightCap, epsilon]
  linarith

theorem outer_decomposition :
    (binaryExponent : ℝ) * Real.log 2 + (outerTaylorArgument : ℝ) ≤
      ((260 * sharpWeightCap : ℚ) : ℝ) := by
  have hlog := CatalanMeasure.GenD.Refinement.log_two_bounds.2
  norm_num [CatalanMeasure.GenD.Refinement.logTwoHi] at hlog
  norm_num [binaryExponent, outerTaylorArgument, sharpWeightCap]
  linarith

theorem centre_exp :
    (centreBound : ℝ) ≤ Real.exp (260 * (sharpWeightCap : ℝ) - (epsilon : ℝ)) := by
  have h := rational_le_exp_of_binary_taylor centreBound
    (260 * sharpWeightCap - epsilon) centralTaylorArgument binaryExponent 16
    (by decide +kernel) central_decomposition centre_finite_exp
  simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat] using h

theorem left_exp :
    (leftBound : ℝ) ≤ Real.exp (260 * (sharpWeightCap : ℝ)) := by
  have h := rational_le_exp_of_binary_taylor leftBound
    (260 * sharpWeightCap) outerTaylorArgument binaryExponent 16
    (by decide +kernel) outer_decomposition left_finite_exp
  simpa only [Rat.cast_mul, Rat.cast_ofNat] using h

theorem right_exp :
    (rightBound : ℝ) ≤ Real.exp (260 * (sharpWeightCap : ℝ)) := by
  have h := rational_le_exp_of_binary_taylor rightBound
    (260 * sharpWeightCap) outerTaylorArgument binaryExponent 16
    (by decide +kernel) outer_decomposition right_finite_exp
  simpa only [Rat.cast_mul, Rat.cast_ofNat] using h

end CatalanMeasure.Refinement.Trimmed130.Sharp

#print axioms CatalanMeasure.Refinement.Trimmed130.Sharp.centre_exp
#print axioms CatalanMeasure.Refinement.Trimmed130.Sharp.factor_positive
