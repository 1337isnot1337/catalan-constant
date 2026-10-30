module

public import Submission.Refinement.Trimmed130Data
public import Submission.Refinement.PolynomialData

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

open Polynomial

def leadingCoefficient : ℚ := coefficientAt powerCoefficients 130

theorem powerCoefficients_length : powerCoefficients.length = 131 := by decide +kernel

theorem leadingCoefficient_pos : 0 < leadingCoefficient := by decide +kernel

theorem leadingCoefficient_ne_zero : leadingCoefficient ≠ 0 := leadingCoefficient_pos.ne'

theorem rationalP_natDegree : rationalP.natDegree = 130 := by
  apply polynomialFromCoeffs_natDegree_eq powerCoefficients 130
  · rw [powerCoefficients_length]
  · exact leadingCoefficient_ne_zero

theorem rationalP_leadingCoeff : rationalP.leadingCoeff = leadingCoefficient := by
  apply polynomialFromCoeffs_leadingCoeff powerCoefficients 130
  · rw [powerCoefficients_length]
  · exact leadingCoefficient_ne_zero

theorem realP_natDegree : realP.natDegree = 130 := by
  rw [realP, Polynomial.natDegree_map, rationalP_natDegree]

theorem realP_leadingCoeff : realP.leadingCoeff = (leadingCoefficient : ℝ) := by
  rw [realP, Polynomial.leadingCoeff_map, rationalP_leadingCoeff]
  rfl

theorem realP_ne_zero : realP ≠ 0 := by
  intro h
  have hh := congrArg Polynomial.natDegree h
  rw [realP_natDegree, natDegree_zero] at hh
  norm_num at hh

theorem realP_eval_rational (x : ℚ) :
    realP.eval (x : ℝ) = (rationalHorner powerCoefficients x : ℝ) :=
  polynomialFromCoeffs_eval_map_real powerCoefficients x

end CatalanMeasure.Refinement.Trimmed130
