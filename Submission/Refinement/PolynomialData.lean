module

public import Submission.Refinement.PolynomialNorm
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Order.Fin.Basic

@[expose] public section

namespace CatalanMeasure.Refinement

open Polynomial

def rationalHorner : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: as, x => a + x * rationalHorner as x

def coefficientAt (as : List ℚ) (n : ℕ) : ℚ := as[n]?.getD 0

theorem polynomialFromCoeffs_eval (as : List ℚ) (x : ℚ) :
    (polynomialFromCoeffs as).eval x = rationalHorner as x := by
  induction as with
  | nil => simp [polynomialFromCoeffs, rationalHorner]
  | cons a as ih => simp [polynomialFromCoeffs, rationalHorner, ih]

theorem polynomialFromCoeffs_eval_map_real (as : List ℚ) (x : ℚ) :
    ((polynomialFromCoeffs as).map (algebraMap ℚ ℝ)).eval (x : ℝ) =
      (rationalHorner as x : ℝ) := by
  induction as with
  | nil => simp [polynomialFromCoeffs, rationalHorner]
  | cons a as ih => simp [polynomialFromCoeffs, rationalHorner, ih]

theorem polynomialFromCoeffs_coeff (as : List ℚ) (n : ℕ) :
    (polynomialFromCoeffs as).coeff n = coefficientAt as n := by
  induction as generalizing n with
  | nil => simp [polynomialFromCoeffs, coefficientAt]
  | cons a as ih =>
    cases n with
    | zero => simp [polynomialFromCoeffs, coefficientAt]
    | succ n => simp [polynomialFromCoeffs, coefficientAt, coeff_X_mul, ih]

theorem polynomialFromCoeffs_natDegree_le (as : List ℚ) (n : ℕ)
    (hlen : as.length ≤ n + 1) : (polynomialFromCoeffs as).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [polynomialFromCoeffs_coeff]
  have hli : as.length ≤ i := by omega
  simp [coefficientAt, List.getElem?_eq_none hli]

theorem polynomialFromCoeffs_natDegree_eq (as : List ℚ) (n : ℕ)
    (hlen : as.length ≤ n + 1) (hcoeff : coefficientAt as n ≠ 0) :
    (polynomialFromCoeffs as).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (polynomialFromCoeffs_natDegree_le as n hlen)
  rwa [polynomialFromCoeffs_coeff]

theorem polynomialFromCoeffs_leadingCoeff (as : List ℚ) (n : ℕ)
    (hlen : as.length ≤ n + 1) (hcoeff : coefficientAt as n ≠ 0) :
    (polynomialFromCoeffs as).leadingCoeff = coefficientAt as n := by
  rw [Polynomial.leadingCoeff, polynomialFromCoeffs_natDegree_eq as n hlen hcoeff,
    polynomialFromCoeffs_coeff]

theorem ordered_intervals_separated {n : ℕ} {left right : Fin (n + 1) → ℚ}
    (hord : ∀ i, left i ≤ right i)
    (hadj : ∀ i : Fin n, right i.castSucc ≤ left i.succ) :
    ∀ i j, i < j → right i ≤ left j := by
  have hmono : Monotone left := Fin.monotone_iff_le_succ.mpr
    (fun i => (hord i.castSucc).trans (hadj i))
  intro i j hij
  have hi : i.val < n := by have := j.isLt; exact Nat.lt_of_lt_of_le hij (Nat.le_of_lt_succ this)
  let k : Fin n := ⟨i.val, hi⟩
  have hk : k.castSucc = i := Fin.ext rfl
  have hkj : k.succ ≤ j := by change i.val + 1 ≤ j.val; exact hij
  rw [← hk]
  exact (hadj k).trans (hmono hkj)

end CatalanMeasure.Refinement
