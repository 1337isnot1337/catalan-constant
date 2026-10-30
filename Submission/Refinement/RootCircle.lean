module

public import Submission.Refinement.AffineProduct
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Circle bounds from real-root enclosures

Positive affine majorants for squared root distances admit a global exponential
tangent bound. This file proves the analytic inequalities independently of the
particular rational certificate.
-/

namespace CatalanMeasure.Refinement

open Polynomial Finset

theorem affineProduct_eq_list_prod (fs : List (ℚ × ℚ)) (x : ℝ) :
    affineProduct fs x = (fs.map fun f => (f.1 : ℝ) + (f.2 : ℝ) * x).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [affineProduct, ih]

theorem affineProduct_ofFn {m : ℕ} (fs : Fin m → ℚ × ℚ) (x : ℝ) :
    affineProduct (List.ofFn fs) x = ∏ i, (((fs i).1 : ℝ) + ((fs i).2 : ℝ) * x) := by
  rw [affineProduct_eq_list_prod, List.map_ofFn, List.prod_ofFn]
  rfl

theorem weighted_affine_tangent (fs : List (ℚ × ℚ))
    (L da db c x : ℝ) (u v : ℕ)
    (hc : ∀ f ∈ fs, 0 < (f.1 : ℝ) + (f.2 : ℝ) * c)
    (hx : ∀ f ∈ fs, 0 ≤ (f.1 : ℝ) + (f.2 : ℝ) * x)
    (hdc : 0 < da + db * c) (hdx : 0 ≤ da + db * x) :
    (L ^ 2 * affineProduct fs x) ^ u * (da + db * x) ^ v ≤
      ((L ^ 2 * affineProduct fs c) ^ u * (da + db * c) ^ v) *
        Real.exp (((u : ℝ) * affineSlope fs c +
          (v : ℝ) * (db / (da + db * c))) * (x - c)) := by
  have hpc := affineProduct_nonneg fs c (fun f hf => (hc f hf).le)
  have hpx := affineProduct_nonneg fs x hx
  have hp := mul_le_mul_of_nonneg_left (affineProduct_tangent fs c x hc hx) (sq_nonneg L)
  have hpp : L ^ 2 * affineProduct fs x ≤
      (L ^ 2 * affineProduct fs c) * Real.exp (affineSlope fs c * (x - c)) := by
    simpa only [mul_assoc] using hp
  have hd := affine_le_tangent da db c x hdc
  calc
    _ ≤ ((L ^ 2 * affineProduct fs c) * Real.exp (affineSlope fs c * (x-c))) ^ u *
        ((da + db*c) * Real.exp ((db/(da+db*c))*(x-c))) ^ v :=
      mul_le_mul (pow_le_pow_left₀ (mul_nonneg (sq_nonneg L) hpx) hpp u)
        (pow_le_pow_left₀ hdx hd v) (pow_nonneg hdx v) (by positivity)
    _ = ((L ^ 2 * affineProduct fs c) ^ u * (da + db*c) ^ v) *
        (Real.exp ((u : ℝ) * (affineSlope fs c * (x-c))) *
         Real.exp ((v : ℝ) * ((db/(da+db*c))*(x-c)))) := by
      simp only [mul_pow, ← Real.exp_nat_mul]
      ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

theorem sq_norm_sub_real (z : ℂ) (t : ℝ) :
    ‖z - (t : ℂ)‖ ^ 2 = ‖z‖ ^ 2 - 2 * t * z.re + t ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  ring

theorem sq_norm_sub_real_upper (z : ℂ) (r a b t : ℝ)
    (hz : ‖z‖ = r) (ha : -1 ≤ a) (ht : t ≤ 1)
    (hat : a ≤ t) (htb : t ≤ b) :
    ‖z - (t : ℂ)‖ ^ 2 ≤ r ^ 2 + a ^ 2 + 2 * (b-a) * (r+1) - 2*a*z.re := by
  have hr : 0 ≤ r := hz ▸ norm_nonneg z
  have hxr : -r ≤ z.re := by
    have h := Complex.abs_re_le_norm z
    rw [hz] at h
    exact (abs_le.mp h).1
  have hta : 0 ≤ t-a := sub_nonneg.mpr hat
  have hab : t-a ≤ b-a := sub_le_sub_right htb a
  have hsum : t+a-2*z.re ≤ 2*(r+1) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hta
  have hmul2 := mul_le_mul_of_nonneg_right hab (by linarith : 0 ≤ 2*(r+1))
  rw [sq_norm_sub_real, hz]
  nlinarith

theorem sq_norm_sub_real_lower (z : ℂ) (r h t : ℝ)
    (hz : ‖z‖ = r) (hh : 0 ≤ h) (hx : |z.re| ≤ h) :
    r ^ 2 - h ^ 2 ≤ ‖z - (t : ℂ)‖ ^ 2 := by
  have hx2 : z.re ^ 2 ≤ h ^ 2 := by
    nlinarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
  rw [sq_norm_sub_real, hz]
  nlinarith [sq_nonneg (t-z.re)]

theorem polynomial_norm_sq_factorization {m : ℕ} (p : ℝ[X]) (L : ℝ)
    (roots : Fin m → ℝ)
    (hf : p = C L * ∏ i, (X - C (roots i))) (z : ℂ) :
    ‖(p.map (algebraMap ℝ ℂ)).eval z‖ ^ 2 =
      L ^ 2 * ∏ i, ‖z - (roots i : ℂ)‖ ^ 2 := by
  rw [hf]
  simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_C,
    Polynomial.map_sub, Polynomial.map_X, eval_mul, eval_prod, eval_C,
    eval_sub, eval_X, norm_mul, norm_prod, mul_pow, Finset.prod_pow]
  simp only [Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem polynomial_norm_sq_lower {m : ℕ} (p : ℝ[X]) (L : ℝ)
    (roots : Fin m → ℝ) (hf : p = C L * ∏ i, (X - C (roots i)))
    (z : ℂ) (r h : ℝ) (hz : ‖z‖ = r) (hh : 0 ≤ h)
    (hx : |z.re| ≤ h) (hl : 0 ≤ r ^ 2 - h ^ 2) :
    L ^ 2 * (r ^ 2 - h ^ 2) ^ m ≤ ‖(p.map (algebraMap ℝ ℂ)).eval z‖ ^ 2 := by
  rw [polynomial_norm_sq_factorization p L roots hf z]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg L)
  have hprod := Finset.prod_le_prod₀
    (fun (i : Fin m) (_ : i ∈ Finset.univ) => hl)
    (fun (i : Fin m) (_ : i ∈ Finset.univ) => sq_norm_sub_real_lower z r h (roots i) hz hh hx)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod

theorem two_mul_add_one_pow_le (p : ℝ) (n : ℕ) (hp : 0 ≤ p) :
    (2*p+1) ^ n ≤ 3 ^ n * (p ^ n + 1) := by
  by_cases h : p ≤ 1
  · have hb : 2*p+1 ≤ 3 := by linarith
    calc
      _ ≤ (3 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hb n
      _ ≤ 3 ^ n * (p ^ n + 1) := by
        nlinarith [mul_nonneg (show 0 ≤ (3 : ℝ) ^ n by positivity) (pow_nonneg hp n)]
  · have hb : 2*p+1 ≤ 3*p := by linarith
    calc
      _ ≤ (3*p) ^ n := pow_le_pow_left₀ (by positivity) hb n
      _ = 3 ^ n * p ^ n := mul_pow _ _ _
      _ ≤ 3 ^ n * (p ^ n + 1) := by nlinarith [show 0 ≤ (3 : ℝ) ^ n by positivity]

theorem two_mul_add_one_le_of_minimum (p M : ℝ) (hM : 0 < M) (hp : M ≤ p) :
    2*p+1 ≤ (2+1/M)*p := by
  have hh : 1 ≤ p / M := (le_div_iff₀ hM).mpr (by simpa using hp)
  rw [div_eq_mul_inv] at hh
  simp only [one_div]
  nlinarith

theorem central_weighted_estimate (p D M C eps E : ℝ)
    (hp : 0 ≤ p) (hD : 0 ≤ D) (hM : 0 < M) (hmp : M ≤ p)
    (hweighted : p ^ 106 * D ^ 780 ≤ C * Real.exp eps)
    (hfinite : (2 + 1/M) ^ 106 * C ≤ Real.exp (E-eps)) :
    (2*p+1) ^ 106 * D ^ 780 ≤ Real.exp E := by
  have hscale : 0 ≤ (2 + 1/M : ℝ) ^ 106 := by positivity
  calc
    _ ≤ ((2+1/M)*p) ^ 106 * D ^ 780 :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (two_mul_add_one_le_of_minimum p M hM hmp) 106)
        (pow_nonneg hD _)
    _ = (2+1/M) ^ 106 * (p ^ 106 * D ^ 780) := by rw [mul_pow]; ring
    _ ≤ (2+1/M) ^ 106 * (C * Real.exp eps) :=
      mul_le_mul_of_nonneg_left hweighted hscale
    _ = ((2+1/M) ^ 106 * C) * Real.exp eps := by ring
    _ ≤ Real.exp (E-eps) * Real.exp eps :=
      mul_le_mul_of_nonneg_right hfinite (Real.exp_pos _).le
    _ = Real.exp E := by rw [← Real.exp_add]; congr 1; ring

theorem outer_weighted_estimate (p D C R E : ℝ)
    (hp : 0 ≤ p) (hD : 0 ≤ D)
    (hweighted : p ^ 106 * D ^ 780 ≤ C) (hDcap : D ^ 780 ≤ R)
    (hfinite : 3 ^ 106 * (C + R) ≤ Real.exp E) :
    (2*p+1) ^ 106 * D ^ 780 ≤ Real.exp E := by
  calc
    _ ≤ (3 ^ 106 * (p ^ 106 + 1)) * D ^ 780 :=
      mul_le_mul_of_nonneg_right (two_mul_add_one_pow_le p 106 hp) (pow_nonneg hD _)
    _ = 3 ^ 106 * (p ^ 106 * D ^ 780 + D ^ 780) := by ring
    _ ≤ 3 ^ 106 * (C + R) := by gcongr
    _ ≤ Real.exp E := hfinite

end CatalanMeasure.Refinement
