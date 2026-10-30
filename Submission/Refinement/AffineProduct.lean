module

public import Submission.Refinement.PolynomialNorm

@[expose] public section

/-!
# Tangent bounds for products of positive affine functions

The basic inequality is `1 + t <= exp t`. No differentiation or numerical
optimization theorem is needed. Rational values and slopes supply finite
certificates after this general real-variable estimate.
-/

namespace CatalanMeasure.Refinement

def affineProductRat : List (ℚ × ℚ) → ℚ → ℚ
  | [], _ => 1
  | (a, b) :: fs, x => (a + b*x) * affineProductRat fs x

def affineSlopeRat : List (ℚ × ℚ) → ℚ → ℚ
  | [], _ => 0
  | (a, b) :: fs, x => b / (a + b*x) + affineSlopeRat fs x

noncomputable def affineProduct : List (ℚ × ℚ) → ℝ → ℝ
  | [], _ => 1
  | (a, b) :: fs, x => ((a : ℝ) + (b : ℝ)*x) * affineProduct fs x

noncomputable def affineSlope : List (ℚ × ℚ) → ℝ → ℝ
  | [], _ => 0
  | (a, b) :: fs, x => (b : ℝ) / ((a : ℝ) + (b : ℝ)*x) + affineSlope fs x

theorem affineProduct_cast (fs : List (ℚ × ℚ)) (x : ℚ) :
    (affineProductRat fs x : ℝ) = affineProduct fs (x : ℝ) := by
  induction fs with
  | nil => simp [affineProductRat, affineProduct]
  | cons f fs ih =>
      rcases f with ⟨a,b⟩
      simp [affineProductRat, affineProduct, ih]

theorem affineSlope_cast (fs : List (ℚ × ℚ)) (x : ℚ) :
    (affineSlopeRat fs x : ℝ) = affineSlope fs (x : ℝ) := by
  induction fs with
  | nil => simp [affineSlopeRat, affineSlope]
  | cons f fs ih =>
      rcases f with ⟨a,b⟩
      simp [affineSlopeRat, affineSlope, ih]

theorem affineProduct_nonneg (fs : List (ℚ × ℚ)) (x : ℝ)
    (h : ∀ f ∈ fs, 0 ≤ (f.1 : ℝ) + (f.2 : ℝ)*x) :
    0 ≤ affineProduct fs x := by
  induction fs with
  | nil => simp [affineProduct]
  | cons f fs ih =>
      rcases f with ⟨a,b⟩
      exact mul_nonneg (h (a,b) (by simp))
        (ih (fun f hf => h f (by simp [hf])))

theorem affine_le_tangent (a b c x : ℝ) (hc : 0 < a+b*c) :
    a+b*x ≤ (a+b*c) * Real.exp ((b/(a+b*c))*(x-c)) := by
  have he := Real.add_one_le_exp ((b/(a+b*c))*(x-c))
  have hh := mul_le_mul_of_nonneg_left he hc.le
  have hid : (a+b*c) * ((b/(a+b*c))*(x-c)+1) = a+b*x := by
    field_simp
    ring
  rw [hid] at hh
  exact hh

theorem affineProduct_tangent (fs : List (ℚ × ℚ)) (c x : ℝ)
    (hc : ∀ f ∈ fs, 0 < (f.1 : ℝ) + (f.2 : ℝ)*c)
    (hx : ∀ f ∈ fs, 0 ≤ (f.1 : ℝ) + (f.2 : ℝ)*x) :
    affineProduct fs x ≤ affineProduct fs c * Real.exp (affineSlope fs c * (x-c)) := by
  induction fs with
  | nil => simp [affineProduct, affineSlope]
  | cons f fs ih =>
      rcases f with ⟨a,b⟩
      have hc0 := hc (a,b) (by simp)
      have hct : ∀ f ∈ fs, 0 < (f.1 : ℝ) + (f.2 : ℝ)*c :=
        fun f hf => hc f (by simp [hf])
      have hxt : ∀ f ∈ fs, 0 ≤ (f.1 : ℝ) + (f.2 : ℝ)*x :=
        fun f hf => hx f (by simp [hf])
      have htail := ih hct hxt
      have hhead := affine_le_tangent (a : ℝ) (b : ℝ) c x hc0
      change ((a : ℝ)+(b : ℝ)*x) * affineProduct fs x ≤
        (((a : ℝ)+(b : ℝ)*c) * affineProduct fs c) *
          Real.exp (((b : ℝ)/((a : ℝ)+(b : ℝ)*c)+affineSlope fs c)*(x-c))
      calc
        _ ≤ (((a : ℝ)+(b : ℝ)*c) *
              Real.exp (((b : ℝ)/((a : ℝ)+(b : ℝ)*c))*(x-c))) *
            (affineProduct fs c * Real.exp (affineSlope fs c*(x-c))) :=
          mul_le_mul hhead htail (affineProduct_nonneg fs x hxt)
            (mul_nonneg hc0.le (Real.exp_pos _).le)
        _ = (((a : ℝ)+(b : ℝ)*c) * affineProduct fs c) *
            (Real.exp (((b : ℝ)/((a : ℝ)+(b : ℝ)*c))*(x-c)) *
              Real.exp (affineSlope fs c*(x-c))) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 2
          ring

theorem affine_positive_between (a b lo hi x : ℝ)
    (hlo : 0 < a+b*lo) (hhi : 0 < a+b*hi)
    (hxlo : lo ≤ x) (hxhi : x ≤ hi) : 0 < a+b*x := by
  by_cases hb : 0 ≤ b
  · have h := mul_le_mul_of_nonneg_left hxlo hb
    linarith
  · have h := mul_le_mul_of_nonpos_left hxhi (le_of_not_ge hb)
    linarith

end CatalanMeasure.Refinement
