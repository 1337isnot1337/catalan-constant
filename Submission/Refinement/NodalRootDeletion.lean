module

public import Submission.CatalanMeasure.GenD.Analytic.GapWeights

@[expose] public section

/-!
# Removing a bounded number of real nodal roots

The input polynomial has `J + S` distinct roots in `(-1,1)`. Retain the first
`J` roots and absorb its leading scalar into their nodal polynomial. If
`S ≤ M`, the derivative lower bound loses at most `2^M` and the circle bound
loses at most `(radius - 1)^(-M)`. Both losses are independent of scale when
`M` is fixed.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial Finset OAI.InternalCatalan CatalanMeasure.Parametric

noncomputable section

def retainedNodes {J S : ℕ} (τ : Fin (J + S) → ℝ) : Fin J → ℝ :=
  fun i => τ (Fin.castAdd S i)

def removedNodal {J S : ℕ} (τ : Fin (J + S) → ℝ) : ℝ[X] :=
  ∏ i : Fin S, (X - C (τ (Fin.natAdd J i)))

def retainedNodal {J S : ℕ} (τ : Fin (J + S) → ℝ) (c : ℝ) : ℝ[X] :=
  C c * ∏ i : Fin J, (X - C (retainedNodes τ i))

theorem retainedNodes_injective {J S : ℕ} {τ : Fin (J + S) → ℝ}
    (hτ : Function.Injective τ) : Function.Injective (retainedNodes τ) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun a : Fin (J + S) => a.val) (hτ hij)

theorem retained_removed_factorization {J S : ℕ} (τ : Fin (J + S) → ℝ) (c : ℝ) :
    C c * ∏ i : Fin (J + S), (X - C (τ i)) =
      retainedNodal τ c * removedNodal τ := by
  rw [Fin.prod_univ_add]
  simp only [retainedNodal, removedNodal, retainedNodes]
  ring

theorem retainedNodal_eval_node {J S : ℕ} (τ : Fin (J + S) → ℝ) (c : ℝ)
    (i : Fin J) : (retainedNodal τ c).eval (retainedNodes τ i) = 0 := by
  rw [retainedNodal, eval_mul, eval_C, eval_prod]
  apply mul_eq_zero_of_right
  exact prod_eq_zero (mem_univ i) (by simp)

theorem removedNodal_eval_abs_le {J S M : ℕ} {τ : Fin (J + S) → ℝ}
    (hmem : ∀ i, τ i ∈ Set.Ioo (-1 : ℝ) 1) (hSM : S ≤ M)
    {t : ℝ} (ht : |t| ≤ 1) : |(removedNodal τ).eval t| ≤ 2 ^ M := by
  unfold removedNodal
  rw [eval_prod, abs_prod]
  have hf : ∀ i : Fin S, |(X - C (τ (Fin.natAdd J i)) : ℝ[X]).eval t| ≤ 2 := by
    intro i
    have hp := hmem (Fin.natAdd J i)
    have ht' := abs_le.mp ht
    simp only [eval_sub, eval_X, eval_C]
    rw [abs_le]
    constructor <;> linarith only [ht'.1, ht'.2, hp.1, hp.2]
  have hc : (∏ i : Fin S, |(X - C (τ (Fin.natAdd J i)) : ℝ[X]).eval t|) ≤
      ∏ _i : Fin S, (2 : ℝ) :=
    Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hf i)
  calc
    _ ≤ _ := hc
    _ = (2 : ℝ) ^ S := by simp
    _ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hSM

theorem removedNodal_norm_ge {J S M : ℕ} {τ : Fin (J + S) → ℝ}
    (hmem : ∀ i, τ i ∈ Set.Ioo (-1 : ℝ) 1) (hSM : S ≤ M)
    {radius : ℝ} (hr1 : 1 < radius) (hr2 : radius ≤ 2)
    (z : ℂ) (hz : ‖z‖ = radius) :
    (radius - 1) ^ M ≤ ‖((removedNodal τ).map (algebraMap ℝ ℂ)).eval z‖ := by
  unfold removedNodal
  rw [Polynomial.map_prod, eval_prod, norm_prod]
  have hf : ∀ i : Fin S, radius - 1 ≤
      ‖(((X - C (τ (Fin.natAdd J i)) : ℝ[X]).map (algebraMap ℝ ℂ)).eval z)‖ := by
    intro i
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      eval_sub, eval_X, eval_C, Complex.coe_algebraMap]
    have hh := norm_sub_norm_le z (τ (Fin.natAdd J i) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, hz] at hh
    have hi := abs_lt.mpr (hmem (Fin.natAdd J i))
    linarith only [hh, hi]
  have hc : (∏ _i : Fin S, (radius - 1)) ≤
      ∏ i : Fin S,
        ‖(((X - C (τ (Fin.natAdd J i)) : ℝ[X]).map (algebraMap ℝ ℂ)).eval z)‖ :=
    Finset.prod_le_prod₀ (fun _ _ => by linarith only [hr1]) (fun i _ => hf i)
  have hpow : (radius - 1) ^ M ≤ (radius - 1) ^ S :=
    pow_le_pow_of_le_one (by linarith only [hr1]) (by linarith only [hr2]) hSM
  exact hpow.trans (by simpa using hc)

/-- Transfer a derivative lower bound from the original polynomial to the
polynomial obtained by deleting the final `S` roots. -/
theorem retainedNodal_derivative_ge {J S M : ℕ} {τ : Fin (J + S) → ℝ}
    (hmem : ∀ i, τ i ∈ Set.Ioo (-1 : ℝ) 1) (hSM : S ≤ M)
    {H : ℝ[X]} {c d : ℝ}
    (hH : H = C c * ∏ i : Fin (J + S), (X - C (τ i)))
    (hder : ∀ i, d ≤ |(derivative H).eval (τ i)|) (i : Fin J) :
    d / 2 ^ M ≤ |(derivative (retainedNodal τ c)).eval (retainedNodes τ i)| := by
  have hsplit : H = retainedNodal τ c * removedNodal τ :=
    hH.trans (retained_removed_factorization τ c)
  have hnode := retainedNodal_eval_node τ c i
  have he : (derivative H).eval (retainedNodes τ i) =
      (derivative (retainedNodal τ c)).eval (retainedNodes τ i) *
        (removedNodal τ).eval (retainedNodes τ i) := by
    rw [hsplit, derivative_mul, eval_add, eval_mul, eval_mul, hnode]
    ring
  have hmemi := hmem (Fin.castAdd S i)
  have ht : |retainedNodes τ i| ≤ 1 := by
    exact (abs_lt.mpr hmemi).le
  have hE := removedNodal_eval_abs_le hmem hSM ht
  have hh := hder (Fin.castAdd S i)
  change d ≤ |(derivative H).eval (retainedNodes τ i)| at hh
  rw [he, abs_mul] at hh
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ M)).mpr
  exact hh.trans (mul_le_mul_of_nonneg_left hE (abs_nonneg _))

/-- Transfer a weighted circle bound through deletion of at most `M` roots. -/
theorem retainedNodal_circle_le {J S M h : ℕ} {τ : Fin (J + S) → ℝ}
    (hmem : ∀ i, τ i ∈ Set.Ioo (-1 : ℝ) 1) (hSM : S ≤ M)
    {H : ℝ[X]} {c radius B : ℝ}
    (hH : H = C c * ∏ i : Fin (J + S), (X - C (τ i)))
    (hr1 : 1 < radius) (hr2 : radius ≤ 2)
    (hcirc : ∀ z : ℂ, ‖z‖ = radius →
      ‖(H.map (algebraMap ℝ ℂ)).eval z‖ * ‖(1 : ℂ) - z‖ ^ h ≤ B)
    (z : ℂ) (hz : ‖z‖ = radius) :
    ‖((retainedNodal τ c).map (algebraMap ℝ ℂ)).eval z‖ *
      ‖(1 : ℂ) - z‖ ^ h ≤ B / (radius - 1) ^ M := by
  have hsplit : H = retainedNodal τ c * removedNodal τ :=
    hH.trans (retained_removed_factorization τ c)
  have hn := congrArg (fun Q : ℝ[X] => ‖(Q.map (algebraMap ℝ ℂ)).eval z‖) hsplit
  simp only [Polynomial.map_mul, eval_mul, norm_mul] at hn
  have hE := removedNodal_norm_ge hmem hSM hr1 hr2 z hz
  have hQ0 := norm_nonneg (((retainedNodal τ c).map (algebraMap ℝ ℂ)).eval z)
  have hf0 : 0 ≤ ‖(1 : ℂ) - z‖ ^ h := by positivity
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (radius - 1) ^ M)).mpr
  calc
    _ = (‖((retainedNodal τ c).map (algebraMap ℝ ℂ)).eval z‖ *
        (radius - 1) ^ M) * ‖(1 : ℂ) - z‖ ^ h := by ring
    _ ≤ (‖((retainedNodal τ c).map (algebraMap ℝ ℂ)).eval z‖ *
        ‖((removedNodal τ).map (algebraMap ℝ ℂ)).eval z‖) *
        ‖(1 : ℂ) - z‖ ^ h :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hQ0) hf0
    _ = ‖(H.map (algebraMap ℝ ℂ)).eval z‖ * ‖(1 : ℂ) - z‖ ^ h := by rw [← hn]
    _ ≤ B := hcirc z hz

end
end Analytic
end CatalanMeasure.GenD
