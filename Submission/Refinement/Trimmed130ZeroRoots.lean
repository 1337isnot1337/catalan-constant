module

public import Submission.Refinement.InverseBranches
public import Submission.Refinement.Trimmed130Degree
public import Submission.Refinement.Trimmed130ZeroChecks

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

open Polynomial Set CatalanMeasure.GenD.Analytic Finset

theorem exists_zero_in_bracket (i : Fin 130) :
    ∃ x ∈ Ioo (zeroLeft i : ℝ) (zeroRight i : ℝ), realP.eval x = 0 := by
  have ho : (zeroLeft i : ℝ) ≤ zeroRight i := by exact_mod_cast (zero_ordered i).le
  have hs : (realP.eval (zeroLeft i : ℝ) < 0 ∧ 0 < realP.eval (zeroRight i : ℝ)) ∨
      (realP.eval (zeroRight i : ℝ) < 0 ∧ 0 < realP.eval (zeroLeft i : ℝ)) := by
    rw [realP_eval_rational, realP_eval_rational]
    exact_mod_cast zero_signs i
  rcases hs with h | h
  · exact intermediate_value_Ioo ho realP.continuousOn h
  · exact intermediate_value_Ioo' ho realP.continuousOn h

noncomputable def zeroRoots (i : Fin 130) : ℝ := Classical.choose (exists_zero_in_bracket i)

theorem zeroRoots_mem (i : Fin 130) :
    zeroRoots i ∈ Ioo (zeroLeft i : ℝ) (zeroRight i : ℝ) :=
  (Classical.choose_spec (exists_zero_in_bracket i)).1

theorem zeroRoots_location (i : Fin 130) :
    (zeroLeft i : ℝ) ≤ zeroRoots i ∧ zeroRoots i ≤ (zeroRight i : ℝ) :=
  Ioo_subset_Icc_self (zeroRoots_mem i)

theorem zeroRoots_unit (i : Fin 130) : zeroRoots i ∈ Ioo (-1 : ℝ) 1 := by
  have hg : (-1 : ℝ) ≤ zeroLeft i ∧ (zeroRight i : ℝ) ≤ 1 := by
    exact_mod_cast zero_geometry i
  exact ⟨lt_of_le_of_lt hg.1 (zeroRoots_mem i).1,
    lt_of_lt_of_le (zeroRoots_mem i).2 hg.2⟩

theorem zeroRoots_eval (i : Fin 130) : realP.eval (zeroRoots i) = 0 :=
  (Classical.choose_spec (exists_zero_in_bracket i)).2

theorem zeroRoots_injective : Function.Injective zeroRoots := by
  intro i j hij
  have hi := zeroRoots_mem i
  have hj := zeroRoots_mem j
  rcases lt_trichotomy i j with h | h | h
  · have hs : (zeroRight i : ℝ) ≤ zeroLeft j := by exact_mod_cast zero_separated i j h
    linarith only [hi.2, hj.1, hs, hij]
  · exact h
  · have hs : (zeroRight j : ℝ) ≤ zeroLeft i := by exact_mod_cast zero_separated j i h
    linarith only [hi.1, hj.2, hs, hij]

theorem realP_factorization :
    realP = C (leadingCoefficient : ℝ) * ∏ i : Fin 130, (X - C (zeroRoots i)) := by
  have h := factorization_of_distinct_roots realP_ne_zero realP_natDegree zeroRoots
    zeroRoots_injective zeroRoots_eval
  rwa [realP_leadingCoeff] at h

end CatalanMeasure.Refinement.Trimmed130
