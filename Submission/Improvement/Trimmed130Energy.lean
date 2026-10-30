module

public import Submission.Improvement.Fields.NearTrimmed
public import Submission.Improvement.Fields.ResidualTrimmed
public import Submission.Improvement.Fields.SecondEventually
public import Submission.Refinement.Trimmed130Scalars
public import Submission.CatalanMeasure.GenD.D58.FirstTrialCert
public import Submission.CatalanMeasure.GenD.D58.Cert590.XCover
public import Submission.CatalanMeasure.GenD.D58.Cert590.YCover
public import Submission.CatalanMeasure.GenD.D58.Cert590.Norm

@[expose] public section

/-! Concrete field providers for the trimmed degree-130 quadrature.
The trial sequences, row and column suprema, and norm bounds are unchanged.
The new support residual and eventual near-field cap supply the stronger budget.
-/

namespace CatalanMeasure.GenD.Refinement.Trimmed130

open CatalanMeasure.Parametric CatalanMeasure.CellCert CatalanMeasure.Cert
open OAI.InternalCatalan Analytic Set Filter
open CatalanMeasure.Improvement.Fields

noncomputable section

def first : FirstTrialBounds D58.Odd.design target D58.K590.firstCost :=
  D58.firstTrial_D58 D58.hrow_D58 D58.hcol_D58 (by
    intro a
    have h := first_budget a
    nlinarith only [h])

def secondU : ℕ → ℝ := trialSeqS D58.Cert590.Pc D58.Cert590.P
def secondV : ℕ → ℝ := trialSeqS D58.Cert590.Vc D58.Cert590.V

theorem second_hu : Summable (fun k => |secondU k|) :=
  (trialSeqS_summable D58.Cert590.tailsP).1

theorem second_hv : Summable (fun k => |secondV k|) :=
  (trialSeqS_summable D58.Cert590.tailsV).1

theorem second_field_sum :
    ((D58.Cert590.MX : ℚ) : ℝ) + ((D58.Cert590.MY : ℚ) : ℝ) = D58.K590.fieldCap := by
  norm_num [D58.Cert590.MX, D58.Cert590.MY, D58.K590.fieldCap]

theorem second_norm_le :
    2 * barrierTrialNormSq secondU + barrierTrialNormSq secondV / 2 ≤ D58.K590.normCap := by
  have h := D58.Cert590.weighted_norm_le
  have h2 : (((2 * D58.Cert590.NP + D58.Cert590.NV / 2 : ℚ)) : ℝ) ≤ D58.K590.normCap := by
    norm_num [D58.Cert590.NP, D58.Cert590.NV, D58.K590.normCap]
  exact h.trans h2

theorem second_row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    rowFieldG (11 / 29) (3 / 29) (39 / 29) secondU secondV x ≤
      ((D58.Cert590.MX : ℚ) : ℝ) := by
  intro x hx
  have h := D58.Cert590.row_sup_S x hx
  have e : rowFieldS D58.Cert590.R D58.Cert590.Pc D58.Cert590.Vc
      D58.Cert590.P D58.Cert590.V =
      rowFieldG (11 / 29) (3 / 29) (39 / 29) secondU secondV := by
    unfold rowFieldS secondU secondV
    norm_num [D58.Cert590.R]
  rw [e] at h
  exact h

theorem second_column_sup : ∀ s ∈ Ioo (0 : ℝ) 1,
    colFieldG (9 / 58) (3 / 58) secondV s ≤ ((D58.Cert590.MY : ℚ) : ℝ) := by
  intro s hs
  have h := D58.Cert590.column_sup_S s hs
  have e : colFieldS D58.Cert590.C D58.Cert590.Vc D58.Cert590.V =
      colFieldG (9 / 58) (3 / 58) secondV := by
    unfold colFieldS secondV
    norm_num [D58.Cert590.C]
  rw [e] at h
  exact h

theorem second_near_eventually :
    ∀ᶠ N : ℕ in atTop, ∀ {y : ℝ}, y ∈ Ioo (0 : ℝ) 1 →
      groupedNearField D58.Odd.design N y - secondU 1 * y ≤
        nearCap + Real.log 2 / (D58.Odd.design.n N : ℝ) := by
  filter_upwards [grouped_near_trimmed_eventually] with N hN y hy
  have h := hN y hy
  have hc : 0 ≤ Real.log 2 / (D58.Odd.design.n N : ℝ) :=
    div_nonneg (Real.log_nonneg (by norm_num)) (Nat.cast_nonneg _)
  change groupedNearField D58.Odd.design N y - secondU 1 * y ≤
    -(78145547 / 100000000 : ℝ) at h
  dsimp only [nearCap]
  linarith only [h, hc]

def second : SecondTrialBoundsEventually D58.Odd.design target residualCap nearCap
    secondCost trimmedResidualSupport :=
  secondTrialEventually_of_fields D58.Odd.design_admissible
    (normCap := D58.K590.normCap) (fieldCap := D58.K590.fieldCap)
    secondU secondV second_hu second_hv
    (11 / 29) (3 / 29) (39 / 29) (9 / 58) (3 / 58)
    (by norm_num [D58.Odd.design]) (by norm_num [D58.Odd.design])
    (by norm_num [D58.Odd.design]) (by norm_num [D58.Odd.design])
    (by norm_num [D58.Odd.design])
    ((D58.Cert590.MX : ℚ) : ℝ) ((D58.Cert590.MY : ℚ) : ℝ) nearCap
    second_near_eventually second_norm_le second_field_sum second_row_sup second_column_sup
    (fun x _ hx => by
      simpa [secondU, residualCap] using residual_sup_trimmed x hx)
    (by
      intro a t ha ht
      rw [Instances.d58_gC0, Instances.d58_gC1]
      have h := second_budget ha ht
      norm_num [D58.c07, D58.c26] at h
      exact h)

end
end CatalanMeasure.GenD.Refinement.Trimmed130

#print axioms CatalanMeasure.GenD.Refinement.Trimmed130.first
#print axioms CatalanMeasure.GenD.Refinement.Trimmed130.second
