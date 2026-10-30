module

public import Submission.Refinement.InverseBranches
public import Submission.Refinement.Trimmed130Degree
public import Submission.Refinement.Trimmed130BranchChecks

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

open Polynomial Set CatalanMeasure.GenD.Analytic

noncomputable def branchCertificate : InverseBranchCertificate realP 130 allowedT where
  left i := (branchLeft i : ℝ)
  right i := (branchRight i : ℝ)
  ordered i := by exact_mod_cast branch_ordered i
  separated i j hij := by exact_mod_cast branch_separated i j hij
  support i x hx := by
    have hg : (-1 : ℝ) ≤ branchLeft i ∧ (branchRight i : ℝ) ≤ 1 ∧
        (((outerLeft : ℝ) ≤ branchLeft i ∧ (branchRight i : ℝ) ≤ innerLeft) ∨
          ((innerRight : ℝ) ≤ branchLeft i ∧ (branchRight i : ℝ) ≤ 1)) := by
      exact_mod_cast branch_geometry i
    have hleft : (innerLeft : ℝ) < 0 := by norm_num [innerLeft]
    have hright : (0 : ℝ) < innerRight := by norm_num [innerRight]
    refine ⟨⟨lt_of_le_of_lt hg.1 hx.1, lt_of_lt_of_le hx.2 hg.2.1⟩, ?_, ?_⟩
    · rcases hg.2.2 with hl | hr
      · exact ne_of_lt (lt_trans (lt_of_lt_of_le hx.2 hl.2) hleft)
      · exact ne_of_gt (lt_trans hright (lt_of_le_of_lt hr.1 hx.1))
    · rcases hg.2.2 with hl | hr
      · exact Or.inl ⟨(lt_of_le_of_lt hl.1 hx.1).le, (lt_of_lt_of_le hx.2 hl.2).le⟩
      · exact Or.inr ⟨(lt_of_le_of_lt hr.1 hx.1).le, (lt_of_lt_of_le hx.2 hr.2).le⟩
  alternating i := by
    rw [realP_eval_rational, realP_eval_rational]
    exact_mod_cast branch_signs i

end CatalanMeasure.Refinement.Trimmed130
