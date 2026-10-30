module

public import Submission.Improvement.Trimmed130Energy
public import Submission.Improvement.Fields.DecayEventually
public import Submission.Refinement.Trimmed130Nodes

@[expose] public section

/-! Determinant decay for the trimmed degree-130 quadrature and its certified
energy budgets.  This is the analytic input to the final irrationality measure
criterion; all node, field and scalar hypotheses are discharged here. -/

namespace CatalanMeasure.GenD.Refinement.Trimmed130

open Analytic OAI.InternalCatalan Filter Polynomial
open CatalanMeasure.Improvement.Fields CatalanMeasure.Parametric
open scoped Topology

theorem delta_small :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(rho * (N : ℝ))) →
        |aeval x (deltaPoly D58.Odd.design N)| ≤
          Real.exp (-((tDelta - ε) * (N : ℝ) ^ 2)) := by
  have hfirst : (D58.Odd.design.n0 : ℝ) * D58.K590.firstCost ≤
      58 * secondCost := by
    norm_num only [D58.Odd.design, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left first_cost_le (by norm_num)
  have hsecond : (D58.Odd.design.n0 : ℝ) * secondCost ≤ 58 * secondCost := by
    norm_num [D58.Odd.design]
  have htarget : tDelta = (D58.Odd.design.n0 : ℝ) ^ 2 *
      (target - Real.log 2 / 2) := by
    norm_num [tDelta, D58.Odd.design]
  exact delta_small_of_eventual_trials D58.Odd.design_admissible
    tau trimmedResidualSupport tau_injective tau_mem tau_ne_zero tau_support
    first second tau_weights hfirst hsecond htarget

end CatalanMeasure.GenD.Refinement.Trimmed130

#print axioms CatalanMeasure.GenD.Refinement.Trimmed130.delta_small
