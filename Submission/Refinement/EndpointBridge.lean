import Submission.CatalanStatement
import Mathlib.Tactic.NormNum

/-!
# Bridge from a fixed endpoint inequality to the verifier target

The constant and target definitions are the unchanged Big O Speedrun statement.
This proof follows the verifier's docs/convert-layout.md bridge, with a rational
bound parameter. It introduces no assumption about reduced fractions.
-/

namespace CatalanMeasure.Refinement

open BigOSpeedrun.Catalan

theorem bound_of_endpoint {r : ℚ} (hr : 0 ≤ r)
    (h : Endpoint constant (r : ℝ)) : Bound r := by
  refine ⟨hr, ?_⟩
  intro s hs
  filter_upwards [h, Filter.eventually_ge_atTop 1] with b hb hb1 a
  have h1 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  exact lt_of_le_of_lt
    (Real.rpow_le_rpow_of_exponent_le h1 (neg_le_neg hs.le)) (hb a)

end CatalanMeasure.Refinement

#print axioms CatalanMeasure.Refinement.bound_of_endpoint
