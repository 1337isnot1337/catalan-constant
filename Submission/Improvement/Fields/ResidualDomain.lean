module

public import Mathlib.Data.Real.Basic

@[expose] public section

namespace CatalanMeasure.Improvement.Fields

def trimmedResidualCap : ℚ := -883 / 10000

def trimmedResidualSupport (x : ℝ) : Prop :=
  (-2409 / 2500 ≤ x ∧ x ≤ -19501 / 100000) ∨
    (98749 / 1000000 ≤ x ∧ x ≤ 1)

end CatalanMeasure.Improvement.Fields
