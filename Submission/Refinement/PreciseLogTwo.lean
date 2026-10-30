module

public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants

@[expose] public section

/-!
# A rational enclosure for log 2

This specializes OpenAI's existing 18-term odd logarithm series and its
proved remainder bound. All finite comparisons use kernel-checked arithmetic.
-/

namespace CatalanMeasure.GenD.Refinement

open OAI.InternalCatalan

noncomputable section

def logTwoLo : ℝ := 693147180559945309 / 1000000000000000000
def logTwoHi : ℝ := 693147180559945310 / 1000000000000000000

theorem log_two_bounds : logTwoLo ≤ Real.log 2 ∧ Real.log 2 ≤ logTwoHi := by
  have h := barrier_logH_remainder_uniform (y := 2) ⟨by norm_num, le_rfl⟩
  have hv : barrierLogH 2 =
      (5796068539909855793494541848 : ℝ) / 8361959339180483840538659925 := by
    have hcast := barrierLogHRat_cast (2 : ℚ)
    rw [barrierLogHRat_two_eq] at hcast
    norm_num at hcast
    exact hcast.symm
  rw [hv] at h
  constructor
  · have hl : logTwoLo ≤
        (5796068539909855793494541848 : ℝ) / 8361959339180483840538659925 := by
      norm_num [logTwoLo]
    linarith [h.1]
  · have hh :
        (5796068539909855793494541848 : ℝ) / 8361959339180483840538659925 +
          barrierLogHError ≤ logTwoHi := by
      norm_num [logTwoHi, barrierLogHError]
    linarith [h.2]

end
end CatalanMeasure.GenD.Refinement

#print axioms CatalanMeasure.GenD.Refinement.log_two_bounds
