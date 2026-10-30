module

public import Submission.Refinement.Trimmed130BranchData
public import Submission.Refinement.Trimmed130ZeroData
public import Submission.Refinement.PolynomialData

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem branch_ordered : ∀ i : Fin 130, branchLeft i < branchRight i := by decide +kernel

theorem branch_adjacent : ∀ i : Fin 129, branchRight i.castSucc ≤ branchLeft i.succ := by
  decide +kernel

theorem branch_separated : ∀ i j : Fin 130, i < j → branchRight i ≤ branchLeft j :=
  ordered_intervals_separated (fun i => (branch_ordered i).le) branch_adjacent

theorem branch_geometry : ∀ i : Fin 130,
    -1 ≤ branchLeft i ∧ branchRight i ≤ 1 ∧
      ((outerLeft ≤ branchLeft i ∧ branchRight i ≤ innerLeft) ∨
        (innerRight ≤ branchLeft i ∧ branchRight i ≤ 1)) := by decide +kernel

theorem zero_ordered : ∀ i : Fin 130, zeroLeft i < zeroRight i := by decide +kernel

theorem zero_geometry : ∀ i : Fin 130, -1 ≤ zeroLeft i ∧ zeroRight i ≤ 1 := by
  decide +kernel

theorem zero_adjacent : ∀ i : Fin 129, zeroRight i.castSucc ≤ zeroLeft i.succ := by
  decide +kernel

theorem zero_separated : ∀ i j : Fin 130, i < j → zeroRight i ≤ zeroLeft j :=
  ordered_intervals_separated (fun i => (zero_ordered i).le) zero_adjacent

end CatalanMeasure.Refinement.Trimmed130
