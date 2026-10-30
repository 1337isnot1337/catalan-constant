module

public import Submission.Refinement.SignChunks.Branch00
public import Submission.Refinement.SignChunks.Branch01
public import Submission.Refinement.SignChunks.Branch02
public import Submission.Refinement.SignChunks.Branch03
public import Submission.Refinement.SignChunks.Branch04
public import Submission.Refinement.SignChunks.Branch05
public import Submission.Refinement.SignChunks.Branch06
public import Submission.Refinement.SignChunks.Branch07
public import Submission.Refinement.SignChunks.Branch08
public import Submission.Refinement.SignChunks.Branch09
public import Submission.Refinement.SignChunks.Branch10
public import Submission.Refinement.SignChunks.Branch11
public import Submission.Refinement.SignChunks.Branch12

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem branch_all_chunks : ∀ b : Fin 13, ∀ j : Fin 10,
    branchScaledSign (signIndex b j) := by
  intro b
  fin_cases b
  · exact branch_sign_chunk_0
  · exact branch_sign_chunk_1
  · exact branch_sign_chunk_2
  · exact branch_sign_chunk_3
  · exact branch_sign_chunk_4
  · exact branch_sign_chunk_5
  · exact branch_sign_chunk_6
  · exact branch_sign_chunk_7
  · exact branch_sign_chunk_8
  · exact branch_sign_chunk_9
  · exact branch_sign_chunk_10
  · exact branch_sign_chunk_11
  · exact branch_sign_chunk_12

theorem branch_scaled_signs (i : Fin 130) : branchScaledSign i := by
  obtain ⟨b, j, rfl⟩ := signIndex_surjective i
  exact branch_all_chunks b j

theorem branch_signs : ∀ i : Fin 130,
    (rationalHorner powerCoefficients (branchLeft i) < -1 ∧
      1 < rationalHorner powerCoefficients (branchRight i)) ∨
    (rationalHorner powerCoefficients (branchRight i) < -1 ∧
      1 < rationalHorner powerCoefficients (branchLeft i)) := by
  intro i
  rcases branch_scaled_signs i with h | h
  · exact Or.inl ⟨by simpa using horner_lt_of_scaled (branchLeft i) (-1) h.1,
      by simpa using lt_horner_of_scaled (branchRight i) 1 h.2⟩
  · exact Or.inr ⟨by simpa using horner_lt_of_scaled (branchRight i) (-1) h.1,
      by simpa using lt_horner_of_scaled (branchLeft i) 1 h.2⟩

end CatalanMeasure.Refinement.Trimmed130
