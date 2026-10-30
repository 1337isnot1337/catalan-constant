module

public import Submission.Refinement.SignChunks.Zero00
public import Submission.Refinement.SignChunks.Zero01
public import Submission.Refinement.SignChunks.Zero02
public import Submission.Refinement.SignChunks.Zero03
public import Submission.Refinement.SignChunks.Zero04
public import Submission.Refinement.SignChunks.Zero05
public import Submission.Refinement.SignChunks.Zero06
public import Submission.Refinement.SignChunks.Zero07
public import Submission.Refinement.SignChunks.Zero08
public import Submission.Refinement.SignChunks.Zero09
public import Submission.Refinement.SignChunks.Zero10
public import Submission.Refinement.SignChunks.Zero11
public import Submission.Refinement.SignChunks.Zero12

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem zero_all_chunks : ∀ b : Fin 13, ∀ j : Fin 10,
    zeroScaledSign (signIndex b j) := by
  intro b
  fin_cases b
  · exact zero_sign_chunk_0
  · exact zero_sign_chunk_1
  · exact zero_sign_chunk_2
  · exact zero_sign_chunk_3
  · exact zero_sign_chunk_4
  · exact zero_sign_chunk_5
  · exact zero_sign_chunk_6
  · exact zero_sign_chunk_7
  · exact zero_sign_chunk_8
  · exact zero_sign_chunk_9
  · exact zero_sign_chunk_10
  · exact zero_sign_chunk_11
  · exact zero_sign_chunk_12

theorem zero_scaled_signs (i : Fin 130) : zeroScaledSign i := by
  obtain ⟨b, j, rfl⟩ := signIndex_surjective i
  exact zero_all_chunks b j

theorem zero_signs : ∀ i : Fin 130,
    (rationalHorner powerCoefficients (zeroLeft i) < 0 ∧
      0 < rationalHorner powerCoefficients (zeroRight i)) ∨
    (rationalHorner powerCoefficients (zeroRight i) < 0 ∧
      0 < rationalHorner powerCoefficients (zeroLeft i)) := by
  intro i
  rcases zero_scaled_signs i with h | h
  · exact Or.inl ⟨by simpa using horner_lt_of_scaled (zeroLeft i) 0 (by simpa using h.1),
      by simpa using lt_horner_of_scaled (zeroRight i) 0 (by simpa using h.2)⟩
  · exact Or.inr ⟨by simpa using horner_lt_of_scaled (zeroRight i) 0 (by simpa using h.1),
      by simpa using lt_horner_of_scaled (zeroLeft i) 0 (by simpa using h.2)⟩

end CatalanMeasure.Refinement.Trimmed130
