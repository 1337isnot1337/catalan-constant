module

public import Submission.Refinement.Trimmed130SignData

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CatalanMeasure.Refinement.Trimmed130

theorem zero_sign_chunk_1 : ∀ j : Fin 10,
    zeroScaledSign (signIndex ⟨1, by decide⟩ j) := by decide +kernel

end CatalanMeasure.Refinement.Trimmed130
