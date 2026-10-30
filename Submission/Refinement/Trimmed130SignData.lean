module

public import Submission.Refinement.Trimmed130Geometry
public import Submission.Refinement.Trimmed130IntegerData

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

def signIndex (b : Fin 13) (j : Fin 10) : Fin 130 :=
  ⟨10 * b.val + j.val, by have := b.isLt; have := j.isLt; omega⟩

theorem signIndex_surjective (i : Fin 130) : ∃ b j, signIndex b j = i := by
  let b : Fin 13 := ⟨i.val / 10, by have := i.isLt; omega⟩
  let j : Fin 10 := ⟨i.val % 10, Nat.mod_lt _ (by decide)⟩
  refine ⟨b, j, Fin.ext ?_⟩
  have h := Nat.mod_add_div i.val 10
  dsimp [signIndex, b, j]
  omega

def branchScaledSign (i : Fin 130) : Prop :=
  (scaledValue (branchLeft i) < (-1) * scaledUnit (branchLeft i) ∧
    1 * scaledUnit (branchRight i) < scaledValue (branchRight i)) ∨
  (scaledValue (branchRight i) < (-1) * scaledUnit (branchRight i) ∧
    1 * scaledUnit (branchLeft i) < scaledValue (branchLeft i))

def zeroScaledSign (i : Fin 130) : Prop :=
  (scaledValue (zeroLeft i) < 0 ∧ 0 < scaledValue (zeroRight i)) ∨
  (scaledValue (zeroRight i) < 0 ∧ 0 < scaledValue (zeroLeft i))

instance (i : Fin 130) : Decidable (branchScaledSign i) := inferInstanceAs (Decidable (_ ∨ _))
instance (i : Fin 130) : Decidable (zeroScaledSign i) := inferInstanceAs (Decidable (_ ∨ _))

end CatalanMeasure.Refinement.Trimmed130
