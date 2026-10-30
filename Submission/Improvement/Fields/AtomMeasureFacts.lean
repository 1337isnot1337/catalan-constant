module

public import Submission.CatalanMeasure.GenD.Analytic.AtomBase
public import Submission.CatalanMeasure.Parametric.MarkedAtomAlmostEverywhere

@[expose] public section

/-! Two elementary determinant and measure facts used by the generic weighted
atom argument.  These are the proofs from the legacy Lemma6 module, isolated
from its unrelated fixed-design numerical certificates. -/

namespace CatalanMeasure.GenD.Analytic

open OAI.InternalCatalan

theorem atom_abs_det_submatrix_equiv {k l : ℕ}
    (M : Matrix (Fin l) (Fin l) ℝ) (g e : Fin k ≃ Fin l) :
    |(M.submatrix g e).det| = |M.det| := by
  have h : M.submatrix g e = (M.submatrix id (g.symm.trans e)).submatrix g g := by
    ext r c
    simp
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_permute', abs_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (g.symm.trans e)) with hs | hs <;> simp [hs]

theorem atom_pairMeasure_real_univ (p : ℕ) :
    (CatalanMeasure.pairMeasure realPlaceMeasure
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) p).real Set.univ = 2 ^ p := by
  unfold CatalanMeasure.pairMeasure
  rw [MeasureTheory.measureReal_def, ← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod,
    MeasureTheory.Measure.pi_univ, MeasureTheory.Measure.pi_univ]
  simp [realPlaceMeasure_univ, Real.volume_Ioo]

end CatalanMeasure.GenD.Analytic

#print axioms CatalanMeasure.GenD.Analytic.atom_abs_det_submatrix_equiv
#print axioms CatalanMeasure.GenD.Analytic.atom_pairMeasure_real_univ
