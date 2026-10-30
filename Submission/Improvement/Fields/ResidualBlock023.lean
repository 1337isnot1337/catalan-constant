module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB023 : Block := ⟨-257698037760, 17179869184, 4, 3336800257277533469018172734161044816888528106758902079, [((-257698037760:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB023_blk : decide (PbV D_R.N trimmedRB023.cB trimmedRB023.HB
    (polyValsS D_R trimmedRB023.cB (5+65)) (5+trimmedRB023.L) (65-trimmedRB023.L) MGL_R ≤ trimmedRB023.BB) = true := by decide +kernel
theorem trimmedRB023_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-257698037760:ℚ)/(TT:ℚ)) (-1977518166305183783/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB023_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-257698037760:ℤ)
    (polyValsS D_R (-257698037760:ℤ) (5+4)) 5 = [138714325846255056412135149742466866258, 1103527219444545125381399143099372733325, 9973874288909109010480965424982100247521, 131244085412323896382184773324967106563290, 1858474185968311373967866708436260799145463] := by decide +kernel
theorem trimmedRB023_c0_aa : AL D_R.N (polyValsS D_R (-257698037760:ℤ) (5+4)) 5 4 = [398369412349325814475053292105125784393904995, 1375807703113752775546406478439744012239056229, 4820363713305932018953698359492511331786137262701, 86966286867844918769862247008372942773484474752891] := by decide +kernel
theorem trimmedRB023_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-257698037760:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -257698037760:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 3449250165614519629979892667488344524993427155 := by decide +kernel
theorem trimmedRB023_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 3336800257277533469018172734161044816888528106758902079 none trimmedResidualCap (-257698037760,17179869184) (-1977518166305183783/18446744073709551616:ℚ) [138714325846255056412135149742466866258, 1103527219444545125381399143099372733325, 9973874288909109010480965424982100247521, 131244085412323896382184773324967106563290, 1858474185968311373967866708436260799145463] [398369412349325814475053292105125784393904995, 1375807703113752775546406478439744012239056229, 4820363713305932018953698359492511331786137262701, 86966286867844918769862247008372942773484474752891] 3449250165614519629979892667488344524993427155 = true := by decide +kernel
theorem trimmedRB023_cells : ∀ c ∈ trimmedRB023.cells,
    |c.1 - trimmedRB023.cB| + c.2.1 ≤ trimmedRB023.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB023.L trimmedRB023.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB023, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 3336800257277533469018172734161044816888528106758902079
        trimmedResidualCap (-257698037760:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB023_c0_ev trimmedRB023_c0_fh trimmedRB023_c0_aa trimmedRB023_c0_mp trimmedRB023_c0_fin⟩
theorem trimmedRB023_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB023 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB023
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB023_blk trimmedRB023_cells
end CatalanMeasure.Improvement.Fields
