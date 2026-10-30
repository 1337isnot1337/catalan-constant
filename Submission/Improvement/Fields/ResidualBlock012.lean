module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB012 : Block := ⟨-635655159808, 17179869184, 4, 827469387558068951616483206711232863567760075237982948, [((-635655159808:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB012_blk : decide (PbV D_R.N trimmedRB012.cB trimmedRB012.HB
    (polyValsS D_R trimmedRB012.cB (5+65)) (5+trimmedRB012.L) (65-trimmedRB012.L) MGL_R ≤ trimmedRB012.BB) = true := by decide +kernel
theorem trimmedRB012_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-635655159808:ℚ)/(TT:ℚ)) (-2769589492734294777/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB012_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-635655159808:ℤ)
    (polyValsS D_R (-635655159808:ℤ) (5+4)) 5 = [-9706264769311366029129943945224802792, 191648069049603537944177216738004206267, 307586091469889212506884337308063339548, 4353512115646861340499547050309032957380, -74106077847231826084289478712513307127620] := by decide +kernel
theorem trimmedRB012_c0_aa : AL D_R.N (polyValsS D_R (-635655159808:ℤ) (5+4)) 5 4 = [25189497513377706366141374587061050959752686, 3510469208530076120417455063392798946978351043, 957001709437378971487739383510804888611464804655, 139944142796580087696276430160987764636563426024282] := by decide +kernel
theorem trimmedRB012_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-635655159808:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -635655159808:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 9596745017769038798745518724737687313832366 := by decide +kernel
theorem trimmedRB012_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 827469387558068951616483206711232863567760075237982948 none trimmedResidualCap (-635655159808,17179869184) (-2769589492734294777/18446744073709551616:ℚ) [-9706264769311366029129943945224802792, 191648069049603537944177216738004206267, 307586091469889212506884337308063339548, 4353512115646861340499547050309032957380, -74106077847231826084289478712513307127620] [25189497513377706366141374587061050959752686, 3510469208530076120417455063392798946978351043, 957001709437378971487739383510804888611464804655, 139944142796580087696276430160987764636563426024282] 9596745017769038798745518724737687313832366 = true := by decide +kernel
theorem trimmedRB012_cells : ∀ c ∈ trimmedRB012.cells,
    |c.1 - trimmedRB012.cB| + c.2.1 ≤ trimmedRB012.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB012.L trimmedRB012.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB012, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 827469387558068951616483206711232863567760075237982948
        trimmedResidualCap (-635655159808:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB012_c0_ev trimmedRB012_c0_fh trimmedRB012_c0_aa trimmedRB012_c0_mp trimmedRB012_c0_fin⟩
theorem trimmedRB012_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB012 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB012
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB012_blk trimmedRB012_cells
end CatalanMeasure.Improvement.Fields
