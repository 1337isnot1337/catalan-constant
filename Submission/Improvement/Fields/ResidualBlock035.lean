module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB035 : Block := ⟨463856467968, 17179869184, 4, 191923405365242364142990658116090164694676468498671816, [((463856467968:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB035_blk : decide (PbV D_R.N trimmedRB035.cB trimmedRB035.HB
    (polyValsS D_R trimmedRB035.cB (5+65)) (5+trimmedRB035.L) (65-trimmedRB035.L) MGL_R ≤ trimmedRB035.BB) = true := by decide +kernel
theorem trimmedRB035_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((463856467968:ℚ)/(TT:ℚ)) (-4737209272830119911/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB035_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (463856467968:ℤ)
    (polyValsS D_R (463856467968:ℤ) (5+4)) 5 = [-304424606200786710317169679861539052667, 449313787781587657712976980322018575697, -1217562307305142792198360692514152146209, 13336106780290546132932023489525946992972, -170381343954687678870922340273589252110535] := by decide +kernel
theorem trimmedRB035_c0_aa : AL D_R.N (polyValsS D_R (463856467968:ℤ) (5+4)) 5 4 = [35663341561883573944130583788691594179248761, 2064883574320628638737368705721086367880337198, 34123101500588424463639268406313728609030252427, 90421756269064692663215482895639216245623505808489] := by decide +kernel
theorem trimmedRB035_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((463856467968:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 463856467968:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 73593752764477968608713460791208571992480893 := by decide +kernel
theorem trimmedRB035_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 191923405365242364142990658116090164694676468498671816 none trimmedResidualCap (463856467968,17179869184) (-4737209272830119911/9223372036854775808:ℚ) [-304424606200786710317169679861539052667, 449313787781587657712976980322018575697, -1217562307305142792198360692514152146209, 13336106780290546132932023489525946992972, -170381343954687678870922340273589252110535] [35663341561883573944130583788691594179248761, 2064883574320628638737368705721086367880337198, 34123101500588424463639268406313728609030252427, 90421756269064692663215482895639216245623505808489] 73593752764477968608713460791208571992480893 = true := by decide +kernel
theorem trimmedRB035_cells : ∀ c ∈ trimmedRB035.cells,
    |c.1 - trimmedRB035.cB| + c.2.1 ≤ trimmedRB035.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB035.L trimmedRB035.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB035, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 191923405365242364142990658116090164694676468498671816
        trimmedResidualCap (463856467968:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB035_c0_ev trimmedRB035_c0_fh trimmedRB035_c0_aa trimmedRB035_c0_mp trimmedRB035_c0_fin⟩
theorem trimmedRB035_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB035 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB035
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB035_blk trimmedRB035_cells
end CatalanMeasure.Improvement.Fields
