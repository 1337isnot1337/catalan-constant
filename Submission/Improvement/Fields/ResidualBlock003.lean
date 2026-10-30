module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB003 : Block := ⟨-944892805120, 17179869184, 4, 1015650786604077726158352341978295739267236022672606330892, [((-944892805120:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB003_blk : decide (PbV D_R.N trimmedRB003.cB trimmedRB003.HB
    (polyValsS D_R trimmedRB003.cB (5+65)) (5+trimmedRB003.L) (65-trimmedRB003.L) MGL_R ≤ trimmedRB003.BB) = true := by decide +kernel
theorem trimmedRB003_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-944892805120:ℚ)/(TT:ℚ)) (-1100592775666414065/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB003_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-944892805120:ℤ)
    (polyValsS D_R (-944892805120:ℤ) (5+4)) 5 = [-71745847509159775334259897903916357955, 370273731801803495048859043393532246744, -2927356275455427412579077234594041845722, 46165482039104809099416918370874808960461, -3881556661474199481264705280604826616428584] := by decide +kernel
theorem trimmedRB003_c0_aa : AL D_R.N (polyValsS D_R (-944892805120:ℤ) (5+4)) 5 4 = [3149483455694979429563113084933352696484234433, 145750735925834398184501483849651380500578351850, 65081665331884208022822383212841451772600809988908, 22220105026642069098267031106588488367229347101239868] := by decide +kernel
theorem trimmedRB003_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-944892805120:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -944892805120:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 8359593905328719753465710398980581995073536761 := by decide +kernel
theorem trimmedRB003_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 1015650786604077726158352341978295739267236022672606330892 none trimmedResidualCap (-944892805120,17179869184) (-1100592775666414065/9223372036854775808:ℚ) [-71745847509159775334259897903916357955, 370273731801803495048859043393532246744, -2927356275455427412579077234594041845722, 46165482039104809099416918370874808960461, -3881556661474199481264705280604826616428584] [3149483455694979429563113084933352696484234433, 145750735925834398184501483849651380500578351850, 65081665331884208022822383212841451772600809988908, 22220105026642069098267031106588488367229347101239868] 8359593905328719753465710398980581995073536761 = true := by decide +kernel
theorem trimmedRB003_cells : ∀ c ∈ trimmedRB003.cells,
    |c.1 - trimmedRB003.cB| + c.2.1 ≤ trimmedRB003.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB003.L trimmedRB003.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB003, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 1015650786604077726158352341978295739267236022672606330892
        trimmedResidualCap (-944892805120:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB003_c0_ev trimmedRB003_c0_fh trimmedRB003_c0_aa trimmedRB003_c0_mp trimmedRB003_c0_fin⟩
theorem trimmedRB003_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB003 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB003
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB003_blk trimmedRB003_cells
end CatalanMeasure.Improvement.Fields
