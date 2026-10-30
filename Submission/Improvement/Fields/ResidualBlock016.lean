module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB016 : Block := ⟨-498216206336, 17179869184, 4, 399019267593853715420738897210454520069064992881798795, [((-498216206336:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB016_blk : decide (PbV D_R.N trimmedRB016.cB trimmedRB016.HB
    (polyValsS D_R trimmedRB016.cB (5+65)) (5+trimmedRB016.L) (65-trimmedRB016.L) MGL_R ≤ trimmedRB016.BB) = true := by decide +kernel
theorem trimmedRB016_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-498216206336:ℚ)/(TT:ℚ)) (-1372919061368807391/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB016_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-498216206336:ℤ)
    (polyValsS D_R (-498216206336:ℤ) (5+4)) 5 = [18450054160620405434280467486706995982, 276148519533152485515527491216132955309, 1153024467283083420992476136931013503733, 9664841641249253154569171409249605014806, -11233995615168534950595488590803626407322] := by decide +kernel
theorem trimmedRB016_c0_aa : AL D_R.N (polyValsS D_R (-498216206336:ℤ) (5+4)) 5 4 = [11023839855567946620035077907315553938577551, 3356189605349287347134353211470376028788491143, 430372359336756941898657746039184036597868391621, 125080769566995593072577088311644591316201737884700] := by decide +kernel
theorem trimmedRB016_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-498216206336:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -498216206336:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 12524756327947841484743208416503258804336470 := by decide +kernel
theorem trimmedRB016_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 399019267593853715420738897210454520069064992881798795 none trimmedResidualCap (-498216206336,17179869184) (-1372919061368807391/9223372036854775808:ℚ) [18450054160620405434280467486706995982, 276148519533152485515527491216132955309, 1153024467283083420992476136931013503733, 9664841641249253154569171409249605014806, -11233995615168534950595488590803626407322] [11023839855567946620035077907315553938577551, 3356189605349287347134353211470376028788491143, 430372359336756941898657746039184036597868391621, 125080769566995593072577088311644591316201737884700] 12524756327947841484743208416503258804336470 = true := by decide +kernel
theorem trimmedRB016_cells : ∀ c ∈ trimmedRB016.cells,
    |c.1 - trimmedRB016.cB| + c.2.1 ≤ trimmedRB016.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB016.L trimmedRB016.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB016, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 399019267593853715420738897210454520069064992881798795
        trimmedResidualCap (-498216206336:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB016_c0_ev trimmedRB016_c0_fh trimmedRB016_c0_aa trimmedRB016_c0_mp trimmedRB016_c0_fin⟩
theorem trimmedRB016_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB016 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB016
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB016_blk trimmedRB016_cells
end CatalanMeasure.Improvement.Fields
