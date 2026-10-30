module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB002 : Block := ⟨-979252543488, 17179869184, 4, 8725810000148030842769832625981894706756781297883128824164, [((-979252543488:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB002_blk : decide (PbV D_R.N trimmedRB002.cB trimmedRB002.HB
    (polyValsS D_R trimmedRB002.cB (5+65)) (5+trimmedRB002.L) (65-trimmedRB002.L) MGL_R ≤ trimmedRB002.BB) = true := by decide +kernel
theorem trimmedRB002_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-979252543488:ℚ)/(TT:ℚ)) (-2068902488793692365/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB002_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-979252543488:ℤ)
    (polyValsS D_R (-979252543488:ℤ) (5+4)) 5 = [-85069399286737557137429624567673623010, 494776943585162266545920764882150387962, -5359707581233856597246072438196913094775, 98292703980187959491901035394785967149548, 1986306969000919407759600027534302180041397] := by decide +kernel
theorem trimmedRB002_c0_aa : AL D_R.N (polyValsS D_R (-979252543488:ℤ) (5+4)) 5 4 = [13126376835393814559327747934420746389556272691, 1441502336074293218734869007830151555710560735084, 110803763394000892980912505985365856724832965374378, 118951508469097632717804029640064942655352435706314417] := by decide +kernel
theorem trimmedRB002_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-979252543488:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -979252543488:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 45942001047040097992444169243536416415677914527 := by decide +kernel
theorem trimmedRB002_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 8725810000148030842769832625981894706756781297883128824164 none trimmedResidualCap (-979252543488,17179869184) (-2068902488793692365/18446744073709551616:ℚ) [-85069399286737557137429624567673623010, 494776943585162266545920764882150387962, -5359707581233856597246072438196913094775, 98292703980187959491901035394785967149548, 1986306969000919407759600027534302180041397] [13126376835393814559327747934420746389556272691, 1441502336074293218734869007830151555710560735084, 110803763394000892980912505985365856724832965374378, 118951508469097632717804029640064942655352435706314417] 45942001047040097992444169243536416415677914527 = true := by decide +kernel
theorem trimmedRB002_cells : ∀ c ∈ trimmedRB002.cells,
    |c.1 - trimmedRB002.cB| + c.2.1 ≤ trimmedRB002.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB002.L trimmedRB002.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB002, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 8725810000148030842769832625981894706756781297883128824164
        trimmedResidualCap (-979252543488:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB002_c0_ev trimmedRB002_c0_fh trimmedRB002_c0_aa trimmedRB002_c0_mp trimmedRB002_c0_fin⟩
theorem trimmedRB002_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB002 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB002
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB002_blk trimmedRB002_cells
end CatalanMeasure.Improvement.Fields
