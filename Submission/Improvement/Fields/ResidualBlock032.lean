module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB032 : Block := ⟨360777252864, 17179869184, 4, 368793280137402662255053708267645975635070966646018222, [((360777252864:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB032_blk : decide (PbV D_R.N trimmedRB032.cB trimmedRB032.HB
    (polyValsS D_R trimmedRB032.cB (5+65)) (5+trimmedRB032.L) (65-trimmedRB032.L) MGL_R ≤ trimmedRB032.BB) = true := by decide +kernel
theorem trimmedRB032_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((360777252864:ℚ)/(TT:ℚ)) (-7808391816550336111/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB032_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (360777252864:ℤ)
    (polyValsS D_R (360777252864:ℤ) (5+4)) 5 = [-354191326341172428686556115668496554375, 643165494100873308043165461228506841910, -3227986909387935608502365411736608788567, 33801462484444081599231680562239099819986, -491429114596309889120943701752710314885270] := by decide +kernel
theorem trimmedRB032_c0_aa : AL D_R.N (polyValsS D_R (360777252864:ℤ) (5+4)) 5 4 = [14375424909678813757560069907550234690606938, 3270712065649952020957218490408204178499619930, 479321968442294451359533377504452805649917844699, 103831059675975837753121121534840902255206093360238] := by decide +kernel
theorem trimmedRB032_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((360777252864:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 360777252864:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 154081014812221918692716378050842997252172623 := by decide +kernel
theorem trimmedRB032_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 368793280137402662255053708267645975635070966646018222 none trimmedResidualCap (360777252864,17179869184) (-7808391816550336111/18446744073709551616:ℚ) [-354191326341172428686556115668496554375, 643165494100873308043165461228506841910, -3227986909387935608502365411736608788567, 33801462484444081599231680562239099819986, -491429114596309889120943701752710314885270] [14375424909678813757560069907550234690606938, 3270712065649952020957218490408204178499619930, 479321968442294451359533377504452805649917844699, 103831059675975837753121121534840902255206093360238] 154081014812221918692716378050842997252172623 = true := by decide +kernel
theorem trimmedRB032_cells : ∀ c ∈ trimmedRB032.cells,
    |c.1 - trimmedRB032.cB| + c.2.1 ≤ trimmedRB032.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB032.L trimmedRB032.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB032, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 368793280137402662255053708267645975635070966646018222
        trimmedResidualCap (360777252864:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB032_c0_ev trimmedRB032_c0_fh trimmedRB032_c0_aa trimmedRB032_c0_mp trimmedRB032_c0_fin⟩
theorem trimmedRB032_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB032 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB032
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB032_blk trimmedRB032_cells
end CatalanMeasure.Improvement.Fields
