module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB028 : Block := ⟨223338299392, 17179869184, 4, 13969799758971364969710184656600158042974382357671502835, [((223338299392:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB028_blk : decide (PbV D_R.N trimmedRB028.cB trimmedRB028.HB
    (polyValsS D_R trimmedRB028.cB (5+65)) (5+trimmedRB028.L) (65-trimmedRB028.L) MGL_R ≤ trimmedRB028.BB) = true := by decide +kernel
theorem trimmedRB028_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((223338299392:ℚ)/(TT:ℚ)) (-2525933663269967581/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB028_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (223338299392:ℤ)
    (polyValsS D_R (223338299392:ℤ) (5+4)) 5 = [-477591441451287250450926664997008864822, 1559792577452244448165113889043389486214, -15035642485731091241402808540939709682354, 229641476009031984183234112301220328480394, -5844884678571164150829491846187845910293443] := by decide +kernel
theorem trimmedRB028_c0_aa : AL D_R.N (polyValsS D_R (223338299392:ℤ) (5+4)) 5 4 = [1960898962748441397641013072032402552760275385, 186410966166064189048416807195383905125166492149, 18172539283063417345361001590386163615914368010365, 2362032769240943455178634030602085728419113612366312] := by decide +kernel
theorem trimmedRB028_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((223338299392:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 223338299392:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 20120636664909438149917863094684527933132530851 := by decide +kernel
theorem trimmedRB028_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 13969799758971364969710184656600158042974382357671502835 none trimmedResidualCap (223338299392,17179869184) (-2525933663269967581/9223372036854775808:ℚ) [-477591441451287250450926664997008864822, 1559792577452244448165113889043389486214, -15035642485731091241402808540939709682354, 229641476009031984183234112301220328480394, -5844884678571164150829491846187845910293443] [1960898962748441397641013072032402552760275385, 186410966166064189048416807195383905125166492149, 18172539283063417345361001590386163615914368010365, 2362032769240943455178634030602085728419113612366312] 20120636664909438149917863094684527933132530851 = true := by decide +kernel
theorem trimmedRB028_cells : ∀ c ∈ trimmedRB028.cells,
    |c.1 - trimmedRB028.cB| + c.2.1 ≤ trimmedRB028.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB028.L trimmedRB028.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB028, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 13969799758971364969710184656600158042974382357671502835
        trimmedResidualCap (223338299392:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB028_c0_ev trimmedRB028_c0_fh trimmedRB028_c0_aa trimmedRB028_c0_mp trimmedRB028_c0_fin⟩
theorem trimmedRB028_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB028 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB028
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB028_blk trimmedRB028_cells
end CatalanMeasure.Improvement.Fields
