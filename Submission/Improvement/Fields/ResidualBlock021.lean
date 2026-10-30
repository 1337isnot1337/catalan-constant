module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB021 : Block := ⟨-326417514496, 17179869184, 4, 611112025858842136463253600922431159780846547915234828, [((-326417514496:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB021_blk : decide (PbV D_R.N trimmedRB021.cB trimmedRB021.HB
    (polyValsS D_R trimmedRB021.cB (5+65)) (5+trimmedRB021.L) (65-trimmedRB021.L) MGL_R ≤ trimmedRB021.BB) = true := by decide +kernel
theorem trimmedRB021_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-326417514496:ℚ)/(TT:ℚ)) (-2348956214318801279/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB021_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-326417514496:ℤ)
    (polyValsS D_R (-326417514496:ℤ) (5+4)) 5 = [85045346875748993657746164931904491325, 666465539033038115849444024465528893569, 4821236100098048083892994401102548865548, 51520939256200310730233242972334304824680, 556458872363946088398262864772121517742807] := by decide +kernel
theorem trimmedRB021_c0_aa : AL D_R.N (polyValsS D_R (-326417514496:ℤ) (5+4)) 5 4 = [73608345442889974568402252612310138589328646, 2615657773631314384947014295542237641296681979, 1330170626677724037882334039014065156928841987632, 109082393169697170958398564507510005610225201067632] := by decide +kernel
theorem trimmedRB021_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-326417514496:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -326417514496:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 325676875766397226658115309469162375441714501 := by decide +kernel
theorem trimmedRB021_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 611112025858842136463253600922431159780846547915234828 none trimmedResidualCap (-326417514496,17179869184) (-2348956214318801279/18446744073709551616:ℚ) [85045346875748993657746164931904491325, 666465539033038115849444024465528893569, 4821236100098048083892994401102548865548, 51520939256200310730233242972334304824680, 556458872363946088398262864772121517742807] [73608345442889974568402252612310138589328646, 2615657773631314384947014295542237641296681979, 1330170626677724037882334039014065156928841987632, 109082393169697170958398564507510005610225201067632] 325676875766397226658115309469162375441714501 = true := by decide +kernel
theorem trimmedRB021_cells : ∀ c ∈ trimmedRB021.cells,
    |c.1 - trimmedRB021.cB| + c.2.1 ≤ trimmedRB021.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB021.L trimmedRB021.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB021, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 611112025858842136463253600922431159780846547915234828
        trimmedResidualCap (-326417514496:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB021_c0_ev trimmedRB021_c0_fh trimmedRB021_c0_aa trimmedRB021_c0_mp trimmedRB021_c0_fin⟩
theorem trimmedRB021_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB021 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB021
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB021_blk trimmedRB021_cells
end CatalanMeasure.Improvement.Fields
