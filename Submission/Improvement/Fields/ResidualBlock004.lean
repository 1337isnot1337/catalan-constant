module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB004 : Block := ⟨-910533066752, 17179869184, 4, 204721668763253358372631364625935980150575458607901737010, [((-910533066752:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB004_blk : decide (PbV D_R.N trimmedRB004.cB trimmedRB004.HB
    (polyValsS D_R trimmedRB004.cB (5+65)) (5+trimmedRB004.L) (65-trimmedRB004.L) MGL_R ≤ trimmedRB004.BB) = true := by decide +kernel
theorem trimmedRB004_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-910533066752:ℚ)/(TT:ℚ)) (-1156823631235539255/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB004_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-910533066752:ℤ)
    (polyValsS D_R (-910533066752:ℤ) (5+4)) 5 = [-61401826964721790129209343299574089294, 297615231364872546001756937891425689648, -1826796030227439203954830316018136022788, 29277916235352082131130804683044399653595, 673294967085740662344801236341247512057371] := by decide +kernel
theorem trimmedRB004_c0_aa : AL D_R.N (polyValsS D_R (-910533066752:ℤ) (5+4)) 5 4 = [499422469174390539811066714447464737581607761, 116255632865417791689205586315496054745827100427, 31882735852812636167528271774851228747077924396528, 6088651509892663817936466068173733513548422550905818] := by decide +kernel
theorem trimmedRB004_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-910533066752:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -910533066752:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 2223120739431583198643593980207831187922797433 := by decide +kernel
theorem trimmedRB004_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 204721668763253358372631364625935980150575458607901737010 none trimmedResidualCap (-910533066752,17179869184) (-1156823631235539255/9223372036854775808:ℚ) [-61401826964721790129209343299574089294, 297615231364872546001756937891425689648, -1826796030227439203954830316018136022788, 29277916235352082131130804683044399653595, 673294967085740662344801236341247512057371] [499422469174390539811066714447464737581607761, 116255632865417791689205586315496054745827100427, 31882735852812636167528271774851228747077924396528, 6088651509892663817936466068173733513548422550905818] 2223120739431583198643593980207831187922797433 = true := by decide +kernel
theorem trimmedRB004_cells : ∀ c ∈ trimmedRB004.cells,
    |c.1 - trimmedRB004.cB| + c.2.1 ≤ trimmedRB004.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB004.L trimmedRB004.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB004, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 204721668763253358372631364625935980150575458607901737010
        trimmedResidualCap (-910533066752:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB004_c0_ev trimmedRB004_c0_fh trimmedRB004_c0_aa trimmedRB004_c0_mp trimmedRB004_c0_fin⟩
theorem trimmedRB004_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB004 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB004
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB004_blk trimmedRB004_cells
end CatalanMeasure.Improvement.Fields
