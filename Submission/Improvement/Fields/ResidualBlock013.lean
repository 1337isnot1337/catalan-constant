module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB013 : Block := ⟨-601295421440, 17179869184, 4, 611565523157658918981775181405056469495492932173630963, [((-601295421440:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB013_blk : decide (PbV D_R.N trimmedRB013.cB trimmedRB013.HB
    (polyValsS D_R trimmedRB013.cB (5+65)) (5+trimmedRB013.L) (65-trimmedRB013.L) MGL_R ≤ trimmedRB013.BB) = true := by decide +kernel
theorem trimmedRB013_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-601295421440:ℚ)/(TT:ℚ)) (-1390432503670807621/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB013_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-601295421440:ℤ)
    (polyValsS D_R (-601295421440:ℤ) (5+4)) 5 = [-3543180202729598004397268048408530236, 203644194115255913841772882468739598851, 467224215862898180740505208258955813476, 4980277581101801528472740473801330284885, -42072805670499441163519898073977876719550] := by decide +kernel
theorem trimmedRB013_c0_aa : AL D_R.N (polyValsS D_R (-601295421440:ℤ) (5+4)) 5 4 = [22487868358616227584133620532271285004269265, 2616341725446129109152634599767993146414167326, 852937467329798484612760163847062058572594268850, 101039347205366635539262137490730076165683603434397] := by decide +kernel
theorem trimmedRB013_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-601295421440:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -601295421440:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 7828072304795368512602255997557870987326006 := by decide +kernel
theorem trimmedRB013_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 611565523157658918981775181405056469495492932173630963 none trimmedResidualCap (-601295421440,17179869184) (-1390432503670807621/9223372036854775808:ℚ) [-3543180202729598004397268048408530236, 203644194115255913841772882468739598851, 467224215862898180740505208258955813476, 4980277581101801528472740473801330284885, -42072805670499441163519898073977876719550] [22487868358616227584133620532271285004269265, 2616341725446129109152634599767993146414167326, 852937467329798484612760163847062058572594268850, 101039347205366635539262137490730076165683603434397] 7828072304795368512602255997557870987326006 = true := by decide +kernel
theorem trimmedRB013_cells : ∀ c ∈ trimmedRB013.cells,
    |c.1 - trimmedRB013.cB| + c.2.1 ≤ trimmedRB013.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB013.L trimmedRB013.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB013, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 611565523157658918981775181405056469495492932173630963
        trimmedResidualCap (-601295421440:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB013_c0_ev trimmedRB013_c0_fh trimmedRB013_c0_aa trimmedRB013_c0_mp trimmedRB013_c0_fin⟩
theorem trimmedRB013_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB013 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB013
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB013_blk trimmedRB013_cells
end CatalanMeasure.Improvement.Fields
