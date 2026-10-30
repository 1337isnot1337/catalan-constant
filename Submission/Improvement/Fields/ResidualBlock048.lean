module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB048 : Block := ⟨910533066752, 17179869184, 4, 392036709821880772575626856643347112129568778153449510143, [((910533066752:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB048_blk : decide (PbV D_R.N trimmedRB048.cB trimmedRB048.HB
    (polyValsS D_R trimmedRB048.cB (5+65)) (5+trimmedRB048.L) (65-trimmedRB048.L) MGL_R ≤ trimmedRB048.BB) = true := by decide +kernel
theorem trimmedRB048_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((910533066752:ℚ)/(TT:ℚ)) (-14295243366255390065/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB048_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (910533066752:ℤ)
    (polyValsS D_R (910533066752:ℤ) (5+4)) 5 = [-105121619348114657240357316436480002113, 1038243240259568377606755858207622177689, 9946551309857580882476701165001305119364, 183143862156587173515922452606473391029673, 5050275986420201788550539039969553406826001] := by decide +kernel
theorem trimmedRB048_c0_aa : AL D_R.N (polyValsS D_R (910533066752:ℤ) (5+4)) 5 4 = [47520729243029938087146152932685138624475163223, 1746874949564858206632656826096802136115362910619, 14416182966918434715956767836462220970823462977667, 11328102210740382080461599091634268773768538472008366] := by decide +kernel
theorem trimmedRB048_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((910533066752:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 910533066752:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 116578706769146797140463758771002788107811529684 := by decide +kernel
theorem trimmedRB048_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 392036709821880772575626856643347112129568778153449510143 none trimmedResidualCap (910533066752,17179869184) (-14295243366255390065/18446744073709551616:ℚ) [-105121619348114657240357316436480002113, 1038243240259568377606755858207622177689, 9946551309857580882476701165001305119364, 183143862156587173515922452606473391029673, 5050275986420201788550539039969553406826001] [47520729243029938087146152932685138624475163223, 1746874949564858206632656826096802136115362910619, 14416182966918434715956767836462220970823462977667, 11328102210740382080461599091634268773768538472008366] 116578706769146797140463758771002788107811529684 = true := by decide +kernel
theorem trimmedRB048_cells : ∀ c ∈ trimmedRB048.cells,
    |c.1 - trimmedRB048.cB| + c.2.1 ≤ trimmedRB048.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB048.L trimmedRB048.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB048, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 392036709821880772575626856643347112129568778153449510143
        trimmedResidualCap (910533066752:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB048_c0_ev trimmedRB048_c0_fh trimmedRB048_c0_aa trimmedRB048_c0_mp trimmedRB048_c0_fin⟩
theorem trimmedRB048_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB048 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB048
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB048_blk trimmedRB048_cells
end CatalanMeasure.Improvement.Fields
