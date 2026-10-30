module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB009 : Block := ⟨-738734374912, 17179869184, 4, 2439000805519686284267999317890102156730046906353038679, [((-738734374912:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB009_blk : decide (PbV D_R.N trimmedRB009.cB trimmedRB009.HB
    (polyValsS D_R trimmedRB009.cB (5+65)) (5+trimmedRB009.L) (65-trimmedRB009.L) MGL_R ≤ trimmedRB009.BB) = true := by decide +kernel
theorem trimmedRB009_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-738734374912:ℚ)/(TT:ℚ)) (-2676067256135725403/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB009_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-738734374912:ℤ)
    (polyValsS D_R (-738734374912:ℤ) (5+4)) 5 = [-26967635440581935817653548730180797877, 183311891865760067600198528453897673841, -125403467852477646926429188367308551720, 5392684289547764852886202734050064364831, -221954311241257890049725125554032798406744] := by decide +kernel
theorem trimmedRB009_c0_aa : AL D_R.N (polyValsS D_R (-738734374912:ℤ) (5+4)) 5 4 = [3108172469999711955025337137416738274159313, 10453416251669239320722334213708708389459970252, 840507485467795961182231887672461465233500089253, 565949272194053667876427311027901927370083201010880] := by decide +kernel
theorem trimmedRB009_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-738734374912:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -738734374912:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 36707755753621702906911545232442761872026847 := by decide +kernel
theorem trimmedRB009_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 2439000805519686284267999317890102156730046906353038679 none trimmedResidualCap (-738734374912,17179869184) (-2676067256135725403/18446744073709551616:ℚ) [-26967635440581935817653548730180797877, 183311891865760067600198528453897673841, -125403467852477646926429188367308551720, 5392684289547764852886202734050064364831, -221954311241257890049725125554032798406744] [3108172469999711955025337137416738274159313, 10453416251669239320722334213708708389459970252, 840507485467795961182231887672461465233500089253, 565949272194053667876427311027901927370083201010880] 36707755753621702906911545232442761872026847 = true := by decide +kernel
theorem trimmedRB009_cells : ∀ c ∈ trimmedRB009.cells,
    |c.1 - trimmedRB009.cB| + c.2.1 ≤ trimmedRB009.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB009.L trimmedRB009.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB009, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 2439000805519686284267999317890102156730046906353038679
        trimmedResidualCap (-738734374912:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB009_c0_ev trimmedRB009_c0_fh trimmedRB009_c0_aa trimmedRB009_c0_mp trimmedRB009_c0_fin⟩
theorem trimmedRB009_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB009 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB009
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB009_blk trimmedRB009_cells
end CatalanMeasure.Improvement.Fields
