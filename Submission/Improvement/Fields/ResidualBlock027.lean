module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB027 : Block := ⟨188978561024, 17179869184, 4, 112258935323983275411154438129394625422386505859551150669, [((188978561024:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB027_blk : decide (PbV D_R.N trimmedRB027.cB trimmedRB027.HB
    (polyValsS D_R trimmedRB027.cB (5+65)) (5+trimmedRB027.L) (65-trimmedRB027.L) MGL_R ≤ trimmedRB027.BB) = true := by decide +kernel
theorem trimmedRB027_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((188978561024:ℚ)/(TT:ℚ)) (-262299759440016917/1152921504606846976:ℚ) = true := by decide +kernel
theorem trimmedRB027_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (188978561024:ℤ)
    (polyValsS D_R (188978561024:ℤ) (5+4)) 5 = [-535057311611640745935903226940237011902, 2170137729912463005240888549431047200854, -25279101046037208736192961603803158277518, 435946913913551458372631204286495226536078, 25522752241358528983675972911589200639757614] := by decide +kernel
theorem trimmedRB027_c0_aa : AL D_R.N (polyValsS D_R (188978561024:ℤ) (5+4)) 5 4 = [16339591427283883558870856560488912928765565646, 4555555050874041566244264738169388083932303898250, 955572823493327402624305767770842731090617926843839, 106926060926256164679589461948893051812338481257750018] := by decide +kernel
theorem trimmedRB027_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((188978561024:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 188978561024:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 4813296240382844155708959306609737187845107061843 := by decide +kernel
theorem trimmedRB027_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 112258935323983275411154438129394625422386505859551150669 none trimmedResidualCap (188978561024,17179869184) (-262299759440016917/1152921504606846976:ℚ) [-535057311611640745935903226940237011902, 2170137729912463005240888549431047200854, -25279101046037208736192961603803158277518, 435946913913551458372631204286495226536078, 25522752241358528983675972911589200639757614] [16339591427283883558870856560488912928765565646, 4555555050874041566244264738169388083932303898250, 955572823493327402624305767770842731090617926843839, 106926060926256164679589461948893051812338481257750018] 4813296240382844155708959306609737187845107061843 = true := by decide +kernel
theorem trimmedRB027_cells : ∀ c ∈ trimmedRB027.cells,
    |c.1 - trimmedRB027.cB| + c.2.1 ≤ trimmedRB027.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB027.L trimmedRB027.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB027, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 112258935323983275411154438129394625422386505859551150669
        trimmedResidualCap (188978561024:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB027_c0_ev trimmedRB027_c0_fh trimmedRB027_c0_aa trimmedRB027_c0_mp trimmedRB027_c0_fin⟩
theorem trimmedRB027_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB027 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB027
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB027_blk trimmedRB027_cells
end CatalanMeasure.Improvement.Fields
