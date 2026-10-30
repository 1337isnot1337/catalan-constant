module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB051 : Block := ⟨1013612281856, 17179869184, 4, 857497656018940464936484582566595852456091485931781014342884, [((1013612281856:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB051_blk : decide (PbV D_R.N trimmedRB051.cB trimmedRB051.HB
    (polyValsS D_R trimmedRB051.cB (5+65)) (5+trimmedRB051.L) (65-trimmedRB051.L) MGL_R ≤ trimmedRB051.BB) = true := by decide +kernel
theorem trimmedRB051_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((1013612281856:ℚ)/(TT:ℚ)) (-1806618817829791149/2305843009213693952:ℚ) = true := by decide +kernel
theorem trimmedRB051_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (1013612281856:ℤ)
    (polyValsS D_R (1013612281856:ℤ) (5+4)) 5 = [88349604346973406624697463317587685470, 4304446344411183951989441185211733908935, 104640208678079595436080241387513088071847, 3927164247815864598131008511436835115223744, 109687118548775826514742051059057293379348662] := by decide +kernel
theorem trimmedRB051_c0_aa : AL D_R.N (polyValsS D_R (1013612281856:ℤ) (5+4)) 5 4 = [5017204102828944852444645499992476206814762535688, 362066511970508779365696204827384729351511374329398, 28799329265843488989854826387468383449051771338054194, 5603933625391507511950081065233141962469516162221708852] := by decide +kernel
theorem trimmedRB051_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((1013612281856:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 1013612281856:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 26657917558476394151038915617062972909847966434727 := by decide +kernel
theorem trimmedRB051_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 857497656018940464936484582566595852456091485931781014342884 none trimmedResidualCap (1013612281856,17179869184) (-1806618817829791149/2305843009213693952:ℚ) [88349604346973406624697463317587685470, 4304446344411183951989441185211733908935, 104640208678079595436080241387513088071847, 3927164247815864598131008511436835115223744, 109687118548775826514742051059057293379348662] [5017204102828944852444645499992476206814762535688, 362066511970508779365696204827384729351511374329398, 28799329265843488989854826387468383449051771338054194, 5603933625391507511950081065233141962469516162221708852] 26657917558476394151038915617062972909847966434727 = true := by decide +kernel
theorem trimmedRB051_cells : ∀ c ∈ trimmedRB051.cells,
    |c.1 - trimmedRB051.cB| + c.2.1 ≤ trimmedRB051.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB051.L trimmedRB051.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB051, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 857497656018940464936484582566595852456091485931781014342884
        trimmedResidualCap (1013612281856:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB051_c0_ev trimmedRB051_c0_fh trimmedRB051_c0_aa trimmedRB051_c0_mp trimmedRB051_c0_fin⟩
theorem trimmedRB051_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB051 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB051
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB051_blk trimmedRB051_cells
end CatalanMeasure.Improvement.Fields
