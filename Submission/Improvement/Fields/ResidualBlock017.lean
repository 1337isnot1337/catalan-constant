module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB017 : Block := ⟨-463856467968, 17179869184, 4, 335640501169042115728922328001388118110229080344606221, [((-463856467968:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB017_blk : decide (PbV D_R.N trimmedRB017.cB trimmedRB017.HB
    (polyValsS D_R trimmedRB017.cB (5+65)) (5+trimmedRB017.L) (65-trimmedRB017.L) MGL_R ≤ trimmedRB017.BB) = true := by decide +kernel
theorem trimmedRB017_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-463856467968:ℚ)/(TT:ℚ)) (-1353466574170566283/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB017_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-463856467968:ℤ)
    (polyValsS D_R (-463856467968:ℤ) (5+4)) 5 = [27695401922950406306008579614495117341, 317419724328221938319592394484507801839, 1509522143468090162765027572226362399537, 12807315956897448627484053014066409454004, 7258392259726444210492899021715004377278] := by decide +kernel
theorem trimmedRB017_c0_aa : AL D_R.N (polyValsS D_R (-463856467968:ℤ) (5+4)) 5 4 = [4426987728579169572297999152918658884591916, 3913080201265894848873595902957166979459222453, 215310876858968301941795796512775554735074984768, 144205279800503955091018008116650880803335332744480] := by decide +kernel
theorem trimmedRB017_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-463856467968:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -463856467968:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 19655852900788422277470640843927109700612061 := by decide +kernel
theorem trimmedRB017_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 335640501169042115728922328001388118110229080344606221 none trimmedResidualCap (-463856467968,17179869184) (-1353466574170566283/9223372036854775808:ℚ) [27695401922950406306008579614495117341, 317419724328221938319592394484507801839, 1509522143468090162765027572226362399537, 12807315956897448627484053014066409454004, 7258392259726444210492899021715004377278] [4426987728579169572297999152918658884591916, 3913080201265894848873595902957166979459222453, 215310876858968301941795796512775554735074984768, 144205279800503955091018008116650880803335332744480] 19655852900788422277470640843927109700612061 = true := by decide +kernel
theorem trimmedRB017_cells : ∀ c ∈ trimmedRB017.cells,
    |c.1 - trimmedRB017.cB| + c.2.1 ≤ trimmedRB017.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB017.L trimmedRB017.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB017, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 335640501169042115728922328001388118110229080344606221
        trimmedResidualCap (-463856467968:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB017_c0_ev trimmedRB017_c0_fh trimmedRB017_c0_aa trimmedRB017_c0_mp trimmedRB017_c0_fin⟩
theorem trimmedRB017_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB017 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB017
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB017_blk trimmedRB017_cells
end CatalanMeasure.Improvement.Fields
