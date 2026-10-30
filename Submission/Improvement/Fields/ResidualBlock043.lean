module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB043 : Block := ⟨738734374912, 17179869184, 4, 2659845462217400071825608350183702111023828098822940824, [((738734374912:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB043_blk : decide (PbV D_R.N trimmedRB043.cB trimmedRB043.HB
    (polyValsS D_R trimmedRB043.cB (5+65)) (5+trimmedRB043.L) (65-trimmedRB043.L) MGL_R ≤ trimmedRB043.BB) = true := by decide +kernel
theorem trimmedRB043_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((738734374912:ℚ)/(TT:ℚ)) (-6460940182451833247/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB043_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (738734374912:ℤ)
    (polyValsS D_R (738734374912:ℤ) (5+4)) 5 = [-204814876376908942684196537848067758197, 438399877755562720475215416125548989432, 1169160835718609780314901771554582789969, 14115993645685314349296627394668158533921, 161035816449302342942369268040074655086376] := by decide +kernel
theorem trimmedRB043_c0_aa : AL D_R.N (polyValsS D_R (738734374912:ℤ) (5+4)) 5 4 = [952096848182179697480611970946156897981014061, 17659084017859094072710511875944326292133800252, 2467272809553436021043698280716634334414274909381, 85703579539100376843732659753630998143026248452793] := by decide +kernel
theorem trimmedRB043_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((738734374912:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 738734374912:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 1863049847090656361757141390092981785541622742 := by decide +kernel
theorem trimmedRB043_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 2659845462217400071825608350183702111023828098822940824 none trimmedResidualCap (738734374912,17179869184) (-6460940182451833247/9223372036854775808:ℚ) [-204814876376908942684196537848067758197, 438399877755562720475215416125548989432, 1169160835718609780314901771554582789969, 14115993645685314349296627394668158533921, 161035816449302342942369268040074655086376] [952096848182179697480611970946156897981014061, 17659084017859094072710511875944326292133800252, 2467272809553436021043698280716634334414274909381, 85703579539100376843732659753630998143026248452793] 1863049847090656361757141390092981785541622742 = true := by decide +kernel
theorem trimmedRB043_cells : ∀ c ∈ trimmedRB043.cells,
    |c.1 - trimmedRB043.cB| + c.2.1 ≤ trimmedRB043.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB043.L trimmedRB043.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB043, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 2659845462217400071825608350183702111023828098822940824
        trimmedResidualCap (738734374912:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB043_c0_ev trimmedRB043_c0_fh trimmedRB043_c0_aa trimmedRB043_c0_mp trimmedRB043_c0_fin⟩
theorem trimmedRB043_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB043 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB043
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB043_blk trimmedRB043_cells
end CatalanMeasure.Improvement.Fields
