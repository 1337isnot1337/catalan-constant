module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB029 : Block := ⟨257698037760, 17179869184, 4, 2480465754120495385762133189057684453203638378421476757, [((257698037760:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB029_blk : decide (PbV D_R.N trimmedRB029.cB trimmedRB029.HB
    (polyValsS D_R trimmedRB029.cB (5+65)) (5+trimmedRB029.L) (65-trimmedRB029.L) MGL_R ≤ trimmedRB029.BB) = true := by decide +kernel
theorem trimmedRB029_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((257698037760:ℚ)/(TT:ℚ)) (-5823362999829639335/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB029_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (257698037760:ℤ)
    (polyValsS D_R (257698037760:ℤ) (5+4)) 5 = [-435191727336074271167508664581076904435, 1181663081202105199908421899535368721982, -9651739615107200683049031618061765730064, 127955890792311943156261113481302765047140, -2529514824851812147856193784389439947946045] := by decide +kernel
theorem trimmedRB029_c0_aa : AL D_R.N (polyValsS D_R (257698037760:ℤ) (5+4)) 5 4 = [339291069640912961584042625459922874336466538, 30620344960420232461638188612381462604502736058, 4572396884918995150014465282041811357098305492203, 228899825427899403417846619451576274707039190214282] := by decide +kernel
theorem trimmedRB029_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((257698037760:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 257698037760:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 3160811828174723710589904614078511482503591792 := by decide +kernel
theorem trimmedRB029_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 2480465754120495385762133189057684453203638378421476757 none trimmedResidualCap (257698037760,17179869184) (-5823362999829639335/18446744073709551616:ℚ) [-435191727336074271167508664581076904435, 1181663081202105199908421899535368721982, -9651739615107200683049031618061765730064, 127955890792311943156261113481302765047140, -2529514824851812147856193784389439947946045] [339291069640912961584042625459922874336466538, 30620344960420232461638188612381462604502736058, 4572396884918995150014465282041811357098305492203, 228899825427899403417846619451576274707039190214282] 3160811828174723710589904614078511482503591792 = true := by decide +kernel
theorem trimmedRB029_cells : ∀ c ∈ trimmedRB029.cells,
    |c.1 - trimmedRB029.cB| + c.2.1 ≤ trimmedRB029.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB029.L trimmedRB029.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB029, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 2480465754120495385762133189057684453203638378421476757
        trimmedResidualCap (257698037760:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB029_c0_ev trimmedRB029_c0_fh trimmedRB029_c0_aa trimmedRB029_c0_mp trimmedRB029_c0_fin⟩
theorem trimmedRB029_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB029 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB029
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB029_blk trimmedRB029_cells
end CatalanMeasure.Improvement.Fields
