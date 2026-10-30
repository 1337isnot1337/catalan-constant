module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB041 : Block := ⟨670014898176, 17179869184, 4, 773565322331391820990396340458526044773878272262445468, [((670014898176:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB041_blk : decide (PbV D_R.N trimmedRB041.cB trimmedRB041.HB
    (polyValsS D_R trimmedRB041.cB (5+65)) (5+trimmedRB041.L) (65-trimmedRB041.L) MGL_R ≤ trimmedRB041.BB) = true := by decide +kernel
theorem trimmedRB041_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((670014898176:ℚ)/(TT:ℚ)) (-6091823821572592051/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB041_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (670014898176:ℤ)
    (polyValsS D_R (670014898176:ℤ) (5+4)) 5 = [-230455289888129416826041797701726898136, 389486116219977217697245016868710743428, 457029479460681908404883604886215383159, 8925975869165312923181700730578944368052, -49222956817712599413748469589204396765934] := by decide +kernel
theorem trimmedRB041_c0_aa : AL D_R.N (polyValsS D_R (670014898176:ℤ) (5+4)) 5 4 = [345409395060826371997857325484006238616520587, 664011721801716842381332045275767523975474843, 237432055722579790811503265780285782436565072427, 222737601176783936006143190500990529600663351476118] := by decide +kernel
theorem trimmedRB041_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((670014898176:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 670014898176:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 627407255210383443295660155406204399428002633 := by decide +kernel
theorem trimmedRB041_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 773565322331391820990396340458526044773878272262445468 none trimmedResidualCap (670014898176,17179869184) (-6091823821572592051/9223372036854775808:ℚ) [-230455289888129416826041797701726898136, 389486116219977217697245016868710743428, 457029479460681908404883604886215383159, 8925975869165312923181700730578944368052, -49222956817712599413748469589204396765934] [345409395060826371997857325484006238616520587, 664011721801716842381332045275767523975474843, 237432055722579790811503265780285782436565072427, 222737601176783936006143190500990529600663351476118] 627407255210383443295660155406204399428002633 = true := by decide +kernel
theorem trimmedRB041_cells : ∀ c ∈ trimmedRB041.cells,
    |c.1 - trimmedRB041.cB| + c.2.1 ≤ trimmedRB041.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB041.L trimmedRB041.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB041, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 773565322331391820990396340458526044773878272262445468
        trimmedResidualCap (670014898176:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB041_c0_ev trimmedRB041_c0_fh trimmedRB041_c0_aa trimmedRB041_c0_mp trimmedRB041_c0_fin⟩
theorem trimmedRB041_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB041 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB041
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB041_blk trimmedRB041_cells
end CatalanMeasure.Improvement.Fields
