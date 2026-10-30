module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB049 : Block := ⟨944892805120, 17179869184, 4, 2407422726389245379598507929584803613015641633868330791353, [((944892805120:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB049_blk : decide (PbV D_R.N trimmedRB049.cB trimmedRB049.HB
    (polyValsS D_R trimmedRB049.cB (5+65)) (5+trimmedRB049.L) (65-trimmedRB049.L) MGL_R ≤ trimmedRB049.BB) = true := by decide +kernel
theorem trimmedRB049_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((944892805120:ℚ)/(TT:ℚ)) (-7221327640865430657/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB049_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (944892805120:ℤ)
    (polyValsS D_R (944892805120:ℤ) (5+4)) 5 = [-66724488377194993166882524322196995350, 1461722830547178298186430529665297226009, 18211096612326261889466330291678816180259, 370207206965581012902870124197216816211754, 10582996005295596197239776738232621853030159] := by decide +kernel
theorem trimmedRB049_c0_aa : AL D_R.N (polyValsS D_R (944892805120:ℤ) (5+4)) 5 4 = [152644428232083828328045781774982238391969911341, 6370483571218513065023669085897128730510633007944, 515968775722685143062519976758203099849106852338446, 50200826719279078516567139076369541417298766655098987] := by decide +kernel
theorem trimmedRB049_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((944892805120:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 944892805120:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 439845612812521186406724177466051895988439444401 := by decide +kernel
theorem trimmedRB049_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 2407422726389245379598507929584803613015641633868330791353 none trimmedResidualCap (944892805120,17179869184) (-7221327640865430657/9223372036854775808:ℚ) [-66724488377194993166882524322196995350, 1461722830547178298186430529665297226009, 18211096612326261889466330291678816180259, 370207206965581012902870124197216816211754, 10582996005295596197239776738232621853030159] [152644428232083828328045781774982238391969911341, 6370483571218513065023669085897128730510633007944, 515968775722685143062519976758203099849106852338446, 50200826719279078516567139076369541417298766655098987] 439845612812521186406724177466051895988439444401 = true := by decide +kernel
theorem trimmedRB049_cells : ∀ c ∈ trimmedRB049.cells,
    |c.1 - trimmedRB049.cB| + c.2.1 ≤ trimmedRB049.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB049.L trimmedRB049.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB049, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 2407422726389245379598507929584803613015641633868330791353
        trimmedResidualCap (944892805120:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB049_c0_ev trimmedRB049_c0_fh trimmedRB049_c0_aa trimmedRB049_c0_mp trimmedRB049_c0_fin⟩
theorem trimmedRB049_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB049 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB049
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB049_blk trimmedRB049_cells
end CatalanMeasure.Improvement.Fields
