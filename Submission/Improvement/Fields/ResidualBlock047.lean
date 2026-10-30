module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB047 : Block := ⟨876173328384, 17179869184, 4, 104278800664864322551007489703826559664810481961626723515, [((876173328384:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB047_blk : decide (PbV D_R.N trimmedRB047.cB trimmedRB047.HB
    (polyValsS D_R trimmedRB047.cB (5+65)) (5+trimmedRB047.L) (65-trimmedRB047.L) MGL_R ≤ trimmedRB047.BB) = true := by decide +kernel
theorem trimmedRB047_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((876173328384:ℚ)/(TT:ℚ)) (-14092089873171642299/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB047_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (876173328384:ℤ)
    (polyValsS D_R (876173328384:ℤ) (5+4)) 5 = [-133465891364734421184658256102834617423, 796307402889815906657765634346324537578, 5971202170233298762075628934080743996854, 86422083053960673200652282415868544453541, 1776287906056611025661841178761657190973718] := by decide +kernel
theorem trimmedRB047_c0_aa : AL D_R.N (polyValsS D_R (876173328384:ℤ) (5+4)) 5 4 = [16996760733845111783316773340900847116916287211, 494665816964839532088589240065757706176409007444, 43088867745804460024558462869516351902566770196583, 3102642200751128384432858418159600265997707684552087] := by decide +kernel
theorem trimmedRB047_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((876173328384:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 876173328384:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 39330429472693793359895235786029417322808276113 := by decide +kernel
theorem trimmedRB047_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 104278800664864322551007489703826559664810481961626723515 none trimmedResidualCap (876173328384,17179869184) (-14092089873171642299/18446744073709551616:ℚ) [-133465891364734421184658256102834617423, 796307402889815906657765634346324537578, 5971202170233298762075628934080743996854, 86422083053960673200652282415868544453541, 1776287906056611025661841178761657190973718] [16996760733845111783316773340900847116916287211, 494665816964839532088589240065757706176409007444, 43088867745804460024558462869516351902566770196583, 3102642200751128384432858418159600265997707684552087] 39330429472693793359895235786029417322808276113 = true := by decide +kernel
theorem trimmedRB047_cells : ∀ c ∈ trimmedRB047.cells,
    |c.1 - trimmedRB047.cB| + c.2.1 ≤ trimmedRB047.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB047.L trimmedRB047.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB047, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 104278800664864322551007489703826559664810481961626723515
        trimmedResidualCap (876173328384:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB047_c0_ev trimmedRB047_c0_fh trimmedRB047_c0_aa trimmedRB047_c0_mp trimmedRB047_c0_fin⟩
theorem trimmedRB047_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB047 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB047
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB047_blk trimmedRB047_cells
end CatalanMeasure.Improvement.Fields
