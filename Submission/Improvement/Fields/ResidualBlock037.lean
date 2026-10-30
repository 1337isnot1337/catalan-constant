module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB037 : Block := ⟨532575944704, 17179869184, 4, 291565985914074405831147534630827894923518197482472344, [((532575944704:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB037_blk : decide (PbV D_R.N trimmedRB037.cB trimmedRB037.HB
    (polyValsS D_R trimmedRB037.cB (5+65)) (5+trimmedRB037.L) (65-trimmedRB037.L) MGL_R ≤ trimmedRB037.BB) = true := by decide +kernel
theorem trimmedRB037_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((532575944704:ℚ)/(TT:ℚ)) (-2615136840533843897/4611686018427387904:ℚ) = true := by decide +kernel
theorem trimmedRB037_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (532575944704:ℤ)
    (polyValsS D_R (532575944704:ℤ) (5+4)) 5 = [-278240595392541553862573278038053276610, 395513130632097254125455913217515922544, -546879395347175186922201234050075096682, 8973109473438980330883775007958312281841, -101607706899045543629794006916887080362835] := by decide +kernel
theorem trimmedRB037_c0_aa : AL D_R.N (polyValsS D_R (532575944704:ℤ) (5+4)) 5 4 = [71945718412359051684456842099002051107289712, 1561628323499026414829798282534403297715391360, 198834779786219120405237853658042452715243541522, 90382024145066483471126877720471392500212778953873] := by decide +kernel
theorem trimmedRB037_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((532575944704:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 532575944704:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 118643299310839889156585536764652139488121087 := by decide +kernel
theorem trimmedRB037_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 291565985914074405831147534630827894923518197482472344 none trimmedResidualCap (532575944704,17179869184) (-2615136840533843897/4611686018427387904:ℚ) [-278240595392541553862573278038053276610, 395513130632097254125455913217515922544, -546879395347175186922201234050075096682, 8973109473438980330883775007958312281841, -101607706899045543629794006916887080362835] [71945718412359051684456842099002051107289712, 1561628323499026414829798282534403297715391360, 198834779786219120405237853658042452715243541522, 90382024145066483471126877720471392500212778953873] 118643299310839889156585536764652139488121087 = true := by decide +kernel
theorem trimmedRB037_cells : ∀ c ∈ trimmedRB037.cells,
    |c.1 - trimmedRB037.cB| + c.2.1 ≤ trimmedRB037.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB037.L trimmedRB037.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB037, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 291565985914074405831147534630827894923518197482472344
        trimmedResidualCap (532575944704:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB037_c0_ev trimmedRB037_c0_fh trimmedRB037_c0_aa trimmedRB037_c0_mp trimmedRB037_c0_fin⟩
theorem trimmedRB037_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB037 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB037
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB037_blk trimmedRB037_cells
end CatalanMeasure.Improvement.Fields
