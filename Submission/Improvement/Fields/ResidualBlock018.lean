module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB018 : Block := ⟨-429496729600, 17179869184, 4, 315958584812011107700374224533526535865380682174262459, [((-429496729600:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB018_blk : decide (PbV D_R.N trimmedRB018.cB trimmedRB018.HB
    (polyValsS D_R trimmedRB018.cB (5+65)) (5+trimmedRB018.L) (65-trimmedRB018.L) MGL_R ≤ trimmedRB018.BB) = true := by decide +kernel
theorem trimmedRB018_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-429496729600:ℚ)/(TT:ℚ)) (-2651168238413769139/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB018_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-429496729600:ℤ)
    (polyValsS D_R (-429496729600:ℤ) (5+4)) 5 = [38421249816892859227818191233343271630, 371485453295437158237835358054682465913, 1980173958900474188496683979115232772254, 17400873982007194871430953682116260513407, 48198800650272975056203406681650830829720] := by decide +kernel
theorem trimmedRB018_c0_aa : AL D_R.N (polyValsS D_R (-429496729600:ℤ) (5+4)) 5 4 = [5061545651763028172667671963407229380467986, 4292603466087656097617805527590278732687800612, 65399552291729670020388937804860612451378779088, 156624696994962176856167765266239771320972414346294] := by decide +kernel
theorem trimmedRB018_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-429496729600:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -429496729600:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 34060962943500768972286981568085251828628943 := by decide +kernel
theorem trimmedRB018_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 315958584812011107700374224533526535865380682174262459 none trimmedResidualCap (-429496729600,17179869184) (-2651168238413769139/18446744073709551616:ℚ) [38421249816892859227818191233343271630, 371485453295437158237835358054682465913, 1980173958900474188496683979115232772254, 17400873982007194871430953682116260513407, 48198800650272975056203406681650830829720] [5061545651763028172667671963407229380467986, 4292603466087656097617805527590278732687800612, 65399552291729670020388937804860612451378779088, 156624696994962176856167765266239771320972414346294] 34060962943500768972286981568085251828628943 = true := by decide +kernel
theorem trimmedRB018_cells : ∀ c ∈ trimmedRB018.cells,
    |c.1 - trimmedRB018.cB| + c.2.1 ≤ trimmedRB018.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB018.L trimmedRB018.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB018, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 315958584812011107700374224533526535865380682174262459
        trimmedResidualCap (-429496729600:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB018_c0_ev trimmedRB018_c0_fh trimmedRB018_c0_aa trimmedRB018_c0_mp trimmedRB018_c0_fin⟩
theorem trimmedRB018_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB018 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB018
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB018_blk trimmedRB018_cells
end CatalanMeasure.Improvement.Fields
