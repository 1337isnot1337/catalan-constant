module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB006 : Block := ⟨-841813590016, 17179869184, 4, 22098427578540545173721723399130332778333546592995850884, [((-841813590016:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB006_blk : decide (PbV D_R.N trimmedRB006.cB trimmedRB006.HB
    (polyValsS D_R trimmedRB006.cB (5+65)) (5+trimmedRB006.L) (65-trimmedRB006.L) MGL_R ≤ trimmedRB006.BB) = true := by decide +kernel
theorem trimmedRB006_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-841813590016:ℚ)/(TT:ℚ)) (-2493424212238932463/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB006_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-841813590016:ℤ)
    (polyValsS D_R (-841813590016:ℤ) (5+4)) 5 = [-45498548473649863478999931442346140431, 221888225707022290183779698749693848599, -778037475269328682759083883054548765559, 8512895853703876845320456835013559276610, 200075490258593473842653357145486903007419] := by decide +kernel
theorem trimmedRB006_c0_aa : AL D_R.N (polyValsS D_R (-841813590016:ℤ) (5+4)) 5 4 = [243059278867658263784826384632642470381934256, 28309548725569696345472777006507394915993839236, 6812397579736481000615861924360779187240853105764, 1910975747418782141609782937146072944810664626870083] := by decide +kernel
theorem trimmedRB006_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-841813590016:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -841813590016:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 300867924621986355018245471274613066595099316 := by decide +kernel
theorem trimmedRB006_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 22098427578540545173721723399130332778333546592995850884 none trimmedResidualCap (-841813590016,17179869184) (-2493424212238932463/18446744073709551616:ℚ) [-45498548473649863478999931442346140431, 221888225707022290183779698749693848599, -778037475269328682759083883054548765559, 8512895853703876845320456835013559276610, 200075490258593473842653357145486903007419] [243059278867658263784826384632642470381934256, 28309548725569696345472777006507394915993839236, 6812397579736481000615861924360779187240853105764, 1910975747418782141609782937146072944810664626870083] 300867924621986355018245471274613066595099316 = true := by decide +kernel
theorem trimmedRB006_cells : ∀ c ∈ trimmedRB006.cells,
    |c.1 - trimmedRB006.cB| + c.2.1 ≤ trimmedRB006.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB006.L trimmedRB006.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB006, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 22098427578540545173721723399130332778333546592995850884
        trimmedResidualCap (-841813590016:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB006_c0_ev trimmedRB006_c0_fh trimmedRB006_c0_aa trimmedRB006_c0_mp trimmedRB006_c0_fin⟩
theorem trimmedRB006_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB006 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB006
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB006_blk trimmedRB006_cells
end CatalanMeasure.Improvement.Fields
