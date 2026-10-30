module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB040 : Block := ⟨635655159808, 17179869184, 4, 613330455929665327568411877266042942783179736399160879, [((635655159808:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB040_blk : decide (PbV D_R.N trimmedRB040.cB trimmedRB040.HB
    (polyValsS D_R trimmedRB040.cB (5+65)) (5+trimmedRB040.L) (65-trimmedRB040.L) MGL_R ≤ trimmedRB040.BB) = true := by decide +kernel
theorem trimmedRB040_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((635655159808:ℚ)/(TT:ℚ)) (-11783038289095362685/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB040_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (635655159808:ℤ)
    (polyValsS D_R (635655159808:ℤ) (5+4)) 5 = [-242448764153432584469762334722283637558, 379465820744536372922116124342577623682, 193838160617681826380036446212089934742, 7986118660631789126771812831966705477167, -63865355137272034564420996513492704633533] := by decide +kernel
theorem trimmedRB040_c0_aa : AL D_R.N (polyValsS D_R (635655159808:ℤ) (5+4)) 5 4 = [223826769322270624723996226689415437929437119, 639564926004923461018884406004631114520812574, 121137807225320910072843062095769996944935885348, 164268045968283877207596114712676216238651449376458] := by decide +kernel
theorem trimmedRB040_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((635655159808:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 635655159808:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 389804839356638615196255636762414944454123385 := by decide +kernel
theorem trimmedRB040_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 613330455929665327568411877266042942783179736399160879 none trimmedResidualCap (635655159808,17179869184) (-11783038289095362685/18446744073709551616:ℚ) [-242448764153432584469762334722283637558, 379465820744536372922116124342577623682, 193838160617681826380036446212089934742, 7986118660631789126771812831966705477167, -63865355137272034564420996513492704633533] [223826769322270624723996226689415437929437119, 639564926004923461018884406004631114520812574, 121137807225320910072843062095769996944935885348, 164268045968283877207596114712676216238651449376458] 389804839356638615196255636762414944454123385 = true := by decide +kernel
theorem trimmedRB040_cells : ∀ c ∈ trimmedRB040.cells,
    |c.1 - trimmedRB040.cB| + c.2.1 ≤ trimmedRB040.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB040.L trimmedRB040.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB040, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 613330455929665327568411877266042942783179736399160879
        trimmedResidualCap (635655159808:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB040_c0_ev trimmedRB040_c0_fh trimmedRB040_c0_aa trimmedRB040_c0_mp trimmedRB040_c0_fin⟩
theorem trimmedRB040_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB040 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB040
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB040_blk trimmedRB040_cells
end CatalanMeasure.Improvement.Fields
