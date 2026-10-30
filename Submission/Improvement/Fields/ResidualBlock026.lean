module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB026 : Block := ⟨154618822656, 17179869184, 4, 523555875952566872815299164515445267115842783583975828876, [((154618822656:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB026_blk : decide (PbV D_R.N trimmedRB026.cB trimmedRB026.HB
    (polyValsS D_R trimmedRB026.cB (5+65)) (5+trimmedRB026.L) (65-trimmedRB026.L) MGL_R ≤ trimmedRB026.BB) = true := by decide +kernel
theorem trimmedRB026_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((154618822656:ℚ)/(TT:ℚ)) (-1612447522843967293/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB026_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (154618822656:ℤ)
    (polyValsS D_R (154618822656:ℤ) (5+4)) 5 = [-617889113291632551777426959720666849232, 3237772530234928923807558518465953374852, -41222317559782747796716523882573739089483, 1219849526550087945608359392618156999255943, -3723721875896274582854359240618412226787832116] := by decide +kernel
theorem trimmedRB026_c0_aa : AL D_R.N (polyValsS D_R (154618822656:ℤ) (5+4)) 5 4 = [357104236161099626239779931607162311556638652644, 34241514178155625326626603508224587125028825203116, 8628592574657386489451276622762518338308353896680399, 548936458765797527945149102060728301424724942028569255] := by decide +kernel
theorem trimmedRB026_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((154618822656:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 154618822656:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 145155068957286013852236862518362651208315722796586 := by decide +kernel
theorem trimmedRB026_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 523555875952566872815299164515445267115842783583975828876 none trimmedResidualCap (154618822656,17179869184) (-1612447522843967293/9223372036854775808:ℚ) [-617889113291632551777426959720666849232, 3237772530234928923807558518465953374852, -41222317559782747796716523882573739089483, 1219849526550087945608359392618156999255943, -3723721875896274582854359240618412226787832116] [357104236161099626239779931607162311556638652644, 34241514178155625326626603508224587125028825203116, 8628592574657386489451276622762518338308353896680399, 548936458765797527945149102060728301424724942028569255] 145155068957286013852236862518362651208315722796586 = true := by decide +kernel
theorem trimmedRB026_cells : ∀ c ∈ trimmedRB026.cells,
    |c.1 - trimmedRB026.cB| + c.2.1 ≤ trimmedRB026.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB026.L trimmedRB026.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB026, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 523555875952566872815299164515445267115842783583975828876
        trimmedResidualCap (154618822656:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB026_c0_ev trimmedRB026_c0_fh trimmedRB026_c0_aa trimmedRB026_c0_mp trimmedRB026_c0_fin⟩
theorem trimmedRB026_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB026 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB026
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB026_blk trimmedRB026_cells
end CatalanMeasure.Improvement.Fields
