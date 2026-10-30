module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB022 : Block := ⟨-292057776128, 17179869184, 4, 1183906163240538095677512685774939770436832969412407640, [((-292057776128:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB022_blk : decide (PbV D_R.N trimmedRB022.cB trimmedRB022.HB
    (polyValsS D_R trimmedRB022.cB (5+65)) (5+trimmedRB022.L) (65-trimmedRB022.L) MGL_R ≤ trimmedRB022.BB) = true := by decide +kernel
theorem trimmedRB022_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-292057776128:ℚ)/(TT:ℚ)) (-2185794376017696245/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB022_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-292057776128:ℤ)
    (polyValsS D_R (-292057776128:ℤ) (5+4)) 5 = [108513129036187484629501352388977052150, 845698978473685642715303607104846409088, 6802680389274923183543346809317639610751, 79915101766813288900780378198481791797012, 1029033410414612254675885735727279317803917] := by decide +kernel
theorem trimmedRB022_c0_aa : AL D_R.N (polyValsS D_R (-292057776128:ℤ) (5+4)) 5 4 = [156607574148185950158647768108000825550288142, 747234079968437628588803182457380828167484651, 2251069616133730133579719231173487750540050456791, 71956445746907312361765727635109534652927594915218] := by decide +kernel
theorem trimmedRB022_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-292057776128:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -292057776128:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 926807742193298049878001611714908814948760900 := by decide +kernel
theorem trimmedRB022_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 1183906163240538095677512685774939770436832969412407640 none trimmedResidualCap (-292057776128,17179869184) (-2185794376017696245/18446744073709551616:ℚ) [108513129036187484629501352388977052150, 845698978473685642715303607104846409088, 6802680389274923183543346809317639610751, 79915101766813288900780378198481791797012, 1029033410414612254675885735727279317803917] [156607574148185950158647768108000825550288142, 747234079968437628588803182457380828167484651, 2251069616133730133579719231173487750540050456791, 71956445746907312361765727635109534652927594915218] 926807742193298049878001611714908814948760900 = true := by decide +kernel
theorem trimmedRB022_cells : ∀ c ∈ trimmedRB022.cells,
    |c.1 - trimmedRB022.cB| + c.2.1 ≤ trimmedRB022.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB022.L trimmedRB022.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB022, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 1183906163240538095677512685774939770436832969412407640
        trimmedResidualCap (-292057776128:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB022_c0_ev trimmedRB022_c0_fh trimmedRB022_c0_aa trimmedRB022_c0_mp trimmedRB022_c0_fin⟩
theorem trimmedRB022_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB022 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB022
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB022_blk trimmedRB022_cells
end CatalanMeasure.Improvement.Fields
