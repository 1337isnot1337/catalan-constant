module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB007 : Block := ⟨-807453851648, 17179869184, 4, 10049576221923216694724999201021210681029201052427635757, [((-807453851648:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB007_blk : decide (PbV D_R.N trimmedRB007.cB trimmedRB007.HB
    (polyValsS D_R trimmedRB007.cB (5+65)) (5+trimmedRB007.L) (65-trimmedRB007.L) MGL_R ≤ trimmedRB007.BB) = true := by decide +kernel
theorem trimmedRB007_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-807453851648:ℚ)/(TT:ℚ)) (-1282410901785317659/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB007_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-807453851648:ℤ)
    (polyValsS D_R (-807453851648:ℤ) (5+4)) 5 = [-38894955454789097169966545075024372676, 202174581380779115742173404111040168053, -505590641919124767510013737194763233248, 8363228002981538803138472188420611833208, 249674712082031132071108900706843940752744] := by decide +kernel
theorem trimmedRB007_c0_aa : AL D_R.N (polyValsS D_R (-807453851648:ℤ) (5+4)) 5 4 = [167223506624801443477225280361476918581900, 19290147991974234952384689016704577646107609688, 4115610315686941104232572180627294891709330397762, 961610845351443592627306237133736442743079033927291] := by decide +kernel
theorem trimmedRB007_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-807453851648:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -807453851648:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 136150475323244089546215816604108287075645073 := by decide +kernel
theorem trimmedRB007_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 10049576221923216694724999201021210681029201052427635757 none trimmedResidualCap (-807453851648,17179869184) (-1282410901785317659/9223372036854775808:ℚ) [-38894955454789097169966545075024372676, 202174581380779115742173404111040168053, -505590641919124767510013737194763233248, 8363228002981538803138472188420611833208, 249674712082031132071108900706843940752744] [167223506624801443477225280361476918581900, 19290147991974234952384689016704577646107609688, 4115610315686941104232572180627294891709330397762, 961610845351443592627306237133736442743079033927291] 136150475323244089546215816604108287075645073 = true := by decide +kernel
theorem trimmedRB007_cells : ∀ c ∈ trimmedRB007.cells,
    |c.1 - trimmedRB007.cB| + c.2.1 ≤ trimmedRB007.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB007.L trimmedRB007.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB007, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 10049576221923216694724999201021210681029201052427635757
        trimmedResidualCap (-807453851648:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB007_c0_ev trimmedRB007_c0_fh trimmedRB007_c0_aa trimmedRB007_c0_mp trimmedRB007_c0_fin⟩
theorem trimmedRB007_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB007 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB007
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB007_blk trimmedRB007_cells
end CatalanMeasure.Improvement.Fields
