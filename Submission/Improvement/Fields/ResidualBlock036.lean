module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB036 : Block := ⟨498216206336, 17179869184, 4, 240023664421564683188864597769811695953133787143140544, [((498216206336:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB036_blk : decide (PbV D_R.N trimmedRB036.cB trimmedRB036.HB
    (polyValsS D_R trimmedRB036.cB (5+65)) (5+trimmedRB036.L) (65-trimmedRB036.L) MGL_R ≤ trimmedRB036.BB) = true := by decide +kernel
theorem trimmedRB036_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((498216206336:ℚ)/(TT:ℚ)) (-9978549414154575903/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB036_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (498216206336:ℤ)
    (polyValsS D_R (498216206336:ℤ) (5+4)) 5 = [-290915103659751038242246453110937932206, 417214589855190174893232415159804870686, -847728680127512779275803506310460685155, 10646216238440356269609987859070506323801, -131035358876684534329666009440791888660010] := by decide +kernel
theorem trimmedRB036_c0_aa : AL D_R.N (polyValsS D_R (498216206336:ℤ) (5+4)) 5 4 = [50561175610244223403156326800988112801803894, 1838169334262284152242360969313596833679551777, 124857185476773124029395632317721733175453234330, 89040625181502253261903433739326599174432578666426] := by decide +kernel
theorem trimmedRB036_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((498216206336:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 498216206336:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 88685566130104647293310860393019986706193705 := by decide +kernel
theorem trimmedRB036_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 240023664421564683188864597769811695953133787143140544 none trimmedResidualCap (498216206336,17179869184) (-9978549414154575903/18446744073709551616:ℚ) [-290915103659751038242246453110937932206, 417214589855190174893232415159804870686, -847728680127512779275803506310460685155, 10646216238440356269609987859070506323801, -131035358876684534329666009440791888660010] [50561175610244223403156326800988112801803894, 1838169334262284152242360969313596833679551777, 124857185476773124029395632317721733175453234330, 89040625181502253261903433739326599174432578666426] 88685566130104647293310860393019986706193705 = true := by decide +kernel
theorem trimmedRB036_cells : ∀ c ∈ trimmedRB036.cells,
    |c.1 - trimmedRB036.cB| + c.2.1 ≤ trimmedRB036.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB036.L trimmedRB036.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB036, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 240023664421564683188864597769811695953133787143140544
        trimmedResidualCap (498216206336:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB036_c0_ev trimmedRB036_c0_fh trimmedRB036_c0_aa trimmedRB036_c0_mp trimmedRB036_c0_fin⟩
theorem trimmedRB036_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB036 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB036
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB036_blk trimmedRB036_cells
end CatalanMeasure.Improvement.Fields
