module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB008 : Block := ⟨-773094113280, 17179869184, 4, 5544900733124287774081389605940499404373945331195656044, [((-773094113280:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB008_blk : decide (PbV D_R.N trimmedRB008.cB trimmedRB008.HB
    (polyValsS D_R trimmedRB008.cB (5+65)) (5+trimmedRB008.L) (65-trimmedRB008.L) MGL_R ≤ trimmedRB008.BB) = true := by decide +kernel
theorem trimmedRB008_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-773094113280:ℚ)/(TT:ℚ)) (-1312741688418930787/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB008_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-773094113280:ℤ)
    (polyValsS D_R (-773094113280:ℤ) (5+4)) 5 = [-32785458535302847423555571303419814281, 189863936925673959678694253665080801813, -294654905794397118230155821755247604787, 7077314205858230779782455014198225210715, -108115327303828358463888327020305126278888] := by decide +kernel
theorem trimmedRB008_c0_aa : AL D_R.N (polyValsS D_R (-773094113280:ℤ) (5+4)) 5 4 = [36108956251662919484747855638237389519593618, 4516988820330027511558321168240795052208943389, 3568888025901877352953420352452570770359066422741, 368555763637013227134483036950631223464919994630712] := by decide +kernel
theorem trimmedRB008_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-773094113280:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -773094113280:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 67874185143713728434561748304620832936229419 := by decide +kernel
theorem trimmedRB008_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 5544900733124287774081389605940499404373945331195656044 none trimmedResidualCap (-773094113280,17179869184) (-1312741688418930787/9223372036854775808:ℚ) [-32785458535302847423555571303419814281, 189863936925673959678694253665080801813, -294654905794397118230155821755247604787, 7077314205858230779782455014198225210715, -108115327303828358463888327020305126278888] [36108956251662919484747855638237389519593618, 4516988820330027511558321168240795052208943389, 3568888025901877352953420352452570770359066422741, 368555763637013227134483036950631223464919994630712] 67874185143713728434561748304620832936229419 = true := by decide +kernel
theorem trimmedRB008_cells : ∀ c ∈ trimmedRB008.cells,
    |c.1 - trimmedRB008.cB| + c.2.1 ≤ trimmedRB008.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB008.L trimmedRB008.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB008, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 5544900733124287774081389605940499404373945331195656044
        trimmedResidualCap (-773094113280:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB008_c0_ev trimmedRB008_c0_fh trimmedRB008_c0_aa trimmedRB008_c0_mp trimmedRB008_c0_fin⟩
theorem trimmedRB008_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB008 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB008
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB008_blk trimmedRB008_cells
end CatalanMeasure.Improvement.Fields
