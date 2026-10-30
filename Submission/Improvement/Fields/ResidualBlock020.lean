module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB020 : Block := ⟨-360777252864, 17179869184, 4, 521075319830428903972876832710477417332497259400142831, [((-360777252864:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB020_blk : decide (PbV D_R.N trimmedRB020.cB trimmedRB020.HB
    (polyValsS D_R trimmedRB020.cB (5+65)) (5+trimmedRB020.L) (65-trimmedRB020.L) MGL_R ≤ trimmedRB020.BB) = true := by decide +kernel
theorem trimmedRB020_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-360777252864:ℚ)/(TT:ℚ)) (-619153658129456279/4611686018427387904:ℚ) = true := by decide +kernel
theorem trimmedRB020_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-360777252864:ℤ)
    (polyValsS D_R (-360777252864:ℤ) (5+4)) 5 = [66336535640110224875575804561946188861, 537637848768759502508090046735714457093, 3516543265294650255954349064046541607894, 34719467278997662790977767887487811979383, 286347433363072375773604257557003321995829] := by decide +kernel
theorem trimmedRB020_c0_aa : AL D_R.N (polyValsS D_R (-360777252864:ℤ) (5+4)) 5 4 = [37866296915772809980753170074339371116304966, 3736806724354897112407230854084903942216572718, 805218986822278490527379502130906283149985362419, 139500839540862847049835952672554076806124398663093] := by decide +kernel
theorem trimmedRB020_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-360777252864:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -360777252864:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 136259256328257428098316953713813294322166795 := by decide +kernel
theorem trimmedRB020_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 521075319830428903972876832710477417332497259400142831 none trimmedResidualCap (-360777252864,17179869184) (-619153658129456279/4611686018427387904:ℚ) [66336535640110224875575804561946188861, 537637848768759502508090046735714457093, 3516543265294650255954349064046541607894, 34719467278997662790977767887487811979383, 286347433363072375773604257557003321995829] [37866296915772809980753170074339371116304966, 3736806724354897112407230854084903942216572718, 805218986822278490527379502130906283149985362419, 139500839540862847049835952672554076806124398663093] 136259256328257428098316953713813294322166795 = true := by decide +kernel
theorem trimmedRB020_cells : ∀ c ∈ trimmedRB020.cells,
    |c.1 - trimmedRB020.cB| + c.2.1 ≤ trimmedRB020.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB020.L trimmedRB020.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB020, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 521075319830428903972876832710477417332497259400142831
        trimmedResidualCap (-360777252864:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB020_c0_ev trimmedRB020_c0_fh trimmedRB020_c0_aa trimmedRB020_c0_mp trimmedRB020_c0_fin⟩
theorem trimmedRB020_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB020 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB020
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB020_blk trimmedRB020_cells
end CatalanMeasure.Improvement.Fields
