module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB045 : Block := ⟨807453851648, 17179869184, 4, 10714052713846830977083118446356336542073325008998649839, [((807453851648:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB045_blk : decide (PbV D_R.N trimmedRB045.cB trimmedRB045.HB
    (polyValsS D_R trimmedRB045.cB (5+65)) (5+trimmedRB045.L) (65-trimmedRB045.L) MGL_R ≤ trimmedRB045.BB) = true := by decide +kernel
theorem trimmedRB045_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((807453851648:ℚ)/(TT:ℚ)) (-3391558256145252545/4611686018427387904:ℚ) = true := by decide +kernel
theorem trimmedRB045_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (807453851648:ℤ)
    (polyValsS D_R (807453851648:ℤ) (5+4)) 5 = [-174405137927530512503622764036259657701, 548753549402603819460071925116326165040, 2534266419701012107684093884074608347639, 33243489662961805364007823264960783980434, 694440706240195009004908842446342780867246] := by decide +kernel
theorem trimmedRB045_c0_aa : AL D_R.N (polyValsS D_R (807453851648:ℤ) (5+4)) 5 4 = [3572363040211379279959152063299414993314860664, 95809786473483346128749272443242525396351459738, 1720380196229874329922711752421664990257079608467, 1156157004322759444327336076754261817589660032259091] := by decide +kernel
theorem trimmedRB045_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((807453851648:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 807453851648:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 7065205654142305746601723766878395589874080257 := by decide +kernel
theorem trimmedRB045_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 10714052713846830977083118446356336542073325008998649839 none trimmedResidualCap (807453851648,17179869184) (-3391558256145252545/4611686018427387904:ℚ) [-174405137927530512503622764036259657701, 548753549402603819460071925116326165040, 2534266419701012107684093884074608347639, 33243489662961805364007823264960783980434, 694440706240195009004908842446342780867246] [3572363040211379279959152063299414993314860664, 95809786473483346128749272443242525396351459738, 1720380196229874329922711752421664990257079608467, 1156157004322759444327336076754261817589660032259091] 7065205654142305746601723766878395589874080257 = true := by decide +kernel
theorem trimmedRB045_cells : ∀ c ∈ trimmedRB045.cells,
    |c.1 - trimmedRB045.cB| + c.2.1 ≤ trimmedRB045.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB045.L trimmedRB045.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB045, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 10714052713846830977083118446356336542073325008998649839
        trimmedResidualCap (807453851648:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB045_c0_ev trimmedRB045_c0_fh trimmedRB045_c0_aa trimmedRB045_c0_mp trimmedRB045_c0_fin⟩
theorem trimmedRB045_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB045 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB045
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB045_blk trimmedRB045_cells
end CatalanMeasure.Improvement.Fields
