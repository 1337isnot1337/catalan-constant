module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB042 : Block := ⟨704374636544, 17179869184, 4, 1415866456888239471596422053761561870133393326502981448, [((704374636544:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB042_blk : decide (PbV D_R.N trimmedRB042.cB trimmedRB042.HB
    (polyValsS D_R trimmedRB042.cB (5+65)) (5+trimmedRB042.L) (65-trimmedRB042.L) MGL_R ≤ trimmedRB042.BB) = true := by decide +kernel
theorem trimmedRB042_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((704374636544:ℚ)/(TT:ℚ)) (-6281799407939384543/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB042_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (704374636544:ℤ)
    (polyValsS D_R (704374636544:ℤ) (5+4)) 5 = [-218013532215216614261198761788627143168, 408422355012228940780214593385297956647, 769259802681980581582171722476858091176, 10755323803314265034337288291285216539044, 4219821451648041373771432131147094871198] := by decide +kernel
theorem trimmedRB042_c0_aa : AL D_R.N (polyValsS D_R (704374636544:ℤ) (5+4)) 5 4 = [555919699429872980637212843810750535622378757, 4948258933129555461929284228347428979746767275, 1089806069026355523897925509697097145818924303938, 253755362049189782506192483411145897593597747754784] := by decide +kernel
theorem trimmedRB042_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((704374636544:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 704374636544:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 1054366528620579856662858949832429772898822902 := by decide +kernel
theorem trimmedRB042_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 1415866456888239471596422053761561870133393326502981448 none trimmedResidualCap (704374636544,17179869184) (-6281799407939384543/9223372036854775808:ℚ) [-218013532215216614261198761788627143168, 408422355012228940780214593385297956647, 769259802681980581582171722476858091176, 10755323803314265034337288291285216539044, 4219821451648041373771432131147094871198] [555919699429872980637212843810750535622378757, 4948258933129555461929284228347428979746767275, 1089806069026355523897925509697097145818924303938, 253755362049189782506192483411145897593597747754784] 1054366528620579856662858949832429772898822902 = true := by decide +kernel
theorem trimmedRB042_cells : ∀ c ∈ trimmedRB042.cells,
    |c.1 - trimmedRB042.cB| + c.2.1 ≤ trimmedRB042.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB042.L trimmedRB042.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB042, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 1415866456888239471596422053761561870133393326502981448
        trimmedResidualCap (704374636544:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB042_c0_ev trimmedRB042_c0_fh trimmedRB042_c0_aa trimmedRB042_c0_mp trimmedRB042_c0_fin⟩
theorem trimmedRB042_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB042 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB042
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB042_blk trimmedRB042_cells
end CatalanMeasure.Improvement.Fields
