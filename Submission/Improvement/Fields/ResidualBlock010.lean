module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB010 : Block := ⟨-704374636544, 17179869184, 4, 1857313978685668285420755795766140649435117362268210278, [((-704374636544:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB010_blk : decide (PbV D_R.N trimmedRB010.cB trimmedRB010.HB
    (polyValsS D_R trimmedRB010.cB (5+65)) (5+trimmedRB010.L) (65-trimmedRB010.L) MGL_R ≤ trimmedRB010.BB) = true := by decide +kernel
theorem trimmedRB010_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-704374636544:ℚ)/(TT:ℚ)) (-679231207657376859/4611686018427387904:ℚ) = true := by decide +kernel
theorem trimmedRB010_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-704374636544:ℤ)
    (polyValsS D_R (-704374636544:ℤ) (5+4)) 5 = [-21277442627727072726769914671964368656, 181622531071626339794336605385698308875, 22116601018830988347154036994922669993, 4378198390014950570269137044052916504289, -189106553715752163600089016784868634391278] := by decide +kernel
theorem trimmedRB010_c0_aa : AL D_R.N (polyValsS D_R (-704374636544:ℤ) (5+4)) 5 4 = [19765453835056878739324287395673808223126838, 8372126782390252910789170624462830196756571133, 577488762729029438109158398557764742583123515935, 394405035938727705816060939723899619532199711404667] := by decide +kernel
theorem trimmedRB010_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-704374636544:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -704374636544:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 21426534828051501105221955584542227587414591 := by decide +kernel
theorem trimmedRB010_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 1857313978685668285420755795766140649435117362268210278 none trimmedResidualCap (-704374636544,17179869184) (-679231207657376859/4611686018427387904:ℚ) [-21277442627727072726769914671964368656, 181622531071626339794336605385698308875, 22116601018830988347154036994922669993, 4378198390014950570269137044052916504289, -189106553715752163600089016784868634391278] [19765453835056878739324287395673808223126838, 8372126782390252910789170624462830196756571133, 577488762729029438109158398557764742583123515935, 394405035938727705816060939723899619532199711404667] 21426534828051501105221955584542227587414591 = true := by decide +kernel
theorem trimmedRB010_cells : ∀ c ∈ trimmedRB010.cells,
    |c.1 - trimmedRB010.cB| + c.2.1 ≤ trimmedRB010.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB010.L trimmedRB010.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB010, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 1857313978685668285420755795766140649435117362268210278
        trimmedResidualCap (-704374636544:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB010_c0_ev trimmedRB010_c0_fh trimmedRB010_c0_aa trimmedRB010_c0_mp trimmedRB010_c0_fin⟩
theorem trimmedRB010_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB010 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB010
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB010_blk trimmedRB010_cells
end CatalanMeasure.Improvement.Fields
