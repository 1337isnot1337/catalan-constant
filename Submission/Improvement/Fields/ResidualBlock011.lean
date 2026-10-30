module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB011 : Block := ⟨-670014898176, 17179869184, 4, 1234419502109776622784314368633612081367609254013382251, [((-670014898176:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB011_blk : decide (PbV D_R.N trimmedRB011.cB trimmedRB011.HB
    (polyValsS D_R trimmedRB011.cB (5+65)) (5+trimmedRB011.L) (65-trimmedRB011.L) MGL_R ≤ trimmedRB011.BB) = true := by decide +kernel
theorem trimmedRB011_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-670014898176:ℚ)/(TT:ℚ)) (-2748147895087962441/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB011_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-670014898176:ℤ)
    (polyValsS D_R (-670014898176:ℤ) (5+4)) 5 = [-15569930647833413987323052602516497668, 184404613447437042075433597729979541864, 162503352207382529773269626079398643069, 4128321736418274716980544464357909670137, -124625736348901287247938161125182128559921] := by decide +kernel
theorem trimmedRB011_c0_aa : AL D_R.N (polyValsS D_R (-670014898176:ℤ) (5+4)) 5 4 = [25956189463558253858805183863616750713033387, 5434995328200213668851349439408384837937904451, 964805789182537134461204664343004864315319384037, 231989711743397011043160517868769212207702707852618] := by decide +kernel
theorem trimmedRB011_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-670014898176:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -670014898176:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 13595572307989487016053201133674163824806284 := by decide +kernel
theorem trimmedRB011_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 1234419502109776622784314368633612081367609254013382251 none trimmedResidualCap (-670014898176,17179869184) (-2748147895087962441/18446744073709551616:ℚ) [-15569930647833413987323052602516497668, 184404613447437042075433597729979541864, 162503352207382529773269626079398643069, 4128321736418274716980544464357909670137, -124625736348901287247938161125182128559921] [25956189463558253858805183863616750713033387, 5434995328200213668851349439408384837937904451, 964805789182537134461204664343004864315319384037, 231989711743397011043160517868769212207702707852618] 13595572307989487016053201133674163824806284 = true := by decide +kernel
theorem trimmedRB011_cells : ∀ c ∈ trimmedRB011.cells,
    |c.1 - trimmedRB011.cB| + c.2.1 ≤ trimmedRB011.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB011.L trimmedRB011.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB011, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 1234419502109776622784314368633612081367609254013382251
        trimmedResidualCap (-670014898176:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB011_c0_ev trimmedRB011_c0_fh trimmedRB011_c0_aa trimmedRB011_c0_mp trimmedRB011_c0_fin⟩
theorem trimmedRB011_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB011 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB011
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB011_blk trimmedRB011_cells
end CatalanMeasure.Improvement.Fields
