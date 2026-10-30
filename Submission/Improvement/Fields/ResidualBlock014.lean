module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB014 : Block := ⟨-566935683072, 17179869184, 4, 505362261541067330076359706523041764054503565305823615, [((-566935683072:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB014_blk : decide (PbV D_R.N trimmedRB014.cB trimmedRB014.HB
    (polyValsS D_R trimmedRB014.cB (5+65)) (5+trimmedRB014.L) (65-trimmedRB014.L) MGL_R ≤ trimmedRB014.BB) = true := by decide +kernel
theorem trimmedRB014_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-566935683072:ℚ)/(TT:ℚ)) (-2781336703044710351/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB014_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-566935683072:ℤ)
    (polyValsS D_R (-566935683072:ℤ) (5+4)) 5 = [3076564842066759158939403469430343570, 221006300817428572112298732594396918712, 652313475962041358075768013613730221791, 5968602797535628752719479188225381842403, -28392529540872459056067570277224860956724] := by decide +kernel
theorem trimmedRB014_c0_aa : AL D_R.N (polyValsS D_R (-566935683072:ℤ) (5+4)) 5 4 = [19738122976156206799998745933423400748339465, 2516931561774923167179628366816543825283448926, 737319423157438834165409414715120488470724601959, 95252025036180110671727107264628655080213315125565] := by decide +kernel
theorem trimmedRB014_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-566935683072:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -566935683072:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 7652792886944710477587698466489065071635855 := by decide +kernel
theorem trimmedRB014_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 505362261541067330076359706523041764054503565305823615 none trimmedResidualCap (-566935683072,17179869184) (-2781336703044710351/18446744073709551616:ℚ) [3076564842066759158939403469430343570, 221006300817428572112298732594396918712, 652313475962041358075768013613730221791, 5968602797535628752719479188225381842403, -28392529540872459056067570277224860956724] [19738122976156206799998745933423400748339465, 2516931561774923167179628366816543825283448926, 737319423157438834165409414715120488470724601959, 95252025036180110671727107264628655080213315125565] 7652792886944710477587698466489065071635855 = true := by decide +kernel
theorem trimmedRB014_cells : ∀ c ∈ trimmedRB014.cells,
    |c.1 - trimmedRB014.cB| + c.2.1 ≤ trimmedRB014.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB014.L trimmedRB014.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB014, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 505362261541067330076359706523041764054503565305823615
        trimmedResidualCap (-566935683072:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB014_c0_ev trimmedRB014_c0_fh trimmedRB014_c0_aa trimmedRB014_c0_mp trimmedRB014_c0_fin⟩
theorem trimmedRB014_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB014 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB014
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB014_blk trimmedRB014_cells
end CatalanMeasure.Improvement.Fields
