module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB031 : Block := ⟨326417514496, 17179869184, 4, 478106725979904769963393492603831629902496632099969965, [((326417514496:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB031_blk : decide (PbV D_R.N trimmedRB031.cB trimmedRB031.HB
    (polyValsS D_R trimmedRB031.cB (5+65)) (5+trimmedRB031.L) (65-trimmedRB031.L) MGL_R ≤ trimmedRB031.BB) = true := by decide +kernel
theorem trimmedRB031_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((326417514496:ℚ)/(TT:ℚ)) (-3595187096710288695/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB031_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (326417514496:ℤ)
    (polyValsS D_R (326417514496:ℤ) (5+4)) 5 = [-376058450616275179110761041608236553625, 763089527794466501935088052052078711443, -4526675164794010217170660771681851331860, 50015474340689785662965861852011166987233, -772118044873988570304448495847844100549656] := by decide +kernel
theorem trimmedRB031_c0_aa : AL D_R.N (polyValsS D_R (326417514496:ℤ) (5+4)) 5 4 = [23007459349631767111858818681770976861998385, 4454693954125133440143857619850279668150933163, 882847330555811558562916305849116301320389678500, 106688574133801166652126539192962070608315008663872] := by decide +kernel
theorem trimmedRB031_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((326417514496:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 326417514496:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 329152004015631391476870737765964732418620028 := by decide +kernel
theorem trimmedRB031_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 478106725979904769963393492603831629902496632099969965 none trimmedResidualCap (326417514496,17179869184) (-3595187096710288695/9223372036854775808:ℚ) [-376058450616275179110761041608236553625, 763089527794466501935088052052078711443, -4526675164794010217170660771681851331860, 50015474340689785662965861852011166987233, -772118044873988570304448495847844100549656] [23007459349631767111858818681770976861998385, 4454693954125133440143857619850279668150933163, 882847330555811558562916305849116301320389678500, 106688574133801166652126539192962070608315008663872] 329152004015631391476870737765964732418620028 = true := by decide +kernel
theorem trimmedRB031_cells : ∀ c ∈ trimmedRB031.cells,
    |c.1 - trimmedRB031.cB| + c.2.1 ≤ trimmedRB031.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB031.L trimmedRB031.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB031, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 478106725979904769963393492603831629902496632099969965
        trimmedResidualCap (326417514496:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB031_c0_ev trimmedRB031_c0_fh trimmedRB031_c0_aa trimmedRB031_c0_mp trimmedRB031_c0_fin⟩
theorem trimmedRB031_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB031 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB031
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB031_blk trimmedRB031_cells
end CatalanMeasure.Improvement.Fields
