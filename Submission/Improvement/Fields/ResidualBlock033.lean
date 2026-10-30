module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB033 : Block := ⟨395136991232, 17179869184, 4, 286726863072621689396410452380939223252288205702332130, [((395136991232:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB033_blk : decide (PbV D_R.N trimmedRB033.cB trimmedRB033.HB
    (polyValsS D_R trimmedRB033.cB (5+65)) (5+trimmedRB033.L) (65-trimmedRB033.L) MGL_R ≤ trimmedRB033.BB) = true := by decide +kernel
theorem trimmedRB033_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((395136991232:ℚ)/(TT:ℚ)) (-4196106622162395215/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB033_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (395136991232:ℤ)
    (polyValsS D_R (395136991232:ℤ) (5+4)) 5 = [-335511381667281749989726845515185746569, 557002489345902557340159613331992292938, -2334194198326099232390688697073560617260, 23836199374471821808589232953332779235125, -330674205151558965898797048963581911138774] := by decide +kernel
theorem trimmedRB033_c0_aa : AL D_R.N (polyValsS D_R (395136991232:ℤ) (5+4)) 5 4 = [17670683005388084928682757943827508772298087, 2729956474188170284401612899843270399298751389, 236378076293790218614529768778388067208064097148, 99720979716477579986803850896893294239231537955811] := by decide +kernel
theorem trimmedRB033_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((395136991232:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 395136991232:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 92313588245243498794046964733286843729024774 := by decide +kernel
theorem trimmedRB033_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 286726863072621689396410452380939223252288205702332130 none trimmedResidualCap (395136991232,17179869184) (-4196106622162395215/9223372036854775808:ℚ) [-335511381667281749989726845515185746569, 557002489345902557340159613331992292938, -2334194198326099232390688697073560617260, 23836199374471821808589232953332779235125, -330674205151558965898797048963581911138774] [17670683005388084928682757943827508772298087, 2729956474188170284401612899843270399298751389, 236378076293790218614529768778388067208064097148, 99720979716477579986803850896893294239231537955811] 92313588245243498794046964733286843729024774 = true := by decide +kernel
theorem trimmedRB033_cells : ∀ c ∈ trimmedRB033.cells,
    |c.1 - trimmedRB033.cB| + c.2.1 ≤ trimmedRB033.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB033.L trimmedRB033.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB033, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 286726863072621689396410452380939223252288205702332130
        trimmedResidualCap (395136991232:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB033_c0_ev trimmedRB033_c0_fh trimmedRB033_c0_aa trimmedRB033_c0_mp trimmedRB033_c0_fin⟩
theorem trimmedRB033_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB033 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB033
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB033_blk trimmedRB033_cells
end CatalanMeasure.Improvement.Fields
