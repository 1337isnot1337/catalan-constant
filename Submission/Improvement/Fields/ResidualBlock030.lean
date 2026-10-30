module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB030 : Block := ⟨292057776128, 17179869184, 4, 844611847195009324250641081951577302981337001469513645, [((292057776128:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB030_blk : decide (PbV D_R.N trimmedRB030.cB trimmedRB030.HB
    (polyValsS D_R trimmedRB030.cB (5+65)) (5+trimmedRB030.L) (65-trimmedRB030.L) MGL_R ≤ trimmedRB030.BB) = true := by decide +kernel
theorem trimmedRB030_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((292057776128:ℚ)/(TT:ℚ)) (-3265870234154786971/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB030_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (292057776128:ℤ)
    (polyValsS D_R (292057776128:ℤ) (5+4)) 5 = [-402402859713845943344351783555265610284, 933208457903341944234057805653982972928, -6498300667015762349995917455558936223477, 77678247499968689748520219371284094228914, -1319472943581452885023321922850381710554197] := by decide +kernel
theorem trimmedRB030_c0_aa : AL D_R.N (polyValsS D_R (292057776128:ℤ) (5+4)) 5 4 = [75991117319153575614299501712486289465487330, 8816140475979940337510119543735897795974355553, 1749452678206918761727426238781463254977598244524, 120326572231398546886721607990352033469074518956013] := by decide +kernel
theorem trimmedRB030_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((292057776128:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 292057776128:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 885696036966832164427840107024012613890666309 := by decide +kernel
theorem trimmedRB030_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 844611847195009324250641081951577302981337001469513645 none trimmedResidualCap (292057776128,17179869184) (-3265870234154786971/9223372036854775808:ℚ) [-402402859713845943344351783555265610284, 933208457903341944234057805653982972928, -6498300667015762349995917455558936223477, 77678247499968689748520219371284094228914, -1319472943581452885023321922850381710554197] [75991117319153575614299501712486289465487330, 8816140475979940337510119543735897795974355553, 1749452678206918761727426238781463254977598244524, 120326572231398546886721607990352033469074518956013] 885696036966832164427840107024012613890666309 = true := by decide +kernel
theorem trimmedRB030_cells : ∀ c ∈ trimmedRB030.cells,
    |c.1 - trimmedRB030.cB| + c.2.1 ≤ trimmedRB030.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB030.L trimmedRB030.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB030, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 844611847195009324250641081951577302981337001469513645
        trimmedResidualCap (292057776128:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB030_c0_ev trimmedRB030_c0_fh trimmedRB030_c0_aa trimmedRB030_c0_mp trimmedRB030_c0_fin⟩
theorem trimmedRB030_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB030 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB030
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB030_blk trimmedRB030_cells
end CatalanMeasure.Improvement.Fields
