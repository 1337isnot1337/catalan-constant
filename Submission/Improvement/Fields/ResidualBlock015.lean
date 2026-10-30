module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB015 : Block := ⟨-532575944704, 17179869184, 4, 447220497311125791850728201793090612815931638614302295, [((-532575944704:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB015_blk : decide (PbV D_R.N trimmedRB015.cB trimmedRB015.HB
    (polyValsS D_R trimmedRB015.cB (5+65)) (5+trimmedRB015.L) (65-trimmedRB015.L) MGL_R ≤ trimmedRB015.BB) = true := by decide +kernel
theorem trimmedRB015_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-532575944704:ℚ)/(TT:ℚ)) (-86565038893175161/576460752303423488:ℚ) = true := by decide +kernel
theorem trimmedRB015_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-532575944704:ℤ)
    (polyValsS D_R (-532575944704:ℤ) (5+4)) 5 = [10334703819943954308474396784104210234, 244696050991341397705500001696055209803, 875279858164008491678637771270411537043, 7496326543163317598238917108944764187350, -21249303025824676891616347843094035368710] := by decide +kernel
theorem trimmedRB015_c0_aa : AL D_R.N (polyValsS D_R (-532575944704:ℤ) (5+4)) 5 4 = [15761048107359538758464849508964625088468509, 2852499693812047085736858552701886694830022884, 597197221625141611472573619567438918411414082290, 106781263379705726132202060192037862872608622161466] := by decide +kernel
theorem trimmedRB015_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-532575944704:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -532575944704:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 9032653394588813597847479323479141970858183 := by decide +kernel
theorem trimmedRB015_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 447220497311125791850728201793090612815931638614302295 none trimmedResidualCap (-532575944704,17179869184) (-86565038893175161/576460752303423488:ℚ) [10334703819943954308474396784104210234, 244696050991341397705500001696055209803, 875279858164008491678637771270411537043, 7496326543163317598238917108944764187350, -21249303025824676891616347843094035368710] [15761048107359538758464849508964625088468509, 2852499693812047085736858552701886694830022884, 597197221625141611472573619567438918411414082290, 106781263379705726132202060192037862872608622161466] 9032653394588813597847479323479141970858183 = true := by decide +kernel
theorem trimmedRB015_cells : ∀ c ∈ trimmedRB015.cells,
    |c.1 - trimmedRB015.cB| + c.2.1 ≤ trimmedRB015.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB015.L trimmedRB015.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB015, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 447220497311125791850728201793090612815931638614302295
        trimmedResidualCap (-532575944704:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB015_c0_ev trimmedRB015_c0_fh trimmedRB015_c0_aa trimmedRB015_c0_mp trimmedRB015_c0_fin⟩
theorem trimmedRB015_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB015 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB015
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB015_blk trimmedRB015_cells
end CatalanMeasure.Improvement.Fields
