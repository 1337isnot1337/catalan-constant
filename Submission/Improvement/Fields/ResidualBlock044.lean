module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB044 : Block := ⟨773094113280, 17179869184, 4, 5205951662869955086080046255223672526212223983047834423, [((773094113280:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB044_blk : decide (PbV D_R.N trimmedRB044.cB trimmedRB044.HB
    (polyValsS D_R trimmedRB044.cB (5+65)) (5+trimmedRB044.L) (65-trimmedRB044.L) MGL_R ≤ trimmedRB044.BB) = true := by decide +kernel
theorem trimmedRB044_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((773094113280:ℚ)/(TT:ℚ)) (-6628444777190732121/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB044_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (773094113280:ℤ)
    (polyValsS D_R (773094113280:ℤ) (5+4)) 5 = [-190461843841552427570398101147869791530, 483085987409538023058681091880323388144, 1719442423522171118894483932624344167285, 20708062905483202177857808811576924369171, 475282278228993361825755303817249874100812] := by decide +kernel
theorem trimmedRB044_c0_aa : AL D_R.N (polyValsS D_R (773094113280:ℤ) (5+4)) 5 4 = [1773694562578871240347001338080192232954105872, 47948225800823817426981437498076753600102794547, 2864913608819627324840554218268481790344295991547, 583082782758275465640447772158858843301929393381020] := by decide +kernel
theorem trimmedRB044_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((773094113280:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 773094113280:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 3496164208377095049424335777352052899298324706 := by decide +kernel
theorem trimmedRB044_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 5205951662869955086080046255223672526212223983047834423 none trimmedResidualCap (773094113280,17179869184) (-6628444777190732121/9223372036854775808:ℚ) [-190461843841552427570398101147869791530, 483085987409538023058681091880323388144, 1719442423522171118894483932624344167285, 20708062905483202177857808811576924369171, 475282278228993361825755303817249874100812] [1773694562578871240347001338080192232954105872, 47948225800823817426981437498076753600102794547, 2864913608819627324840554218268481790344295991547, 583082782758275465640447772158858843301929393381020] 3496164208377095049424335777352052899298324706 = true := by decide +kernel
theorem trimmedRB044_cells : ∀ c ∈ trimmedRB044.cells,
    |c.1 - trimmedRB044.cB| + c.2.1 ≤ trimmedRB044.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB044.L trimmedRB044.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB044, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 5205951662869955086080046255223672526212223983047834423
        trimmedResidualCap (773094113280:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB044_c0_ev trimmedRB044_c0_fh trimmedRB044_c0_aa trimmedRB044_c0_mp trimmedRB044_c0_fin⟩
theorem trimmedRB044_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB044 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB044
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB044_blk trimmedRB044_cells
end CatalanMeasure.Improvement.Fields
