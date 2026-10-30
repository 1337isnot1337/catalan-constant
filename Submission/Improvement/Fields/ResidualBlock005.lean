module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB005 : Block := ⟨-876173328384, 17179869184, 4, 66327175684356772932343391704424735826127121045857764645, [((-876173328384:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB005_blk : decide (PbV D_R.N trimmedRB005.cB trimmedRB005.HB
    (polyValsS D_R trimmedRB005.cB (5+65)) (5+trimmedRB005.L) (65-trimmedRB005.L) MGL_R ≤ trimmedRB005.BB) = true := by decide +kernel
theorem trimmedRB005_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-876173328384:ℚ)/(TT:ℚ)) (-602559104289613429/4611686018427387904:ℚ) = true := by decide +kernel
theorem trimmedRB005_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-876173328384:ℤ)
    (polyValsS D_R (-876173328384:ℤ) (5+4)) 5 = [-52868102850098249503080926916045720597, 251854020215326040546344044522301001965, -1161403201428332303036500112232628303640, 15259388371284335671770427139302617244150, -1102887100491017364972552455156190826220008] := by decide +kernel
theorem trimmedRB005_c0_aa : AL D_R.N (polyValsS D_R (-876173328384:ℤ) (5+4)) 5 4 = [355019757069284898496244591036936949431746173, 54768689902804154559703527797084187200605073205, 6239546197807726082723874405916888647426702780348, 4521020072457522592756677629037065261622708575330397] := by decide +kernel
theorem trimmedRB005_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-876173328384:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -876173328384:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 752292444271537827991700221756988290795358047 := by decide +kernel
theorem trimmedRB005_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 66327175684356772932343391704424735826127121045857764645 none trimmedResidualCap (-876173328384,17179869184) (-602559104289613429/4611686018427387904:ℚ) [-52868102850098249503080926916045720597, 251854020215326040546344044522301001965, -1161403201428332303036500112232628303640, 15259388371284335671770427139302617244150, -1102887100491017364972552455156190826220008] [355019757069284898496244591036936949431746173, 54768689902804154559703527797084187200605073205, 6239546197807726082723874405916888647426702780348, 4521020072457522592756677629037065261622708575330397] 752292444271537827991700221756988290795358047 = true := by decide +kernel
theorem trimmedRB005_cells : ∀ c ∈ trimmedRB005.cells,
    |c.1 - trimmedRB005.cB| + c.2.1 ≤ trimmedRB005.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB005.L trimmedRB005.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB005, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 66327175684356772932343391704424735826127121045857764645
        trimmedResidualCap (-876173328384:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB005_c0_ev trimmedRB005_c0_fh trimmedRB005_c0_aa trimmedRB005_c0_mp trimmedRB005_c0_fin⟩
theorem trimmedRB005_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB005 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB005
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB005_blk trimmedRB005_cells
end CatalanMeasure.Improvement.Fields
