module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB039 : Block := ⟨601295421440, 17179869184, 4, 462520525494007877069355643155763057948318816215213410, [((601295421440:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB039_blk : decide (PbV D_R.N trimmedRB039.cB trimmedRB039.HB
    (polyValsS D_R trimmedRB039.cB (5+65)) (5+trimmedRB039.L) (65-trimmedRB039.L) MGL_R ≤ trimmedRB039.BB) = true := by decide +kernel
theorem trimmedRB039_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((601295421440:ℚ)/(TT:ℚ)) (-5681152919474973353/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB039_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (601295421440:ℤ)
    (polyValsS D_R (601295421440:ℤ) (5+4)) 5 = [-254253063461508638159173690581520919434, 377257874380211617810502332914897741794, -47088098748210140364288308751345157313, 7694458478705774039436773011384982455524, -71072392478586582639347692398880858105489] := by decide +kernel
theorem trimmedRB039_c0_aa : AL D_R.N (polyValsS D_R (601295421440:ℤ) (5+4)) 5 4 = [149472024261931986705115261997328188907816787, 1063602910312537346175200242123814885040217725, 227633940651734708228461414755971850372150374817, 122188400186943114837076307620280479882725712602719] := by decide +kernel
theorem trimmedRB039_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((601295421440:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 601295421440:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 251805810049712659425447716668526895907533137 := by decide +kernel
theorem trimmedRB039_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 462520525494007877069355643155763057948318816215213410 none trimmedResidualCap (601295421440,17179869184) (-5681152919474973353/9223372036854775808:ℚ) [-254253063461508638159173690581520919434, 377257874380211617810502332914897741794, -47088098748210140364288308751345157313, 7694458478705774039436773011384982455524, -71072392478586582639347692398880858105489] [149472024261931986705115261997328188907816787, 1063602910312537346175200242123814885040217725, 227633940651734708228461414755971850372150374817, 122188400186943114837076307620280479882725712602719] 251805810049712659425447716668526895907533137 = true := by decide +kernel
theorem trimmedRB039_cells : ∀ c ∈ trimmedRB039.cells,
    |c.1 - trimmedRB039.cB| + c.2.1 ≤ trimmedRB039.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB039.L trimmedRB039.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB039, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 462520525494007877069355643155763057948318816215213410
        trimmedResidualCap (601295421440:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB039_c0_ev trimmedRB039_c0_fh trimmedRB039_c0_aa trimmedRB039_c0_mp trimmedRB039_c0_fin⟩
theorem trimmedRB039_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB039 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB039
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB039_blk trimmedRB039_cells
end CatalanMeasure.Improvement.Fields
