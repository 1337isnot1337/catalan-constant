module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB038 : Block := ⟨566935683072, 17179869184, 4, 359295560000173492225150875011948930510501352865655827, [((566935683072:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB038_blk : decide (PbV D_R.N trimmedRB038.cB trimmedRB038.HB
    (polyValsS D_R trimmedRB038.cB (5+65)) (5+trimmedRB038.L) (65-trimmedRB038.L) MGL_R ≤ trimmedRB038.BB) = true := by decide +kernel
theorem trimmedRB038_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((566935683072:ℚ)/(TT:ℚ)) (-1365196079813040633/2305843009213693952:ℚ) = true := by decide +kernel
theorem trimmedRB038_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (566935683072:ℤ)
    (polyValsS D_R (566935683072:ℤ) (5+4)) 5 = [-266104983742327594889337614588100044574, 382508767291279117784144150572553536752, -287407133895159968419134735379368273201, 8019754447396171043958037350809396235079, -80630646418440153294735656253870724163866] := by decide +kernel
theorem trimmedRB038_c0_aa : AL D_R.N (polyValsS D_R (566935683072:ℤ) (5+4)) 5 4 = [102619596921163354670915271317138444077482008, 1280237286734455251889182064375725167862897530, 236041659007740535059645073177731432197777072348, 98978371746455301509408389047142753892611347970759] := by decide +kernel
theorem trimmedRB038_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((566935683072:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 566935683072:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 169044122229076199189271629692351606779735316 := by decide +kernel
theorem trimmedRB038_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 359295560000173492225150875011948930510501352865655827 none trimmedResidualCap (566935683072,17179869184) (-1365196079813040633/2305843009213693952:ℚ) [-266104983742327594889337614588100044574, 382508767291279117784144150572553536752, -287407133895159968419134735379368273201, 8019754447396171043958037350809396235079, -80630646418440153294735656253870724163866] [102619596921163354670915271317138444077482008, 1280237286734455251889182064375725167862897530, 236041659007740535059645073177731432197777072348, 98978371746455301509408389047142753892611347970759] 169044122229076199189271629692351606779735316 = true := by decide +kernel
theorem trimmedRB038_cells : ∀ c ∈ trimmedRB038.cells,
    |c.1 - trimmedRB038.cB| + c.2.1 ≤ trimmedRB038.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB038.L trimmedRB038.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB038, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 359295560000173492225150875011948930510501352865655827
        trimmedResidualCap (566935683072:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB038_c0_ev trimmedRB038_c0_fh trimmedRB038_c0_aa trimmedRB038_c0_mp trimmedRB038_c0_fin⟩
theorem trimmedRB038_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB038 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB038
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB038_blk trimmedRB038_cells
end CatalanMeasure.Improvement.Fields
