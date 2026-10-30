module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB034 : Block := ⟨429496729600, 17179869184, 4, 219129039295503321916493128671850799125317075473432855, [((429496729600:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB034_blk : decide (PbV D_R.N trimmedRB034.cB trimmedRB034.HB
    (polyValsS D_R trimmedRB034.cB (5+65)) (5+trimmedRB034.L) (65-trimmedRB034.L) MGL_R ≤ trimmedRB034.BB) = true := by decide +kernel
theorem trimmedRB034_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((429496729600:ℚ)/(TT:ℚ)) (-8946443632980280339/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB034_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (429496729600:ℤ)
    (polyValsS D_R (429496729600:ℤ) (5+4)) 5 = [-319133339826193181747173375014330213127, 494521974212620309317054569766710944652, -1694075686339379510703287669323540863516, 17475698644948495845737347443112255501421, -232564519540119858420325754996739197744637] := by decide +kernel
theorem trimmedRB034_c0_aa : AL D_R.N (polyValsS D_R (429496729600:ℤ) (5+4)) 5 4 = [25099348000971279572180626857700108638569539, 2352261692425485045117830390358880264321999484, 77734865950555296733415129017967120555759941345, 94416991648085972097299406892830721375764173346720] := by decide +kernel
theorem trimmedRB034_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((429496729600:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 429496729600:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 72750938842446735788810241066574251819118582 := by decide +kernel
theorem trimmedRB034_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 219129039295503321916493128671850799125317075473432855 none trimmedResidualCap (429496729600,17179869184) (-8946443632980280339/18446744073709551616:ℚ) [-319133339826193181747173375014330213127, 494521974212620309317054569766710944652, -1694075686339379510703287669323540863516, 17475698644948495845737347443112255501421, -232564519540119858420325754996739197744637] [25099348000971279572180626857700108638569539, 2352261692425485045117830390358880264321999484, 77734865950555296733415129017967120555759941345, 94416991648085972097299406892830721375764173346720] 72750938842446735788810241066574251819118582 = true := by decide +kernel
theorem trimmedRB034_cells : ∀ c ∈ trimmedRB034.cells,
    |c.1 - trimmedRB034.cB| + c.2.1 ≤ trimmedRB034.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB034.L trimmedRB034.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB034, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 219129039295503321916493128671850799125317075473432855
        trimmedResidualCap (429496729600:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB034_c0_ev trimmedRB034_c0_fh trimmedRB034_c0_aa trimmedRB034_c0_mp trimmedRB034_c0_fin⟩
theorem trimmedRB034_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB034 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB034
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB034_blk trimmedRB034_cells
end CatalanMeasure.Improvement.Fields
