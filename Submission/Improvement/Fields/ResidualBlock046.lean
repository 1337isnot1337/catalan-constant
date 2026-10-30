module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB046 : Block := ⟨841813590016, 17179869184, 4, 28789692953646438261215108509031417095856495031372672677, [((841813590016:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB046_blk : decide (PbV D_R.N trimmedRB046.cB trimmedRB046.HB
    (polyValsS D_R trimmedRB046.cB (5+65)) (5+trimmedRB046.L) (65-trimmedRB046.L) MGL_R ≤ trimmedRB046.BB) = true := by decide +kernel
theorem trimmedRB046_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((841813590016:ℚ)/(TT:ℚ)) (-3461596377997549045/4611686018427387904:ℚ) = true := by decide +kernel
theorem trimmedRB046_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (841813590016:ℤ)
    (polyValsS D_R (841813590016:ℤ) (5+4)) 5 = [-155833622410624296100718008066535779976, 646424462354023693046637643227341724523, 3824327386130415063713627192880395260375, 52996678799941540755063470932747582510649, 296680480712040893573283905857601370722991] := by decide +kernel
theorem trimmedRB046_c0_aa : AL D_R.N (polyValsS D_R (841813590016:ℤ) (5+4)) 5 4 = [7487320077578008110565253937780429938648844906, 153023962265988947878007928350237727417788867975, 2684523836981005605337518043548422131644328507213, 2210592189354364542870196683856575964792798436686636] := by decide +kernel
theorem trimmedRB046_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((841813590016:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 841813590016:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 15679821736185602818083523614759716296848171811 := by decide +kernel
theorem trimmedRB046_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 28789692953646438261215108509031417095856495031372672677 none trimmedResidualCap (841813590016,17179869184) (-3461596377997549045/4611686018427387904:ℚ) [-155833622410624296100718008066535779976, 646424462354023693046637643227341724523, 3824327386130415063713627192880395260375, 52996678799941540755063470932747582510649, 296680480712040893573283905857601370722991] [7487320077578008110565253937780429938648844906, 153023962265988947878007928350237727417788867975, 2684523836981005605337518043548422131644328507213, 2210592189354364542870196683856575964792798436686636] 15679821736185602818083523614759716296848171811 = true := by decide +kernel
theorem trimmedRB046_cells : ∀ c ∈ trimmedRB046.cells,
    |c.1 - trimmedRB046.cB| + c.2.1 ≤ trimmedRB046.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB046.L trimmedRB046.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB046, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 28789692953646438261215108509031417095856495031372672677
        trimmedResidualCap (841813590016:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB046_c0_ev trimmedRB046_c0_fh trimmedRB046_c0_aa trimmedRB046_c0_mp trimmedRB046_c0_fin⟩
theorem trimmedRB046_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB046 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB046
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB046_blk trimmedRB046_cells
end CatalanMeasure.Improvement.Fields
