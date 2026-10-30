module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB050 : Block := ⟨979252543488, 17179869184, 4, 26551279763358018081537064569677922029709183257695241818524, [((979252543488:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB050_blk : decide (PbV D_R.N trimmedRB050.cB trimmedRB050.HB
    (polyValsS D_R trimmedRB050.cB (5+65)) (5+trimmedRB050.L) (65-trimmedRB050.L) MGL_R ≤ trimmedRB050.BB) = true := by decide +kernel
theorem trimmedRB050_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((979252543488:ℚ)/(TT:ℚ)) (-14510965618993779697/18446744073709551616:ℚ) = true := by decide +kernel
theorem trimmedRB050_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (979252543488:ℤ)
    (polyValsS D_R (979252543488:ℤ) (5+4)) 5 = [-9628642952447030820310147113784349567, 2296352505827527952723652408257915554159, 38653356107071968109245526261718868518548, 1047790947437427819201513993088658514799182, 20720219129925879028559695393321175472439561] := by decide +kernel
theorem trimmedRB050_c0_aa : AL D_R.N (polyValsS D_R (979252543488:ℤ) (5+4)) 5 4 = [687603066371198854948351900112344065656287772751, 34896927749175817676795289541427704061174161043297, 1905947738322225197160925605198867859285881573010009, 436235310752072168558855404402277132932238941172971698] := by decide +kernel
theorem trimmedRB050_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((979252543488:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( 979252543488:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 2426633554220749850538651463536004772414993313427 := by decide +kernel
theorem trimmedRB050_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 26551279763358018081537064569677922029709183257695241818524 none trimmedResidualCap (979252543488,17179869184) (-14510965618993779697/18446744073709551616:ℚ) [-9628642952447030820310147113784349567, 2296352505827527952723652408257915554159, 38653356107071968109245526261718868518548, 1047790947437427819201513993088658514799182, 20720219129925879028559695393321175472439561] [687603066371198854948351900112344065656287772751, 34896927749175817676795289541427704061174161043297, 1905947738322225197160925605198867859285881573010009, 436235310752072168558855404402277132932238941172971698] 2426633554220749850538651463536004772414993313427 = true := by decide +kernel
theorem trimmedRB050_cells : ∀ c ∈ trimmedRB050.cells,
    |c.1 - trimmedRB050.cB| + c.2.1 ≤ trimmedRB050.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB050.L trimmedRB050.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB050, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 26551279763358018081537064569677922029709183257695241818524
        trimmedResidualCap (979252543488:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB050_c0_ev trimmedRB050_c0_fh trimmedRB050_c0_aa trimmedRB050_c0_mp trimmedRB050_c0_fin⟩
theorem trimmedRB050_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB050 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB050
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB050_blk trimmedRB050_cells
end CatalanMeasure.Improvement.Fields
