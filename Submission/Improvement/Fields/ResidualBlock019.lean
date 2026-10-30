module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedRB019 : Block := ⟨-395136991232, 17179869184, 4, 428784486938722327416602670684633854101790331522021581, [((-395136991232:ℤ),(17179869184:ℤ),0)]⟩
theorem trimmedRB019_blk : decide (PbV D_R.N trimmedRB019.cB trimmedRB019.HB
    (polyValsS D_R trimmedRB019.cB (5+65)) (5+trimmedRB019.L) (65-trimmedRB019.L) MGL_R ≤ trimmedRB019.BB) = true := by decide +kernel
theorem trimmedRB019_c0_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    ((-395136991232:ℚ)/(TT:ℚ)) (-1287830921591014023/9223372036854775808:ℚ) = true := by decide +kernel
theorem trimmedRB019_c0_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles (-395136991232:ℤ)
    (polyValsS D_R (-395136991232:ℤ) (5+4)) 5 = [51091180447929526804983373354146911747, 442705568354884411380704520309820172730, 2619473212638425364722025127224593585145, 24241735030877617006064982240692667285248, 134002972582461121776754745585753928028812] := by decide +kernel
theorem trimmedRB019_c0_aa : AL D_R.N (polyValsS D_R (-395136991232:ℤ) (5+4)) 5 4 = [18280114650752806828119811415683079693537477, 4250181907510589367158125699808994686340120737, 405195174324097079783114431581324136482035680133, 155606358077789274791593829904668713899482193729789] := by decide +kernel
theorem trimmedRB019_c0_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles 5
    ((((-395136991232:ℤ)-(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( -395136991232:ℤ)+(17179869184:ℤ):ℤ):ℚ)/(TT:ℚ)) = 64741023821381628679044000214689661897556729 := by decide +kernel
theorem trimmedRB019_c0_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    5 4 428784486938722327416602670684633854101790331522021581 none trimmedResidualCap (-395136991232,17179869184) (-1287830921591014023/9223372036854775808:ℚ) [51091180447929526804983373354146911747, 442705568354884411380704520309820172730, 2619473212638425364722025127224593585145, 24241735030877617006064982240692667285248, 134002972582461121776754745585753928028812] [18280114650752806828119811415683079693537477, 4250181907510589367158125699808994686340120737, 405195174324097079783114431581324136482035680133, 155606358077789274791593829904668713899482193729789] 64741023821381628679044000214689661897556729 = true := by decide +kernel
theorem trimmedRB019_cells : ∀ c ∈ trimmedRB019.cells,
    |c.1 - trimmedRB019.cB| + c.2.1 ≤ trimmedRB019.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 trimmedRB019.L trimmedRB019.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [trimmedRB019, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl
  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R 5 4 428784486938722327416602670684633854101790331522021581
        trimmedResidualCap (-395136991232:ℤ) (17179869184:ℤ) 0 _ _ _ _ rfl
        trimmedRB019_c0_ev trimmedRB019_c0_fh trimmedRB019_c0_aa trimmedRB019_c0_mp trimmedRB019_c0_fin⟩
theorem trimmedRB019_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    5 65 MGL_R trimmedResidualCap trimmedRB019 = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R 5 65 MGL_R trimmedResidualCap trimmedRB019
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) trimmedRB019_blk trimmedRB019_cells
end CatalanMeasure.Improvement.Fields
