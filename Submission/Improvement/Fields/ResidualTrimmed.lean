module

public import Submission.Improvement.Fields.ResidualBlock000
public import Submission.Improvement.Fields.ResidualBlock001
public import Submission.Improvement.Fields.ResidualBlock002
public import Submission.Improvement.Fields.ResidualBlock003
public import Submission.Improvement.Fields.ResidualBlock004
public import Submission.Improvement.Fields.ResidualBlock005
public import Submission.Improvement.Fields.ResidualBlock006
public import Submission.Improvement.Fields.ResidualBlock007
public import Submission.Improvement.Fields.ResidualBlock008
public import Submission.Improvement.Fields.ResidualBlock009
public import Submission.Improvement.Fields.ResidualBlock010
public import Submission.Improvement.Fields.ResidualBlock011
public import Submission.Improvement.Fields.ResidualBlock012
public import Submission.Improvement.Fields.ResidualBlock013
public import Submission.Improvement.Fields.ResidualBlock014
public import Submission.Improvement.Fields.ResidualBlock015
public import Submission.Improvement.Fields.ResidualBlock016
public import Submission.Improvement.Fields.ResidualBlock017
public import Submission.Improvement.Fields.ResidualBlock018
public import Submission.Improvement.Fields.ResidualBlock019
public import Submission.Improvement.Fields.ResidualBlock020
public import Submission.Improvement.Fields.ResidualBlock021
public import Submission.Improvement.Fields.ResidualBlock022
public import Submission.Improvement.Fields.ResidualBlock023
public import Submission.Improvement.Fields.ResidualBlock024
public import Submission.Improvement.Fields.ResidualBlock025
public import Submission.Improvement.Fields.ResidualBlock026
public import Submission.Improvement.Fields.ResidualBlock027
public import Submission.Improvement.Fields.ResidualBlock028
public import Submission.Improvement.Fields.ResidualBlock029
public import Submission.Improvement.Fields.ResidualBlock030
public import Submission.Improvement.Fields.ResidualBlock031
public import Submission.Improvement.Fields.ResidualBlock032
public import Submission.Improvement.Fields.ResidualBlock033
public import Submission.Improvement.Fields.ResidualBlock034
public import Submission.Improvement.Fields.ResidualBlock035
public import Submission.Improvement.Fields.ResidualBlock036
public import Submission.Improvement.Fields.ResidualBlock037
public import Submission.Improvement.Fields.ResidualBlock038
public import Submission.Improvement.Fields.ResidualBlock039
public import Submission.Improvement.Fields.ResidualBlock040
public import Submission.Improvement.Fields.ResidualBlock041
public import Submission.Improvement.Fields.ResidualBlock042
public import Submission.Improvement.Fields.ResidualBlock043
public import Submission.Improvement.Fields.ResidualBlock044
public import Submission.Improvement.Fields.ResidualBlock045
public import Submission.Improvement.Fields.ResidualBlock046
public import Submission.Improvement.Fields.ResidualBlock047
public import Submission.Improvement.Fields.ResidualBlock048
public import Submission.Improvement.Fields.ResidualBlock049
public import Submission.Improvement.Fields.ResidualBlock050
public import Submission.Improvement.Fields.ResidualBlock051
public import Submission.Improvement.Fields.ResidualBlock052
public import Submission.Improvement.Fields.ResidualBlock053

@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan Set
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def trimmedBlocksLeft : List Block := [trimmedRB000, trimmedRB001, trimmedRB002, trimmedRB003, trimmedRB004, trimmedRB005, trimmedRB006, trimmedRB007, trimmedRB008, trimmedRB009, trimmedRB010, trimmedRB011, trimmedRB012, trimmedRB013, trimmedRB014, trimmedRB015, trimmedRB016, trimmedRB017, trimmedRB018, trimmedRB019, trimmedRB020, trimmedRB021, trimmedRB022, trimmedRB023, trimmedRB024]
theorem trimmedBlocksLeft_ok : ∀ b ∈ trimmedBlocksLeft,
    blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 65 MGL_R trimmedResidualCap b = true := by
  intro b hb
  simp only [trimmedBlocksLeft, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trimmedRB000_ok
  · exact trimmedRB001_ok
  · exact trimmedRB002_ok
  · exact trimmedRB003_ok
  · exact trimmedRB004_ok
  · exact trimmedRB005_ok
  · exact trimmedRB006_ok
  · exact trimmedRB007_ok
  · exact trimmedRB008_ok
  · exact trimmedRB009_ok
  · exact trimmedRB010_ok
  · exact trimmedRB011_ok
  · exact trimmedRB012_ok
  · exact trimmedRB013_ok
  · exact trimmedRB014_ok
  · exact trimmedRB015_ok
  · exact trimmedRB016_ok
  · exact trimmedRB017_ok
  · exact trimmedRB018_ok
  · exact trimmedRB019_ok
  · exact trimmedRB020_ok
  · exact trimmedRB021_ok
  · exact trimmedRB022_ok
  · exact trimmedRB023_ok
  · exact trimmedRB024_ok
theorem trimmedBlocksLeft_cover : coverFrom (-19501/100000) (-1059489404526) (blocksCells trimmedBlocksLeft) = true := by
  decide +kernel
theorem trimmed_residual_left (x : ℝ)
    (hxlo : (-2409/2500:ℝ) ≤ x) (hxhi : x ≤ (-19501/100000:ℝ)) :
    resFieldW ((53/58:ℚ):ℝ) (trialSeqS Pc P) x ≤ (trimmedResidualCap:ℝ) := by
  refine field_le_of_blocks _ (resSpecW (53/58:ℚ) Pc P) D_R.toD D_R_ok
    5 65 MGL_R hMGL_R trimmedResidualCap trimmedBlocksLeft
    (fun c _ => trimmed_residual_spec_sound c.2.2) (-1059489404526) (-19501/100000)
    trimmedBlocksLeft_cover trimmedBlocksLeft_ok x ?_ ?_ ?_
  · have hlo : ((-1059489404526:ℤ):ℝ) / TT ≤ (-2409/2500:ℝ) := by norm_num [TT]
    exact hlo.trans hxlo
  · exact_mod_cast hxhi
  · intro c hc pr hp
    simp [resSpecW] at hp
def trimmedBlocksRight : List Block := [trimmedRB025, trimmedRB026, trimmedRB027, trimmedRB028, trimmedRB029, trimmedRB030, trimmedRB031, trimmedRB032, trimmedRB033, trimmedRB034, trimmedRB035, trimmedRB036, trimmedRB037, trimmedRB038, trimmedRB039, trimmedRB040, trimmedRB041, trimmedRB042, trimmedRB043, trimmedRB044, trimmedRB045, trimmedRB046, trimmedRB047, trimmedRB048, trimmedRB049, trimmedRB050, trimmedRB051, trimmedRB052, trimmedRB053]
theorem trimmedBlocksRight_ok : ∀ b ∈ trimmedBlocksRight,
    blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 65 MGL_R trimmedResidualCap b = true := by
  intro b hb
  simp only [trimmedBlocksRight, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trimmedRB025_ok
  · exact trimmedRB026_ok
  · exact trimmedRB027_ok
  · exact trimmedRB028_ok
  · exact trimmedRB029_ok
  · exact trimmedRB030_ok
  · exact trimmedRB031_ok
  · exact trimmedRB032_ok
  · exact trimmedRB033_ok
  · exact trimmedRB034_ok
  · exact trimmedRB035_ok
  · exact trimmedRB036_ok
  · exact trimmedRB037_ok
  · exact trimmedRB038_ok
  · exact trimmedRB039_ok
  · exact trimmedRB040_ok
  · exact trimmedRB041_ok
  · exact trimmedRB042_ok
  · exact trimmedRB043_ok
  · exact trimmedRB044_ok
  · exact trimmedRB045_ok
  · exact trimmedRB046_ok
  · exact trimmedRB047_ok
  · exact trimmedRB048_ok
  · exact trimmedRB049_ok
  · exact trimmedRB050_ok
  · exact trimmedRB051_ok
  · exact trimmedRB052_ok
  · exact trimmedRB053_ok
theorem trimmedBlocksRight_cover : coverFrom (1) (108575673730) (blocksCells trimmedBlocksRight) = true := by
  decide +kernel
theorem trimmed_residual_right (x : ℝ)
    (hxlo : (98749/1000000:ℝ) ≤ x) (hxhi : x ≤ (1:ℝ)) :
    resFieldW ((53/58:ℚ):ℝ) (trialSeqS Pc P) x ≤ (trimmedResidualCap:ℝ) := by
  refine field_le_of_blocks _ (resSpecW (53/58:ℚ) Pc P) D_R.toD D_R_ok
    5 65 MGL_R hMGL_R trimmedResidualCap trimmedBlocksRight
    (fun c _ => trimmed_residual_spec_sound c.2.2) (108575673730) (1)
    trimmedBlocksRight_cover trimmedBlocksRight_ok x ?_ ?_ ?_
  · have hlo : ((108575673730:ℤ):ℝ) / TT ≤ (98749/1000000:ℝ) := by norm_num [TT]
    exact hlo.trans hxlo
  · exact_mod_cast hxhi
  · intro c hc pr hp
    simp [resSpecW] at hp

theorem residual_sup_trimmed_W (x : ℝ) (hx : trimmedResidualSupport x) :
    resFieldW ((53/58:ℚ):ℝ) (trialSeqS Pc P) x ≤ (trimmedResidualCap:ℝ) := by
  rcases hx with h | h
  · exact trimmed_residual_left x h.1 h.2
  · exact trimmed_residual_right x h.1 h.2

theorem residual_sup_trimmed (x : ℝ) (hx : trimmedResidualSupport x) :
    GenD.Analytic.resFieldGen (GenD.Analytic.gRes GenD.D58.Odd.design)
      (trialSeqS Pc P) x ≤ (-883/10000:ℝ) := by
  have h := residual_sup_trimmed_W x hx
  norm_num [resFieldW, GenD.Analytic.resFieldGen, GenD.Analytic.gRes,
    GenD.D58.Odd.design, trimmedResidualCap] at h ⊢
  exact h

end CatalanMeasure.Improvement.Fields

#print axioms CatalanMeasure.Improvement.Fields.residual_sup_trimmed
