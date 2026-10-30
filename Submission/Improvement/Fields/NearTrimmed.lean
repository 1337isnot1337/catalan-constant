module

public import Submission.CatalanMeasure.Cert.FieldEval
public import Submission.CatalanMeasure.CellCert.Scaled
public import Submission.CatalanMeasure.GenD.D58.Cert590.Near
public import Submission.CatalanMeasure.GenD.D58.OddProfile
public import Submission.CatalanMeasure.GenD.Analytic.Glue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# Eventual near-field cap for the trimmed inverse-image support

The coefficient of `log y` is bounded below by `(48 - 10^-6)/58`
for `N >= 10^6`. The exact first trial coefficient exceeds the rational
lower bound used here. A narrow root box certifies the global maximum.
This adapts the upstream D58 near-field monotonicity proof.
-/

namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan Set
noncomputable section

def nearBaseTrimmed (y : ℝ) : ℝ :=
  -(53/58:ℝ)*Real.log (1+y^2)+(47999999/58000000)*Real.log y-(1815069024687/10000000000000)*y

def nearNumTrimmed (y : ℝ) : ℝ :=
  47999999/58000000-(1815069024687/10000000000000)*y-(58000001/58000000)*y^2-(1815069024687/10000000000000)*y^3

theorem near_derivTrimmed {y : ℝ} (hy : 0<y) :
    HasDerivAt nearBaseTrimmed (nearNumTrimmed y/(y*(1+y^2))) y := by
  have hd : 1+y^2≠0 := by positivity
  have hp : HasDerivAt (fun x : ℝ => 1+x^2) (2*y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (1:ℝ)
  have hh := (((hp.log hd).const_mul (-(53/58:ℝ))).add
    ((Real.hasDerivAt_log hy.ne').const_mul (47999999/58000000:ℝ))).sub
    ((hasDerivAt_id y).const_mul (1815069024687/10000000000000:ℝ))
  refine hh.congr_deriv ?_
  unfold nearNumTrimmed
  field_simp
  ring

def nearBoxTermsTrimmed : List LogTerm :=
  [⟨-53/58,0,1+(7758761519/10000000000)^2,0⟩,⟨47999999/58000000,0,7758761520/10000000000,0⟩]

def nearBoxOKTrimmed : Bool :=
  match sumLogs nearBoxTermsTrimmed with
  | some ve => decide (ve.1+ve.2-(1815069024687/10000000000000)*(7758761519/10000000000) ≤ -(781455472/1000000000:ℚ))
  | none => false

theorem near_boxTrimmed :
    -(53/58:ℝ)*Real.log (1+(7758761519/10000000000:ℝ)^2)+
      (47999999/58000000)*Real.log (7758761520/10000000000:ℝ)-(1815069024687/10000000000000)*(7758761519/10000000000) ≤ -(781455472/1000000000:ℝ) := by
  have hc : nearBoxOKTrimmed=true := by decide +kernel
  unfold nearBoxOKTrimmed at hc
  split at hc
  · rename_i ve he
    have hh := sumLogs_spec he
    have hv : (nearBoxTermsTrimmed.map LogTerm.val).sum =
        -(53/58:ℝ)*Real.log (1+(7758761519/10000000000:ℝ)^2)+
          (47999999/58000000)*Real.log (7758761520/10000000000:ℝ) := by
      simp only [nearBoxTermsTrimmed,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rw [realLogTerm (-53/58) (1+(7758761519/10000000000)^2) (by norm_num),
        realLogTerm (47999999/58000000) (7758761520/10000000000) (by norm_num)]
      norm_num
    rw [hv] at hh
    have hq : ve.1+ve.2-(1815069024687/10000000000000:ℚ)*(7758761519/10000000000) ≤ -(781455472/1000000000:ℚ) := of_decide_eq_true hc
    have hr : ((ve.1+ve.2-(1815069024687/10000000000000:ℚ)*(7758761519/10000000000):ℚ):ℝ) ≤ ((-(781455472/1000000000):ℚ):ℝ) := by
      exact_mod_cast hq
    push_cast at hr
    norm_num at hr
    linarith only [(abs_le.mp hh).2,hr]
  · simp at hc

theorem near_numTrimmed_antitone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    nearNumTrimmed y ≤ nearNumTrimmed x := by
  have h2 := pow_le_pow_left₀ hx hxy 2
  have h3 := pow_le_pow_left₀ hx hxy 3
  unfold nearNumTrimmed
  linarith only [hxy,h2,h3]

theorem near_box_dominatesTrimmed {y : ℝ}
    (hy : y ∈ Icc (7758761519/10000000000:ℝ) (7758761520/10000000000:ℝ)) : nearBaseTrimmed y ≤ -(781455472/1000000000:ℝ) := by
  have hpos : 0<y := by linarith only [hy.1]
  have hlog1 : Real.log (1+(7758761519/10000000000:ℝ)^2) ≤ Real.log (1+y^2) :=
    Real.log_le_log (by positivity) (by nlinarith only [hy.1])
  have hlog2 : Real.log y ≤ Real.log (7758761520/10000000000:ℝ) := Real.log_le_log hpos hy.2
  have hh := near_boxTrimmed
  unfold nearBaseTrimmed
  linarith only [hlog1,hlog2,hy.1,hh]

/-- The scale-free near-field cap after the eventual coefficient comparison. -/
theorem near_residual_field_le_trimmed {p y : ℝ} (hp : (1815069024687/10000000000000:ℝ)≤p)
    (hy : 0<y) (_hy1 : y≤1) :
    -(53/58:ℝ)*Real.log (1+y^2)+(47999999/58000000)*Real.log y-p*y ≤ -(781455472/1000000000:ℝ) := by
  have hmono : MonotoneOn nearBaseTrimmed (Ioc (0:ℝ) (7758761519/10000000000:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
    · intro x hx
      exact (near_derivTrimmed hx.1).continuousAt.continuousWithinAt
    · intro x hx
      simp only [interior_Ioc,mem_Ioo] at hx
      exact (near_derivTrimmed hx.1).differentiableAt.differentiableWithinAt
    · intro x hx
      simp only [interior_Ioc,mem_Ioo] at hx
      rw [(near_derivTrimmed hx.1).deriv]
      apply div_nonneg _ (mul_nonneg hx.1.le (by positivity))
      have hh := near_numTrimmed_antitone hx.1.le hx.2.le
      norm_num [nearNumTrimmed] at hh ⊢
      linarith only [hh]
  have hanti : AntitoneOn nearBaseTrimmed (Ici (7758761520/10000000000:ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro x hx
      have hx0 : 0<x := lt_of_lt_of_le (by norm_num : (0:ℝ)<7758761520/10000000000) hx
      exact (near_derivTrimmed hx0).continuousAt.continuousWithinAt
    · intro x hx
      simp only [interior_Ici,mem_Ioi] at hx
      exact (near_derivTrimmed (by linarith only [hx])).differentiableAt.differentiableWithinAt
    · intro x hx
      simp only [interior_Ici,mem_Ioi] at hx
      have hx0 : 0<x := by linarith only [hx]
      rw [(near_derivTrimmed hx0).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (mul_nonneg hx0.le (by positivity))
      have hh := near_numTrimmed_antitone (by norm_num : (0:ℝ)≤7758761520/10000000000) hx.le
      norm_num [nearNumTrimmed] at hh ⊢
      linarith only [hh]
  have hb : nearBaseTrimmed y ≤ -(781455472/1000000000:ℝ) := by
    by_cases ha : y≤7758761519/10000000000
    · exact (hmono ⟨hy,ha⟩ (by norm_num) ha).trans (near_box_dominatesTrimmed (by norm_num))
    · by_cases hc : 7758761520/10000000000≤y
      · exact (hanti (by norm_num) hc hc).trans (near_box_dominatesTrimmed (by norm_num))
      · exact near_box_dominatesTrimmed ⟨le_of_not_ge ha,(le_of_not_ge hc)⟩
  have hpy := mul_le_mul_of_nonneg_right hp hy.le
  unfold nearBaseTrimmed at hb
  linarith only [hb,hpy]

theorem first_lower_trimmed : (1815069024687 / 10000000000000 : ℝ) ≤
    trialSeqS GenD.D58.Cert590.Pc GenD.D58.Cert590.P 1 := by
  rw [GenD.D58.Cert.trialSeqS_one]
  have hq : (1815069024687 / 10000000000000 : ℚ) ≤
      GenD.D58.Cert.firstQ GenD.D58.Cert590.Pc GenD.D58.Cert590.P := by
    unfold GenD.D58.Cert.firstQ
    decide +kernel
  exact_mod_cast hq

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric Filter

theorem near_coeff_trimmed {N : ℕ} (hN : 1000000 ≤ N) :
    (47999999 / 58000000 : ℝ) ≤
      ((D58.Odd.design.n N - 1 - 2 * D58.Odd.design.g N : ℕ) : ℝ) /
        (D58.Odd.design.n N : ℝ) := by
  have hN0 : 0 < N := by omega
  have hNR : (1000000 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : 1 ≤ D58.Odd.design.n N := by
    simp only [Parameters.n, D58.Odd.design]
    omega
  have hg : 2 * D58.Odd.design.g N ≤ D58.Odd.design.n N - 1 := by
    simp only [Parameters.n, Parameters.g, D58.Odd.design]
    omega
  rw [Nat.cast_sub hg, Nat.cast_sub hn]
  simp only [Parameters.n, Parameters.g, D58.Odd.design, Nat.cast_mul, Nat.cast_ofNat]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 58 * N)]
  nlinarith only [hNR]

/-- The direct grouped-field cap, including its positive finite-scale correction. -/
theorem grouped_near_trimmed {N : ℕ} (hN : 10000000 ≤ N) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    groupedNearField D58.Odd.design N y -
      trialSeqS D58.Cert590.Pc D58.Cert590.P 1 * y ≤ -(78145547 / 100000000 : ℝ) := by
  have hN0 : 0 < N := by omega
  have hN1 : 1000000 ≤ N := by omega
  have hn : (0 : ℝ) < D58.Odd.design.n N := by
    exact_mod_cast n_pos D58.Odd.design_admissible hN0
  have hcoef := near_coeff_trimmed hN1
  have hly : Real.log y ≤ 0 := Real.log_nonpos hy.1.le hy.2.le
  have hm := mul_le_mul_of_nonpos_right hcoef hly
  have hb := near_residual_field_le_trimmed first_lower_trimmed hy.1 hy.2.le
  have hsq : y ^ 2 ≤ 1 := by nlinarith only [hy.1, hy.2]
  have hlog : Real.log (1 + y ^ 2) ≤ 1 := by
    have h2 : Real.log 2 ≤ (1 : ℝ) := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [hh]
    exact (Real.log_le_log (by positivity) (by linarith only [hsq])).trans h2
  have hcorr := div_le_div_of_nonneg_right hlog hn.le
  have hNR : (10000000 : ℝ) ≤ N := by exact_mod_cast hN
  have hsmall : 1 / (D58.Odd.design.n N : ℝ) ≤ (2 / 1000000000 : ℝ) := by
    rw [div_le_iff₀ hn]
    simp only [Parameters.n, D58.Odd.design, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hNR]
  unfold groupedNearField
  rw [grouped_marked_field_identity D58.Odd.design_admissible hN0, abs_of_pos hy.1]
  norm_num [gRes, D58.Odd.design] at hb ⊢
  linarith only [hb, hm, hcorr, hsmall]

theorem grouped_near_trimmed_eventually :
    ∀ᶠ N : ℕ in atTop, ∀ y ∈ Ioo (0 : ℝ) 1,
      groupedNearField D58.Odd.design N y -
        trialSeqS D58.Cert590.Pc D58.Cert590.P 1 * y ≤ -(78145547 / 100000000 : ℝ) := by
  filter_upwards [eventually_ge_atTop (10000000 : ℕ)] with N hN y hy
  exact grouped_near_trimmed hN hy

end CatalanMeasure.Improvement.Fields
