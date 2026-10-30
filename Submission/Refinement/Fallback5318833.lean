module

public import Submission.Refinement.FinalReal
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Hosts532Inst

@[expose] public section
set_option Elab.async false

/-!
# An unchanged-node refinement to exponent 531.8833

This module retains Sean Litsey's determinant, trial bounds, interpolation
nodes, circle certificate, arithmetic normalizer and packet hosts. It recovers
the exact area of the existing rank profile and uses a smaller fixed PNT error.
No new numerical analytic certificate is assumed.

Source: slitsey/catalan-irrationality-measure,
commit aa2a42f4f3835347ad46608779e22dd52c2dc7bf.
-/

namespace CatalanMeasure.GenD.Refinement

open CatalanMeasure.GenD Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.GenD.Uniform.Bank532

noncomputable section

def fallbackBound : ℝ := 5318833 / 10000
def fallbackEta : ℝ := 300474884 / 10000000
def fallbackRho : ℝ := Uniform.Bank540.rho
def fallbackDelta : ℝ := 1 / 10000000000
def fallbackKappa : ℝ := fallbackBound / fallbackRho

theorem gain532_exact :
    gain532 =
      (36235515874601938601596598 : ℝ) / 1642609663271115992578125 := by
  unfold gain532 wins532
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cw_area]
  norm_num

theorem fallback_pay :
    PayW (3 / 4) 53 fallbackRho fallbackEta fallbackKappa fallbackDelta fallbackBound := by
  norm_num [PayW, fallbackRho, fallbackEta, fallbackKappa, fallbackDelta, fallbackBound,
    Uniform.Bank540.rho, D58.K590.rho, D58.K590.secondCost, D58.wcap]

theorem fallback_decay_margin :
    fallbackEta < Uniform.Bank540.tDelta - gDg gain532 := by
  obtain ⟨hl, hh⟩ := D58.log2_bounds
  rw [gain532_exact]
  unfold Uniform.Bank540.tDelta gDg
  norm_num [fallbackEta, D58.K590.target, D58.lo, D58.hi] at hl hh ⊢
  linarith

theorem catalan_irrationalityMeasure_5318833_of_hosts (H : Hosts532) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(5318833 / 10000 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  have h := measure_of_design_real D58.Odd.design
    { B := fallbackBound
      Z := canonicalNormalizer design D58.Odd.design_admissible (famLB (fams532 H)) 79
        (by rw [D58.Odd.design_H]; norm_num)
      w := 3 / 4
      ρ := fallbackRho
      η := fallbackEta
      κ := fallbackKappa
      δ := fallbackDelta
      pay := by
        rw [D58.n0_sub_g0]
        exact fallback_pay
      gD := gDg gain532
      D_growth := fun ε hε => by
        filter_upwards [partial_growth532 H hε] with N hN
        unfold gDg
        convert hN using 2
      tΔ := Uniform.Bank540.tDelta
      delta_small := Uniform.Bank540.delta_small
      eta_le := fallback_decay_margin
      nonvanishing := D58.nonvanishing_d58 D58.C3.c3_d58 }
  simpa [catalan, fallbackBound] using h

theorem catalan_irrationalityMeasure_5318833 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(5318833 / 10000 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  catalan_irrationalityMeasure_5318833_of_hosts hosts532

end
end CatalanMeasure.GenD.Refinement

#print axioms CatalanMeasure.GenD.Refinement.catalan_irrationalityMeasure_5318833
