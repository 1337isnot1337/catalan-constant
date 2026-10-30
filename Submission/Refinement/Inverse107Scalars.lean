module

public import Submission.Refinement.PreciseLogTwo
public import Submission.Refinement.Fallback5318833

@[expose] public section
set_option Elab.async false

/-! Exact scalar budgets for the indicated node certificate.
The analytic node and residual premises are proved in separate modules.
All constants and numerical comparisons here are exact rationals.
-/

namespace CatalanMeasure.GenD.Refinement.Inverse107

noncomputable section

def target : ℝ := 45117153791 / 20000000000
def secondCost : ℝ := 4288129303 / 1000000000
def weightCap : ℝ := 256487 / 5000
def weight : ℝ := 51297401 / 1000000
def eta : ℝ := 3004363227 / 100000000
def bound : ℝ := 52924599 / 100000
def residualCap : ℝ := -315531 / 5000000
def nearCap : ℝ := -77 / 100
def delta : ℝ := 1 / 10000000000
def omega : ℝ := 3 / 4


def rho : ℝ := 58 * secondCost + weight
def kappa : ℝ := bound / rho
def tDelta : ℝ := 58 ^ 2 * (target - Real.log 2 / 2)

theorem weight_margin : weightCap < weight := by norm_num [weightCap, weight]

theorem first_cost_le : D58.K590.firstCost ≤ secondCost := by
  norm_num [D58.K590.firstCost, secondCost]

theorem first_budget (a : ℝ) :
    (-(D58.c07 - 1 / 2) + (D58.c26 - 1) * a - a ^ 2) * Real.log 2 +
      D58.n1 + (1 - a) * D58.F1 + a * (1 - a) * Real.log 2 + a * D58.Lm ≤
      -target + Real.log 2 / 2 + D58.K590.firstCost * a := by
  have h := D58.K590.first_budget_log2 a
  have ht : target ≤ D58.K590.target := by norm_num [target, D58.K590.target]
  nlinarith

theorem second_budget {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-(D58.c07 - 1 / 2) + (D58.c26 - 1) * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      D58.K590.normCap + (1 - a) * D58.K590.fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * residualCap + t * nearCap ≤
      -target + Real.log 2 / 2 + secondCost * a := by
  obtain ⟨hl, hh⟩ := CatalanMeasure.GenD.Refinement.log_two_bounds
  have h := Budget.second_budget
    (ℓ := Real.log 2) (lo := logTwoLo) (hi := logTwoHi)
    (c07 := D58.c07) (c26 := D58.c26) (res := 0)
    (Nn := D58.K590.normCap) (M := D58.K590.fieldCap)
    (r := residualCap) (nc := nearCap) (T := target) (cost := secondCost)
    (m := -(D58.K590.normCap + D58.K590.fieldCap + target - D58.c07 * logTwoLo))
    (a := a) (t := t)
    (by norm_num [logTwoLo]) hl hh
    (by norm_num [D58.c07]) (by norm_num [D58.c26]) (by norm_num)
    (by norm_num [D58.c26, logTwoHi, logTwoLo, D58.K590.normCap,
      D58.K590.fieldCap, target, D58.c07, residualCap, secondCost])
    (by norm_num [logTwoHi, residualCap, nearCap]) ha ht
  simpa using h

theorem pay : PayW omega 53 rho eta kappa delta bound := by
  norm_num [PayW, omega, rho, eta, kappa, delta, bound, secondCost, weight]

theorem decay_margin :
    eta < tDelta - Uniform.Bank540.Ledger.gDg Uniform.Bank532.gain532 := by
  obtain ⟨hl, hh⟩ := CatalanMeasure.GenD.Refinement.log_two_bounds
  rw [gain532_exact]
  norm_num [eta, tDelta, target, Uniform.Bank540.Ledger.gDg,
    logTwoLo, logTwoHi] at hl hh ⊢
  linarith

theorem bound_nonnegative : 0 ≤ bound := by norm_num [bound]

end
end CatalanMeasure.GenD.Refinement.Inverse107

#print axioms CatalanMeasure.GenD.Refinement.Inverse107.pay
#print axioms CatalanMeasure.GenD.Refinement.Inverse107.second_budget
