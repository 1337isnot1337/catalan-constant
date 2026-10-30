module

public import Submission.Improvement.Fields.SecondEventually
public import Submission.CatalanMeasure.GenD.Analytic.DeltaChain

@[expose] public section

/-! Transfer of the eventual near-field contract through the grouped product,
marked sheet, weighted atoms and determinant smallness. The proofs are the
upstream transformations, with the eventual second-energy theorem substituted.
No symmetry or central-gap assumption is imposed on the support predicate. -/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter Polynomial
open scoped BigOperators Topology
noncomputable section

set_option maxHeartbeats 1600000 in
/-- Generic `grouped_marked_product_on`: the grouped physical product is at most
`exp((n0 N)² (-target + log 2/2 + ε) + (n0 · cost) N (a+b))`. -/
theorem grouped_marked_product_eventual {P : Parameters} (hP : Admissible P)
    {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsEventually P target residual nearCap cost G) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (r a b : ℕ), r + a + b = P.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, G (x i)) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      groupedProduct P N z x y s ≤
        Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          ((P.n0 : ℝ) * cost) * N * (a + b)) := by
  filter_upwards [second_energy_eventual hP D hε, eventually_gt_atTop (0 : ℕ)]
    with N he hN r a b hcount z x y s hz hz0 hx hxG hy hs hzi hxi hyi hsi
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hy0 : ∀ i, y i ≠ 0 := fun i => (hy i).1.ne'
  have hlog := log_groupedProduct hP hN z x y s
    hz hx hy' hs hz0 hy0 hzi hxi hyi hsi
  have hval := he r a b hcount z x y s hz hz0 hx hxG hy hs hzi hxi hyi hsi
  have hn : (P.n N : ℝ) = (P.n0 : ℝ) * N := n_cast P N
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : (P.n N : ℝ) ^ 2 *
      (-target + Real.log 2 / 2 + cost * (((a + b : ℕ) : ℝ) / P.n N) + ε) =
      ((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
        ((P.n0 : ℝ) * cost) * N * (a + b) := by
    rw [hn, Nat.cast_add]
    field_simp
    ring
  have hbound := mul_le_mul_of_nonneg_left hval (sq_nonneg (P.n N : ℝ))
  rw [← hlog, hid] at hbound
  have hpos : 0 < groupedProduct P N z x y s := by
    have hS : 0 < (∏ i, (1 + s i)) ^ (a + b) :=
      pow_pos (prod_pos fun i _ => by linarith [(hs i).1]) _
    have hZ : 0 < ∏ i, |z i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) :=
      prod_pos fun i _ => zpow_pos (abs_pos.mpr (hz0 i)) _
    have hX : 0 < ∏ i, markedSheetWeight P N (x i) :=
      prod_pos fun i _ => markedSheetWeight_pos P N _
    have hY : 0 < ∏ i, markedSheetWeight P N (y i) *
        |y i| ^ (P.n N - 1 - 2 * P.g N) :=
      prod_pos fun i _ => mul_pos (markedSheetWeight_pos P N _)
        (pow_pos (abs_pos.mpr (hy0 i)) _)
    have hPair := groupedPairProduct_pos (Fin.append z x) y
        (fun i => abs_lt.mpr (Fin.addCases (fun j => by simpa using hz j)
          (fun j => by simpa using hx j) i)) (fun i => abs_lt.mpr (hy' i)) hxi hyi
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hS hZ) hX) hY) hPair)
      (paramPinPrincipal_pos hP hN z s hz hs hz0 hzi hsi)
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr hbound

theorem marked_sheet_on_eventual {P : Parameters} (hP : Admissible P)
    {target c residual nearCap cost r : ℝ}
    (F : FirstTrialBounds P target c) (G : ℝ → Prop)
    (D : SecondTrialBoundsEventually P target residual nearCap cost G)
    (hfc : (P.n0 : ℝ) * c ≤ r) (hsc : (P.n0 : ℝ) * cost ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) →
      Function.Injective s →
      markedSheetProduct P N hpm x y s ≤
        (5 : ℝ) ^ m * sheetPrefactor P N *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            r * N * m) := by
  filter_upwards [first_marked_sheet hP F hε,
      second_marked_sheet_product_on hP target ((P.n0 : ℝ) * cost) G
        (fun _ he => grouped_marked_product_eventual hP D he) hε] with N hfirst hsecond
  intro p m hpm x y s hx hx0 hy hy0 hGy hs hzi hsi
  have hxi : Function.Injective x := by
    intro i j hij
    exact Fin.castAdd_injective _ _ (hzi (by simpa using hij))
  have h5 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
  have hH : 0 ≤ sheetPrefactor P N := by unfold sheetPrefactor; positivity
  have hF : (3 / 2 : ℝ) ^ P.n N *
      (P.n N : ℝ) ^ ((P.n N : ℝ) / 2) ≤ sheetPrefactor P N := by
    unfold sheetPrefactor
    exact le_add_of_nonneg_right (by positivity)
  have hI : (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N ≤
      sheetPrefactor P N := by
    unfold sheetPrefactor
    exact le_add_of_nonneg_left (by positivity)
  by_cases hcase : -1 < ∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)
  · have hh := hfirst p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
    apply hh.trans
    apply mul_le_mul
    · exact hF.trans (le_mul_of_one_le_left hH h5)
    · apply Real.exp_le_exp.mpr
      have hNm : (0 : ℝ) ≤ N * m := by positivity
      nlinarith only [mul_le_mul_of_nonneg_right hfc hNm]
    · exact (Real.exp_pos _).le
    · positivity
  · have hh := hsecond p m hpm x y s hx hx0 hy hy0 hGy hs hzi hsi (le_of_not_gt hcase)
    apply hh.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hI (pow_nonneg (by norm_num) _)
    · apply Real.exp_le_exp.mpr
      have hNm : (0 : ℝ) ≤ N * m := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      nlinarith only [mul_le_mul_of_nonneg_right hsc hNm]
    · exact (Real.exp_pos _).le
    · positivity

/-- Determinant decay for arbitrary admissible quadrature nodes. -/
theorem delta_small_of_eventual_trials {P : Parameters} (hP : Admissible P)
    {target c residual nearCap cost r w tΔ : ℝ}
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Ioo (-1 : ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i)))
    (F : FirstTrialBounds P target c)
    (D : SecondTrialBoundsEventually P target residual nearCap cost G)
    (hweights : GapWeightBounds P τ w)
    (hfc : (P.n0 : ℝ) * c ≤ r) (hsc : (P.n0 : ℝ) * cost ≤ r)
    (hT : tΔ = (P.n0 : ℝ) ^ 2 * (target - Real.log 2 / 2)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-((r + w) * (N : ℝ))) →
        |aeval x (deltaPoly P N)| ≤ Real.exp (-((tΔ - ε) * (N : ℝ) ^ 2)) := by
  have hpoint : WeightedAtomPoint P τ G target (r + w) :=
    weighted_atom_point_of_sheet P hP τ G
      (fun ε hε => marked_sheet_on_eventual hP F G D hfc hsc hε) hweights
  exact delta_small P hP τ G hτinj hτmem hτzero hτG target (r + w) tΔ hT hpoint

end
end Analytic
end CatalanMeasure.GenD

#print axioms CatalanMeasure.GenD.Analytic.delta_small_of_eventual_trials
