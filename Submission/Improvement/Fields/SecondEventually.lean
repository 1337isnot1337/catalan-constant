module

public import Submission.CatalanMeasure.GenD.Analytic.Glue

@[expose] public section

/-! The second-population energy proof only uses its field bounds eventually.
This version replaces the all-positive-scale near-field premise with an
atTop premise. All other hypotheses and the conclusion are unchanged.
The proof and field constructor adapt the upstream Second and Glue modules. -/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric CatalanMeasure.CellCert OAI.InternalCatalan Filter Set
open scoped Topology BigOperators

noncomputable section

/-- Generic second-population trial contract. -/
structure SecondTrialBoundsEventually (P : Parameters) (target residual nearCap cost : ℝ)
    (G : ℝ → Prop) where
  p : ℕ → ℝ
  v : ℕ → ℝ
  MX : ℝ
  MY : ℝ
  normCap : ℝ
  fieldCap : ℝ
  p_summable : Summable (fun j => |p j|)
  v_summable : Summable (fun j => |v j|)
  norm_le : 2 * barrierTrialNormSq p + barrierTrialNormSq v / 2 ≤ normCap
  field_sum : MX + MY = fieldCap
  row : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      populationPhysicalFreeField P N x - 4 * barrierTrialT p x - barrierTrialS v x -
        Real.log (1 - x) / (2 * (P.n N : ℝ)) ≤ MX + ε
  column : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ s ∈ Ioo (0 : ℝ) 1,
      populationEndpointColumnField P N 0 s + 2 * barrierTrialT v s -
        Real.log (1 - s) / (P.n N : ℝ) ≤ MY + ε
  marked : ∀ {N : ℕ}, 0 < N → ∀ {x : ℝ}, x ∈ Icc (-1 : ℝ) 1 → G x →
    groupedMarkedField P N x - 2 * barrierTrialT p x ≤
      residual + Real.log 2 / (P.n N : ℝ)
  near : ∀ᶠ N : ℕ in atTop, ∀ {y : ℝ}, y ∈ Ioo (0 : ℝ) 1 →
    groupedNearField P N y - p 1 * y ≤ nearCap + Real.log 2 / (P.n N : ℝ)
  budget : ∀ {a t : ℝ}, 0 ≤ a → 0 ≤ t →
    (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      normCap + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * residual + t * nearCap ≤
        -target + Real.log 2 / 2 + cost * a

set_option maxHeartbeats 1600000 in
/-- Generic `second_energy_on`: the grouped second-population energy is at most the target. -/
theorem second_energy_eventual {P : Parameters} (hP : Admissible P)
    {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsEventually P target residual nearCap cost G) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = P.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, G (x i)) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (groupedMarkedField P N)
        (groupedNearField P N) (populationPhysicalColumnField P N (a + b))
        z x y s ≤ -target + Real.log 2 / 2 +
          cost * (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) + δ := by
  let ε : ℝ := δ / 4
  have hε : 0 < ε := by dsimp [ε]; linarith only [hδ]
  obtain ⟨e, he, herr⟩ := grouped_error_eventually hP D.p D.v (by linarith : 0 < δ / 2)
  filter_upwards [D.row hε, D.column hε, D.near,
      log_reciprocal_eventually hP hε, herr, eventually_gt_atTop (0 : ℕ)]
    with N hrow hcol hnear hsmall herror hN r a b hcount z x y s hz hz0 hx hxG hy hs hzi hxi hyi hsi
  let ν : ℝ := P.n N
  let α : ℝ := ((a + b : ℕ) : ℝ) / ν
  let β : ℝ := (b : ℝ) / ν
  have hν : 0 < ν := by
    dsimp only [ν]
    exact_mod_cast n_pos hP hN
  have hα : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hν.le
  have hβ : 0 ≤ β := div_nonneg (Nat.cast_nonneg _) hν.le
  have hfree : (r : ℝ) / ν = 1 - α := by
    have hf := population_fractions hP hN (show r + (a + b) = P.n N by omega)
    dsimp only [α, ν]
    linarith only [hf]
  have hmarked : (a : ℝ) / ν = α - β := by
    dsimp only [α, β]
    rw [Nat.cast_add, add_div]
    ring
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hb := grouped_field_caps_bound (constant := groupedConstant P N r a b) hν he
    (by dsimp only [ν]; exact_mod_cast (show r + a ≤ P.n N by omega))
    (by dsimp only [ν]; exact_mod_cast (show b ≤ P.n N by omega)) z x y s hz hx hy' hs hzi hxi hyi hsi
    D.p D.p D.v D.p_summable D.p_summable D.v_summable
    (populationPhysicalFreeField P N) (groupedMarkedField P N)
    (groupedNearField P N) (populationPhysicalColumnField P N (a + b))
    (D.MX + ε) (residual + ε)
    (nearCap + ε) (D.MY + ε + α * Real.log 2)
    (fun i => by
      have hz' : z i ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
        by_cases ht : z i < 0
        · exact Or.inl ⟨(hz i).1.le, ht⟩
        · exact Or.inr ⟨lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm (hz0 i)), (hz i).2⟩
      have hh := hrow (z i) hz'
      linarith only [hh])
    (fun i => by
      have hh := D.marked hN ⟨(hx i).1.le, (hx i).2.le⟩ (hxG i)
      linarith only [hh, hsmall])
    (fun i => by
      have hh := hnear (hy i)
      linarith only [hh, hsmall])
    (fun i => by
      have hh := hcol (s i) (hs i)
      have hl : Real.log (1 + s i) ≤ Real.log 2 :=
        Real.log_le_log (by linarith [(hs i).1]) (by linarith [(hs i).2])
      have hm := mul_le_mul_of_nonneg_left hl hα
      have hid : populationPhysicalColumnField P N (a + b) (s i) =
          populationEndpointColumnField P N 0 (s i) + α * Real.log (1 + s i) := by
        unfold populationPhysicalColumnField populationEndpointColumnField α ν
        ring
      rw [hid]
      linarith only [hh, hm])
  have hconst := grouped_constant_le hP hN hcount
  have hbudget := D.budget hα hβ
  have hnorm := D.norm_le
  have hfields := congrArg (fun t : ℝ => (1 - α) * t) D.field_sum
  have hεα := mul_nonneg hε.le hα
  rw [← n_cast] at herror
  rw [hfree, hmarked] at hb
  rw [hfree] at hconst
  dsimp only [α, β, ν, ε] at hb hconst hbudget hfields hεα ⊢
  ring_nf at hb hconst hbudget hfields hnorm herror hεα ⊢
  nlinarith only [hb, hconst, hbudget, hfields, hnorm, herror, hεα]

/-- **The generic second-energy contract from the three field suprema.** -/
def secondTrialEventually_of_fields {P : Parameters} (hP : Admissible P)
    {target residual cost normCap fieldCap : ℝ} {G : ℝ → Prop}
    (u v : ℕ → ℝ) (hu : Summable (fun k => |u k|)) (hv : Summable (fun k => |v k|))
    (α β γ b q : ℝ) (hα : α = ((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0)
    (hβ : β = 2 * (P.h0 : ℝ) / P.n0)
    (hγ : γ = ((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0)
    (hb : b = (P.b0 : ℝ) / P.n0) (hq : q = (P.q0 : ℝ) / P.n0)
    (MX MY nearCap : ℝ)
    (near_sup : ∀ᶠ N : ℕ in atTop, ∀ {y : ℝ}, y ∈ Ioo (0 : ℝ) 1 →
      groupedNearField P N y - u 1 * y ≤ nearCap + Real.log 2 / (P.n N : ℝ))
    (norm_le : 2 * barrierTrialNormSq u + barrierTrialNormSq v / 2 ≤ normCap)
    (field_sum : MX + MY = fieldCap)
    (row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldG α β γ u v x ≤ MX)
    (column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG b q v s ≤ MY)
    (residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, G x → resFieldGen (gRes P) u x ≤ residual)
    (budget : ∀ {a t : ℝ}, 0 ≤ a → 0 ≤ t →
      (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
        normCap + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 +
        (a - t) * residual + t * nearCap ≤
          -target + Real.log 2 / 2 + cost * a) :
    SecondTrialBoundsEventually P target residual nearCap cost G where
  p := u
  v := v
  MX := MX
  MY := MY
  normCap := normCap
  fieldCap := fieldCap
  p_summable := hu
  v_summable := hv
  norm_le := norm_le
  field_sum := field_sum
  row := by
    intro ε hε
    have hα0 : 0 ≤ α := by
      rw [hα]; have := n0_pos hP; positivity
    have hβ0 : 0 < β := by
      rw [hβ]; have := n0_pos hP; have : (0 : ℝ) < P.h0 := by exact_mod_cast hP.2.2.2.1
      positivity
    have hh := rowFieldG_corrected_eventually (α := α) (β := β) (γ := γ) hu hv hα0 hβ0
      (a := 2) (b := 1 / 2) (by norm_num) (by norm_num) row_sup
      (fun N : ℕ => 1 / ((P.n0 : ℝ) * N))
      (fun N => by have := n0_pos hP; positivity) (invScale_tendsto hP) hε
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc hN x hx
    rw [physical_free_row_identity, param_row_field_eq hP hN]
    have hb' := hc x hx
    rw [rowFieldG_eq, hα, hβ, hγ] at hb'
    linarith only [hb']
  column := by
    intro ε hε
    have hq0 : 0 < q := by
      rw [hq]; have := n0_pos hP; have : (0 : ℝ) < P.q0 := by exact_mod_cast hP.2.2.1
      positivity
    have hb0 : 0 ≤ b := by
      rw [hb]; have := n0_pos hP; positivity
    have hh := colFieldG_corrected_eventually (b := b) (q := q) hv hb0 hq0 column_sup
      (fun N : ℕ => 1 / ((P.n0 : ℝ) * N))
      (fun N => by have := n0_pos hP; positivity) (invScale_tendsto hP) hε
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc hN s hs
    rw [physical_column_identity_gen hP hN]
    have hb' := hc s hs
    unfold colFieldG colRegG at hb'
    rw [hb, hq] at hb'
    simp only [zero_mul, add_zero]
    linarith only [hb']
  marked := by
    intro N hN x hx hgap
    have hn : (0 : ℝ) < P.n N := by exact_mod_cast n_pos hP hN
    have hsq : x ^ 2 ≤ 1 := by nlinarith only [hx.1, hx.2]
    have hlog : Real.log (1 + x ^ 2) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by linarith only [hsq])
    have hcorr := div_le_div_of_nonneg_right hlog hn.le
    have hb' := residual_sup x hx hgap
    unfold resFieldGen at hb'
    rw [grouped_marked_field_identity hP hN]
    linarith only [hb', hcorr]
  near := near_sup
  budget := budget

end
end Analytic
end CatalanMeasure.GenD
