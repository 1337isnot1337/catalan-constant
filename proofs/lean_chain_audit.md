# Lean chain audit for 528.23288

This note records an independent source and interface review of the theorem
chain from the degree-130 nodes to `Race.bound`. The whole-project kernel
build and the verifier's submission checks were still pending when this
review was completed. This review does not substitute for those checks.
The review found no mismatch in the constants, support coordinate, eventual
quantifiers, arithmetic normalizer, or target definition.

## The exact analytic rates

`Trimmed130Scalars.lean` defines

\[
\begin{aligned}
U&=\frac{28198220921}{12500000000},\\
c_2&=\frac{852585263}{200000000},\\
w&=\frac{52184351}{1000000}=52.184351,\\
\rho&=58c_2+w=299.43407727,\\
t_\Delta&=58^2\left(U-\frac{\log 2}{2}\right),\\
\eta&=\frac{3004357889}{100000000}=30.04357889.
\end{aligned}
\]

The sharp circle cap is `52.18435`, strictly smaller than `w`.
`tau_weights` includes the passage from the circle cap to `w`, with all
fixed interpolation and root-deletion factors absorbed into that strict
margin. No extra factor of 58 belongs in the weight term.

`delta_small_of_eventual_trials` uses a sheet cost `r` and a weight cost
`w`, and produces the approximation radius `exp(-(r+w)*N)`.
`Trimmed130Decay.delta_small` instantiates `r = 58*c_2`, so its radius is
definitionally the `rho` consumed by `Trimmed130Measure`. The target in
the grouped energy is exactly the `U` in `tDelta`; the normalization by
`58^2` is retained through the determinant estimate.

## Support and eventual hypotheses

The polynomial controls locate the interpolation variable `t` in two
closed rational bands inside `[-1,1]`. Every selected node is also proved
to lie in the open interval `(-1,1)` and to be nonzero.
`Trimmed130Support.coordinate_mem_trimmedSupport` transports the bands
under `realCoordinate`. The energy theorem receives the support condition
on `realCoordinate (tau N i)`, exactly as required by `WeightedAtomPoint`.
It never substitutes the untransformed interpolation coordinate for the
energy coordinate.

The near-field comparison uses `N >= 10^6` for the logarithmic coefficient
and `N >= 10^7` for the final grouped field. The latter includes the
positive finite-scale correction `log(1+y^2)/(58*N)`. The resulting cap is
`-0.78145547`. The concrete second trial weakens that direct bound by
adding the nonnegative inherited allowance `log(2)/(58*N)`.

`SecondTrialBoundsEventually` places the eventual quantifier before the
universal quantifier over `y`. `second_energy_eventual` intersects this
tail with all other error and positivity tails before introducing the
populations and configurations. `delta_small` likewise has the form

`∀ ε > 0, ∀ᶠ N, ∀ x, ...`.

Thus the thresholds are uniform in the points and configurations. Only
their allowed dependence on `epsilon` remains.

## Arithmetic normalization and exponent transfer

The determinant and the admissible design remain the original
`D58.Odd.design`. The normalizer uses the concrete `hosts532` and its
existing packet-rank proof. `gain532_exact` identifies the exact profile
area with the rational `exactProfileGain` used by the scalar calculation.
The denominator exponent is

\[
g_D=\frac{24733}{4}+\frac{2673}{8}\log 2
-\frac{36235515874601938601596598}
       {1642609663271115992578125}.
\]

The scalar theorem proves the strict inequality `eta < tDelta - gD`.
`FinalReal` retains the original factorial normalization, denominator
growth, coefficient divisibility and prime-square nonvanishing steps.
Its only interface extension is allowing the target exponent `B` to be
real; the underlying recycled-polynomial criterion already permits a
real exponent. In particular, the nonvanishing hypothesis still covers
every integer numerator and every positive denominator not divisible by
the selected prime square.

The payment theorem uses `omega = 3/4`, `delta = 10^-10`, and
`kappa = bound/rho`. Its first equality is exactly
`rho*kappa = bound`; all the strict window and payment inequalities are
proved for these rational choices.

## Canonical statement and closed entrypoint

`OAI.InternalCatalan.catalan` and `BigOSpeedrun.Catalan.constant` have the
same literal definition:

\[
\sum_{j=0}^{\infty}\frac{(-1)^j}{(2j+1)^2}.
\]

The endpoint theorem gives a strict approximation inequality, uniformly
over every integer numerator, for all sufficiently large natural
denominators. `EndpointBridge` obtains every larger exponent by
monotonicity of the real power for denominators at least one. No fraction
is excluded and no reduced-fraction hypothesis is introduced.

The final declaration is the closed theorem

```lean
theorem Race.bound :
  BigOSpeedrun.Catalan.Bound ((6602911 : ℚ) / 12500)
```

Its proof supplies `Trimmed130Decay.delta_small` to
`Trimmed130Measure.verifier_bound_of_decay`; no analytic hypothesis
remains in the entrypoint.

A source scan of the new refinement and improvement modules found no
admitted lemmas, extra axioms, or `native_decide` calls. The generic and
concrete quadrature axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. The final entrypoint also prints its
axioms so the completed build checks the whole dependency chain.
