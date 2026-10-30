# Checked inverse-image quadrature

The new quadrature construction is now a Lean theorem. The concrete result is
`CatalanMeasure.GenD.Refinement.Trimmed130.tau_weights` in
`Submission/Refinement/Trimmed130Nodes.lean`:

```lean
GapWeightBounds D58.Odd.design tau weight
```

Here `weight = 52184351 / 1000000 = 52.184351`. The node family has exactly
`53*N` distinct nodes at every scale. The same module proves that each node
is nonzero, lies in `(-1,1)`, and maps into the trimmed residual support under
`realCoordinate`.

This document records the quadrature part of the formal proof. The final
irrationality exponent also uses the separately checked field, determinant,
arithmetic, and prime-selection modules.

## Fixed polynomial and finite certificates

`Trimmed130Data.lean` defines the real polynomial by mapping an explicit list
of 131 rational power coefficients into the reals. `Trimmed130Degree.lean`
proves its degree is exactly 130 and identifies its leading coefficient.

The original witness has 61 inverse branches in the negative band and 69 in
the positive band. Their rational endpoint controls appear in
`Trimmed130BranchData.lean`. Exact endpoint evaluations alternate strictly
below `-1` and above `1`. The finite geometry also proves that the branch
intervals are ordered, disjoint, avoid zero, and lie in

\[
\left[-\frac{12045000}{12053281},
      -\frac{3900200000}{10380289001}\right]
\;\cup\;
\left[\frac{197498000000}{1009751365001},1\right].
\]

All finite signs are checked by Lean's kernel. `IntegerHorner.lean` proves
the homogeneous integer Horner identity used for those checks.
`Trimmed130IntegerData.lean` checks the exact conversion to integer
coefficients with common denominator `10^40`. The 26 modules under
`Submission/Refinement/SignChunks` check ten indices each: thirteen chunks
for the all-level inverse branches, and thirteen for the tighter zero-root
brackets used by the circle proof. The aggregate theorems are
`branch_signs` and `zero_signs`.

This calculation uses neither floating-point arithmetic nor `native_decide`.
The numerical search that selected the polynomial is not a premise.

## Inverse branches and simple roots

`InverseBranches.lean` proves the generic implication from an ordered
alternating-control certificate to a full inverse-branch family. For every
`y` in `[-1,1]`, the intermediate value theorem supplies one root of `P-y`
in each certified open interval. There are 130 distinct roots and the
polynomial has degree 130, so the root list is complete and every root is
simple.

The full preimage of `[-1,1]` lies in the certified real intervals. It is
compact, and `P'` is nonzero on it. The theorem
`InverseBranchCertificate.exists_derivative_lower` therefore supplies a
fixed positive lower bound for `|P'|` on all inverse branches.

The separate tight zero brackets in `Trimmed130ZeroData.lean` yield the
checked factorization

\[
P=\operatorname{lc}(P)\prod_{i=1}^{130}(X-\tau_i).
\]

`Trimmed130ZeroRoots.lean` proves this factorization and the exact rational
location of every `tau_i`. The sharp circle proof uses those locations.

## Exactly 53N interpolation nodes

For a positive scale `N`, put

\[
K=\left\lceil\frac{53N}{130}\right\rceil,
\qquad H_N=T_K(P).
\]

`InverseImageNodes.lean` proves that `H_N` has exactly `130K` distinct roots
in the allowed support. Its derivative at each root is at least `K` times
the fixed positive derivative bound for `P`.

The construction retains the first `53N` roots. At most 129 roots are
removed. `NodalRootDeletion.lean` proves that deleting at most `M` roots in
`(-1,1)` loses at most a factor `2^M` in the derivative lower bound and at
most `(r-1)^(-M)` in the circle norm, for a fixed radius `1<r<=2`. These are
fixed constants, independent of `N`.

## Circle exponent and weight bound

The concrete radius is `r = 100000001/100000000`. The checked sharp circle
theorem is

\[
(2|P(z)|+1)^{53}|1-z|^{780}
\le \exp(130\cdot52.18435),\qquad |z|=r.
\]

`InverseImageCircle.lean` transfers that fixed-degree certificate to
`T_K(P)` at every scale. It raises the desired estimate to the positive
integer power 130, so the proof needs no fractional complex powers or
complex logarithms. The ceiling in `K` costs one additional fixed factor.

`GeneralNodalWeights.lean` applies the existing generic cardinal-polynomial
and coefficient-functional estimates to arbitrary injective nodes.
`InverseImageWeights.lean` combines those estimates with root deletion and
absorbs all fixed factors into any exponent strictly greater than 52.18435.
The concrete choice is 52.184351.

## Support in the energy coordinate

The inverse coordinate is `t=2x/(1+x^2)`. `Trimmed130Support.lean` proves its
strict monotonicity on `(-1,1)` and checks the three rational endpoint
identities. Consequently every retained node maps into

\[
\left[-\frac{2409}{2500},-\frac{19501}{100000}\right]
\;\cup\;
\left[\frac{98749}{1000000},1\right],
\]

which is precisely `trimmedResidualSupport` in the new field estimates.

## Verification status

The generic modules, all 26 finite sign chunks, both concrete root families,
the support map, the sharp circle theorem, and the concrete weight theorem
have compiled with the pinned verifier toolchain.

The axiom audits of the generic weight theorem and the concrete polynomial
factorization report only `propext`, `Classical.choice`, and `Quot.sound`.
There are no admitted lemmas, extra axioms, or native-evaluation axioms in
this construction.
