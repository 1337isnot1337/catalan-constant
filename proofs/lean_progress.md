# Lean formalization progress

The target is `BigOSpeedrun.Catalan.Bound (6602911 / 12500)`, representing
the upper bound 528.23288. There is not yet a completed unconditional
`Race.bound` theorem or a verifier submission issue.

## Compiled components

The following new components compile under Lean 4.34.1 with the verifier's
Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`:

- The real-exponent determinant criterion, `FinalReal`.
- The bridge to the verifier's unchanged canonical Catalan statement.
- An exact rational enclosure for log 2.
- General nodal-weight estimates and deletion of surplus roots.
- Inverse branches, Chebyshev compositions, and the full inverse-image
  quadrature weight theorem.
- Rational polynomial evaluation, degree, leading coefficient, and norm tools.
- The degree-130 polynomial data and tight rational zero brackets.
- Global tangent inequalities for products of positive affine factors.
- All three finite tangent-circle comparisons in `Sharp130Finite`.
- All 130 tight root enclosures, their polynomial factorization, and the
  complete complex-circle bound in `Sharp130Circle`.
- The exact scalar budget for the target 528.23288.
- The eventual grouped near-field bound, including the correction at
  finite scale and the threshold N >= 10^7.
- The second-energy argument with this eventual near-field hypothesis.
- The complete concrete degree-130 quadrature, including all level signs,
  the trimmed coordinate support, and weights at exponent 52.184351.

The finite comparisons use kernel reduction (`decide +kernel`). The printed
axioms for the complete circle bound, real exponential bound, and factor positivity theorem are
`propext`, `Classical.choice`, and `Quot.sound`.

The circle certificate is recorded in `certificates/root_tangent_130.json`.
It proves the same weight cap 52.18435 as the earlier Bernstein certificate.
It encloses all 130 roots by rational sign tests, bounds squared distances by
positive affine functions of the real part, and uses three product tangents.
The generic inequality follows from `1 + t ≤ exp t`.

## Remaining assembly

The trimmed residual field, inherited arithmetic proof, determinant decay
estimate, and canonical target are undergoing their complete kernel build.
The final entrypoint is written and has no analytic hypothesis. Its presence
in the repository does not establish the final bound in Lean until that build
and axiom audit succeed.

The submission gate is a successful `lake build Submission`, an allowed-axiom
audit of the unconditional `Race.bound`, and a full published commit SHA.
Only that concrete result will be sent through the verifier's submission issue.

## Written certificate checks

The full written certificate for 528.23288 passes both local exact arithmetic
checks and [GitHub Actions run 41120910391](https://github.com/1337isnot1337/catalan-constant/actions/runs/41120910391).
An independent residual checker reproduced the 157-cell certificate byte for
byte. An independent tangent checker reproduced the three circle bounds.
These checks supplement, and do not replace, the Lean submission gate.
