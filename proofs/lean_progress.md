# Lean formalization progress

The target is `BigOSpeedrun.Catalan.Bound (6602911 / 12500)`, representing
the upper bound 528.23288. The unconditional `Race.bound` source is written;
its complete kernel build and final axiom audit are still pending.

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
- The full trimmed residual cover: 98 exact Taylor cells in 54 checked
  modules, including the aggregate `residual_sup_trimmed` theorem.
- The generic eventual determinant-decay transfer in `DecayEventually`.
- All six inherited finite norm blocks and the first two logarithmic norm
  blocks, with ordinary kernel checking.

The finite comparisons use kernel reduction (`decide +kernel`). The printed
axioms for the complete circle bound, real exponential bound, and factor positivity theorem are
`propext`, `Classical.choice`, and `Quot.sound`.

The circle certificate is recorded in `certificates/root_tangent_130.json`.
It proves the same weight cap 52.18435 as the earlier Bernstein certificate.
It encloses all 130 roots by rational sign tests, bounds squared distances by
positive affine functions of the real part, and uses three product tangents.
The generic inequality follows from `1 + t ≤ exp t`.

## Remaining assembly

The remaining inherited row, column, residual, and logarithmic norm
certificates, the arithmetic proof, and the concrete final assembly are
undergoing their complete kernel build. The new trimmed residual field and
generic eventual decay theorem have already passed. The local build separates
the lower-memory field covers from the heavier logarithmic norm checks;
the latter also have the guarded source ordering described in
[`verifier_resources.md`](verifier_resources.md).
The final entrypoint is written and has no analytic hypothesis. Its presence
in the repository does not establish the final bound in Lean until that build
and axiom audit succeed.

The final local validation gate is a successful `lake build Submission` and
an allowed-axiom audit of the unconditional `Race.bound`. The official verifier
can check a frozen, byte-audited source commit in parallel with this local
rebuild. Submission alone does not establish the bound in Lean; the result
remains Claimed until an official passing receipt is available. Source-layout
and published-byte audits are recorded separately from proof checks.

## Written certificate checks

The full written certificate for 528.23288 passes both local exact arithmetic
checks and [GitHub Actions run 41120910391](https://github.com/1337isnot1337/catalan-constant/actions/runs/41120910391).
An independent residual checker reproduced the 157-cell certificate byte for
byte. An independent tangent checker reproduced the three circle bounds.
These checks supplement, and do not replace, the Lean submission gate.
