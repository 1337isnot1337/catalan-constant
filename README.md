# Catalan's constant: irrationality exponent research

## Current written result

For Catalan's constant $G=\sum_{n\ge0}(-1)^n/(2n+1)^2$, this repository gives the written bound

$$
\boxed{\mu(G)\le 528.23288.}
$$

Precisely, $|G-p/q|>q^{-528.23288}$ for every integer $p$ and every sufficiently large positive integer $q$.

The proof reuses Sean Litsey's determinant construction, arithmetic estimates, nonvanishing theorem, and energy witnesses. It adds a different quadrature node construction and exact rational certificates. The Lean source now includes the unconditional target theorem. The full local kernel build and its final axiom audit are **still in progress**. This is a **Claimed** result until the official verifier accepts it.

| Result | Upper bound |
|---|---:|
| Leading listed claim on [Big O Speedrun](https://bigospeedrun.com/other/catalan), checked 2026-10-30 | 532 |
| Unrounded estimate already discussed in Litsey's paper | about 531.88 |
| First result here: smaller symmetric gap and scalar retuning | 531.55361 |
| Asymmetric polynomial quadrature, degree 53 | 530.6705 |
| Asymmetric polynomial quadrature, degree 107 | 529.24599 |
| Trimmed support, sharper eventual near field, degree 130 | **528.23288** |

## What changed

The determinant design remains $(58,9,3,5,3)$, and its degree in the unknown constant remains at most $53N$.

The old quadrature nodes leave a symmetric gap around zero. The existing energy witness permits an asymmetric support. Trimming its negative outer endpoint allows the stronger residual cap $-0.0883$ on

$$
[-0.9636,-0.19501]\ \cup\ [0.098749,1]
$$

in the energy coordinate. A rational degree-130 polynomial $P$ supplies a node family inside this support. Exact sign checks prove that every level $P(t)=y$, $y\in[-1,1]$, has 61 simple real solutions in the left band and 69 in the right band. The roots of $T_{K_N}(P(t))$, with $K_N=\lceil53N/130\rceil$, supply the interpolation nodes after at most 129 surplus roots are removed. This removal changes only a constant prefactor in the estimates.

An exact Bernstein certificate gives the quadrature weight exponent $52.184351$. A sharper near-field estimate, valid for sufficiently large scales, supports the stronger residual cap. Together these lower the determinant perturbation cost to $\rho=299.43407727$. The energy target and fixed-column cost are retuned, and the exact area of the unchanged arithmetic profile is retained.

## Proofs

- [Current theorem and exact scalar conditions](proofs/result_52823288.md).
- [Trimmed support and eventual near-field argument](proofs/trimmed_support.md).
- [Three-tangent circle certificate](proofs/root_tangent_circle.md).
- [Lean inverse-image quadrature construction](proofs/lean-inverse-image-quadrature.md).
- [Lean residual certificate reproduction](docs/lean-residual-certificate.md).
- [Earlier degree-107 theorem](proofs/result_52924599.md).
- [Earlier degree-53 theorem](proofs/result_5306705.md).
- [Polynomial inverse-image quadrature](proofs/inverse_image_quadrature.md).
- [Extension to any fixed polynomial degree](proofs/inverse_image_general_degree.md).
- [Original symmetric improvement and upstream dependencies](proofs/measure.md).
- [Recorded verification of the degree-130 result](certificates/verification_130.json).

The argument relies on cited upstream mathematical theorems. The scripts check the new finite inequalities; they do not re-prove all of those theorems.

## Lean submission work

The source is prepared for the [Big O Speedrun verifier](https://github.com/bigospeedrun/verifier).
The new modules are under `Submission/Refinement/` and
`Submission/Improvement/`. The entrypoint `Submission.lean` states
`Race.bound : BigOSpeedrun.Catalan.Bound ((6602911 : ℚ) / 12500)`
with no remaining hypotheses. Its complete kernel check is pending.
The verifier's canonical statement is copied unchanged
to `Submission/CatalanStatement.lean`. `scripts/vendor_lean.py` copies only
the pinned upstream dependency closure and prefixes its imports for the
required layout. The source manifest records original and converted hashes.

The build configuration pins Lean 4.34.1 and the verifier's Mathlib revision.
A submission pins a full source commit and the exact rational bound
`6602911/12500`. The official check can run in parallel with the local rebuild.
The written result, local kernel status, and official acceptance are tracked
separately. A source-layout audit checks paths and hashes; it does not establish
the mathematical theorem.

The [formalization progress record](proofs/lean_progress.md) lists the compiled
components. These include the complete new quadrature construction, the sharp
circle estimate, the eventual near field, all 98 trimmed residual cells, and
the generic eventual determinant-decay transfer. The remaining inherited
numerical and arithmetic dependencies and the concrete final assembly are
being checked. The [check-status record](certificates/lean_check_status.json)
records the pending full-build and final-axiom gates.

To reproduce the complete Lean check with the pinned toolchain:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build Submission
```

The entrypoint prints the axioms of `Race.bound`. The accepted logical axioms
are `propext`, `Classical.choice`, and `Quot.sound`. The official verifier's
passing receipt is required before calling this result **Lean Verified**.

## Reproduce the certificates

From the repository root, using ordinary Python 3 and its standard library:

```sh
python3 scripts/verify_current.py
```

This checks the rational inverse branches, the complex-circle bound, the full residual domain, the eventual near field, the 102-piece arithmetic-profile area, and every scalar inequality in the final irrationality criterion. It also rejects an invalid support certificate and an exponent below the proved criterion threshold. Floating-point computations are not used in any certificate decision.

The earlier results remain independently reproducible:

```sh
python3 scripts/verify.py
python3 scripts/verify_asymmetric.py
python3 scripts/verify_current.py --degree 107
```

Candidate search is separate from certification. The [trigamma experiments](research/trigamma/README.md) record an attempted alternative that did not produce a bound.

## Sources and attribution

The principal dependency is [slitsey/catalan-irrationality-measure](https://github.com/slitsey/catalan-irrationality-measure/tree/aa2a42f4f3835347ad46608779e22dd52c2dc7bf), pinned at `aa2a42f4f3835347ad46608779e22dd52c2dc7bf`. The trial data are identical to those at the original leaderboard record commit `4d338bf4c56ddfa60657b64d23100c3404d039ad`; their Git blob and SHA-256 hashes are checked.

The project builds on [OpenAI's original irrationality proof](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Catalans-constant-is-irrational-September-24-2026) and the parameterized construction studied by [M. C. S. Carreira](https://github.com/MarcosCarreira/catalan-designs). See [NOTICE](NOTICE) and [LICENSE](LICENSE).

