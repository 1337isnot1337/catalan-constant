# Catalan's constant: irrationality exponent research

## Current written result

For Catalan's constant $G=\sum_{n\ge0}(-1)^n/(2n+1)^2$, this repository gives the written bound

$$
\boxed{\mu(G)\le 529.24599.}
$$

Precisely, $|G-p/q|>q^{-529.24599}$ for every integer $p$ and every sufficiently large positive integer $q$.

The proof reuses Sean Litsey's determinant construction, arithmetic estimates, nonvanishing theorem, and energy witnesses. It adds a different quadrature node construction and exact rational certificates. This is **not a new Lean formalization**. The complete upstream Lean development has not been rebuilt here, and this result has not been submitted to or verified by the leaderboard.

| Result | Upper bound |
|---|---:|
| Leading listed claim on [Big O Speedrun](https://bigospeedrun.com/other/catalan), checked 2026-10-30 | 532 |
| Unrounded estimate already discussed in Litsey's paper | about 531.88 |
| First result here: smaller symmetric gap and scalar retuning | 531.55361 |
| Asymmetric polynomial quadrature, degree 53 | 530.6705 |
| Asymmetric polynomial quadrature, degree 107 | **529.24599** |

## What changed

The determinant design remains $(58,9,3,5,3)$, and its degree in the unknown constant remains at most $53N$.

The old quadrature nodes leave a symmetric gap around zero. The existing energy witness permits a larger interval on the positive side. We certify its residual bound on

$$
[-1,-0.1573]\ \cup\ [0.0857,1]
$$

in the energy coordinate. A rational degree-107 polynomial $P$ supplies a node family inside this asymmetric support. Exact sign checks prove that every level $P(t)=y$, $y\in[-1,1]$, has 51 simple real solutions in the left band and 56 in the right band. The roots of $T_{K_N}(P(t))$, with $K_N=\lceil53N/107\rceil$, supply the interpolation nodes after at most 106 surplus roots are removed. This removal changes only a constant prefactor in the estimates.

An exact Bernstein certificate bounds the new node polynomial on a complex circle. This lowers the quadrature weight exponent from the upstream $52.7887$ to $51.297401$. The energy target and fixed-column cost are retuned, and the exact area of the unchanged arithmetic profile is retained.

## Proofs

- [Current theorem and exact scalar conditions](proofs/result_52924599.md).
- [Earlier degree-53 theorem](proofs/result_5306705.md).
- [Polynomial inverse-image quadrature](proofs/inverse_image_quadrature.md).
- [Extension to any fixed polynomial degree](proofs/inverse_image_general_degree.md).
- [Original symmetric improvement and upstream dependencies](proofs/measure.md).
- [Recorded verification of the degree-107 result](certificates/verification_107.json).

The argument relies on cited upstream mathematical theorems. The scripts check the new finite inequalities; they do not re-prove all of those theorems.

## Lean submission work

Formalization is in progress for the [Big O Speedrun verifier](https://github.com/bigospeedrun/verifier).
The new draft modules are under `Submission/Refinement/` and
`Submission/Improvement/`; they are not yet a completed, checked proof of
the displayed bound. The verifier's canonical statement is copied unchanged
to `Submission/CatalanStatement.lean`. `scripts/vendor_lean.py` copies only
the pinned upstream dependency closure and prefixes its imports for the
required layout. The source manifest records original and converted hashes.

The build configuration pins Lean 4.34.1 and the verifier's Mathlib revision.
A submission will identify a full commit and the strongest bound proved by
its checked `Race.bound` theorem. The written bound and formal submission
status are tracked separately.

## Reproduce the certificates

From the repository root, using ordinary Python 3 and its standard library:

```sh
python3 scripts/verify_current.py
```

This checks the rational inverse branches, the complex-circle bound, the residual-field extensions, the 102-piece arithmetic-profile area, and every scalar inequality in the final irrationality criterion. It also rejects an invalid support certificate and an exponent below the proved criterion threshold. Floating-point computations are not used in any certificate decision.

The earlier results remain independently reproducible:

```sh
python3 scripts/verify.py
python3 scripts/verify_asymmetric.py
```

Candidate search is separate from certification. The [trigamma experiments](research/trigamma/README.md) record an attempted alternative that did not produce a bound.

## Sources and attribution

The principal dependency is [slitsey/catalan-irrationality-measure](https://github.com/slitsey/catalan-irrationality-measure/tree/aa2a42f4f3835347ad46608779e22dd52c2dc7bf), pinned at `aa2a42f4f3835347ad46608779e22dd52c2dc7bf`. The trial data are identical to those at the original leaderboard record commit `4d338bf4c56ddfa60657b64d23100c3404d039ad`; their Git blob and SHA-256 hashes are checked.

The project builds on [OpenAI's original irrationality proof](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Catalans-constant-is-irrational-September-24-2026) and the parameterized construction studied by [M. C. S. Carreira](https://github.com/MarcosCarreira/catalan-designs). See [NOTICE](NOTICE) and [LICENSE](LICENSE).

