# Catalan's constant: a smaller irrationality exponent

## Current written result

For Catalan's constant \(G=\sum_{n\ge0}(-1)^n/(2n+1)^2\), the construction and certificates here give

\[
\boxed{\mu(G)\le 531.55361.}
\]

More precisely, \(|G-p/q|>q^{-531.55361}\) for every integer \(p\) and every sufficiently large positive integer \(q\).

This is a written derivation using Sean Litsey's determinant construction and generic theorems, with new finite inequalities checked in exact rational arithmetic. It is **not a new Lean formalization**. The complete upstream Lean development has not been rebuilt here. The result has not been submitted to or verified by the leaderboard.

| Comparison | Upper bound |
|---|---:|
| Leading claim on [Big O Speedrun](https://bigospeedrun.com/other/catalan), checked 2026-10-30 | 532 |
| Unrounded limiting estimate already discussed in Litsey's paper | about 531.88 |
| This written result | **531.55361** |

The improvement is modest. Recovering the upstream rounding loss alone is not new; the additional reduction comes from the quadrature and scalar changes below.

## What changed

The design remains \((58,9,3,5,3)\), with degree at most \(53N\). The arithmetic profile, nonvanishing argument, and trial sequences are unchanged.

1. The quadrature contour radius decreases from \(1.001\) to \(1.00000001\). Its distance from the nodes enters only a fixed prefactor, which the asymptotic estimate absorbs.
2. The permitted node gap in the energy coordinate decreases from \(0.1604\) to \(0.1573\). Exact interval checks extend the residual-field bound to both added strips.
3. The existing energy target and fixed-column cost are retuned jointly. The exact area of the unchanged 102-piece arithmetic profile is used.

| Parameter | Exact decimal value |
|---|---:|
| Energy target \(U\) | 2.2558577253 |
| Fixed-column cost \(c_2\) | 4.2881501 |
| Circle cap \(w_c\) | 52.6055 |
| Weight exponent \(w\) | 52.605501 |
| Neighborhood exponent \(\rho=58c_2+w\) | 301.3182068 |
| Integer-polynomial decay \(\eta\) | 30.0437525 |
| Prime-number-theorem tolerance \(\delta\) | 0.0000000001 |

The final condition is the exact rational inequality

\[
\frac{53\rho}{\eta-212\delta}
=\frac{39924662401000}{75109381197}
<\frac{53155361}{100000}=531.55361.
\]

## Proof and reproduction

- [Full derivation and upstream dependencies](proofs/measure.md).
- [Quadrature certificate and its proof](proofs/quadrature.md).
- [Recorded exact verification output](certificates/verification.json).

Run from the repository root:

```sh
python3 scripts/verify.py
```

Only the Python standard library is required. This command checks the exact profile area, generates and checks 990 rational circle cells, verifies both residual strips, checks all scalar inequalities, and tests rejection of malformed circle certificates. Floating-point values are used only for optional display. The check takes about 15 seconds in the development environment.

The GitHub Actions workflow runs the same command. These checks validate the new finite inequalities and their numerical assembly. They use the upstream mathematical theorems identified in the proof.

## Sources and attribution

The principal dependency is [slitsey/catalan-irrationality-measure](https://github.com/slitsey/catalan-irrationality-measure/tree/aa2a42f4f3835347ad46608779e22dd52c2dc7bf), pinned at `aa2a42f4f3835347ad46608779e22dd52c2dc7bf`. The trial data are identical to the data at the leaderboard's original record commit `4d338bf4c56ddfa60657b64d23100c3404d039ad`; their Git blob and SHA-256 hashes are checked explicitly.

The project builds on [OpenAI's original irrationality proof](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Catalans-constant-is-irrational-September-24-2026) and the parameterized construction studied by [M. C. S. Carreira](https://github.com/MarcosCarreira/catalan-designs). See [NOTICE](NOTICE) for attribution of the transcribed profile and trial data, and [LICENSE](LICENSE) for Apache License 2.0.

