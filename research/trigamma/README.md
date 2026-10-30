# Exploratory screen of trigamma frames for Catalan's constant

This experiment did not produce an irrationality bound for Catalan's
constant. Three natural frames all have negative decay minus arithmetic
content in the tested geometries. The closest result is approximately
`-0.27419`, too far from zero for quadrature precision to explain the
failure. These are exploratory floating point results, not certificates
of either impossibility or an irrationality bound.

## Motivation and source

Sean Litsey's trigamma framework gives much smaller exponents for several
other constants. Its elementary arithmetic bounds might therefore be
useful for Catalan's constant if a suitable rational linear combination
of digamma functions could isolate it.

The source is
[slitsey/catalan-irrationality-measure, commit aa2a42f4f3835347ad46608779e22dd52c2dc7bf](https://github.com/slitsey/catalan-irrationality-measure/tree/aa2a42f4f3835347ad46608779e22dd52c2dc7bf),
especially
[paper-lambda](https://github.com/slitsey/catalan-irrationality-measure/blob/aa2a42f4f3835347ad46608779e22dd52c2dc7bf/paper-lambda/lambda-irrationality-hexagon.tex).
`trigamma_inputs.json` records the exact rational scalar inputs, paths,
and SHA-256 hashes of the four upstream `Data.lean` files used here.

## Frames tested

Write

$$
F(z)=\sum_j w_j\psi(z+a_j),\qquad \sum_jw_j=0,
$$

where $\psi$ is the digamma function. The standard trigamma identities
$\psi'(1/4)=\pi^2+8G$, $\psi'(3/4)=\pi^2-8G$,
$\psi'(1/2)=\pi^2/2$, and $\psi'(1)=\pi^2/6$ give the following
exact identities.

| Frame | Shifts $a_j$ | Weights $w_j$ | $F'(0)$ |
|---|---|---|---|
| `G_direct` | $1/4,3/4$ | $1,-1$ | $16G$ |
| `G_three` | $1/4,1/2,1$ | $-2,5,-3$ | $-16G$ |
| `G_four` | $1/4,3/4,1/2,1$ | $5,-1,-10,6$ | $48G$ |
| `chi3_control` | $1/3,1/2,1$ | $-1/3,1/2,-1/6$ | $-3L(2,\chi_3)/2$ |

The three-term Catalan frame lets one prime residue class avoid early
quarter-period poles. The four-term frame also cancels a partial residue
sum between two poles. Those cancellations were included in the screen.

## What the screen computes

The border parameter is $\alpha=m/r$, with $r$ normalized to one and
total interval length $N=1+2\alpha$. For a prime scale $\theta=p/r$,
the script takes the least of these arithmetic cost estimates:

1. The assignment bound $2+2\alpha-\operatorname{dist}(\alpha,\theta\mathbf Z)$.
2. The pole-free-window improvement after deleting the maximal complete
   prefix of length $\lfloor\alpha/\theta\rfloor\theta$.
3. Regular-node assignment potentials when $N\leq2\theta$.

For shifts with common denominator $q$ and a reduced residue class
$u\bmod q$, the first pole of the term at $a$ occurs at
$\kappa\theta$, where
$\kappa\equiv a u^{-1}\pmod1$, with the representative in $(0,1]$.
Partial sums of $w_j/\kappa_j$ and $w_j/\kappa_j^2$ are computed as
exact rational numbers. A border node is regular when the first sum
vanishes; a common node requires both sums to vanish.

The resulting cost functions are integrated numerically and averaged
over the reduced residue classes. The interval $0<\theta<0.001$ is
filled with the trivial cost $2+2\alpha$. This is a conservative
small-scale approximation before numerical integration error. The
reported SciPy errors are estimates and are not interval certificates.

To compare different numbers of shifts, the script uses the upstream
analytic scalar inputs to form the exploratory decay proxy

$$
D_{\rm new}=D_{\rm source}
 +2(d_{\rm new}-d_{\rm source})(S_{\rm cap}-\eta_S).
$$

This substitutes the new dimension in the existing contour budget. A
successful numerical screen would still require proof of the contour,
nonvanishing, arithmetic, and uniformity hypotheses for the new frame.
No such adaptation is claimed here.

## Results

Let $\Lambda$ denote the integrated arithmetic cost. A usable result
would require $D-\Lambda>0$. Each tested Catalan frame fails this test.

| Analytic inputs | $\alpha$ | `G_direct`: $D-\Lambda$ | `G_three`: $D-\Lambda$ | `G_four`: $D-\Lambda$ |
|---|---:|---:|---:|---:|
| Fourths | 0.100000 | -1.279063 | **-0.274194** | -1.457969 |
| Fifths | 0.111111 | -1.315798 | -0.288741 | -1.489954 |
| Thirds | 0.150000 | -1.490179 | -0.369934 | -1.622872 |
| Chi3 | 0.250000 | -1.948617 | -0.530147 | -1.892961 |

The best tested Catalan case has $\Lambda\approx3.89951863$ and
$D\approx3.62532450$. It would need an additional arithmetic gain of
more than $0.27419$, or a corresponding analytic improvement, just to
make the decay positive.

As a sanity check, the original `chi3_control` frame with Chi3 analytic
inputs gives $\Lambda\approx4.09589485$, compared with the upstream
certified value $4.09592776731$. This agreement is useful evidence that
the arithmetic formulas were implemented plausibly. The small
difference does not certify an improvement: this screen uses different
small-scale truncation and unverified numerical quadrature.

### Assignment linear program

`trigamma_lp_screen.py` checks whether more flexible nonnegative row and
column potentials improve the closest Catalan case. It partitions the
residue interval at every pole and interval boundary. Partial pole sums
are exact fractions, while interval lengths, the linear program, and
the outer integration use floating point numbers. The local valuations
distinguish equal-residue fibers from different-residue fibers and
include the two parity classes of the border.

For `G_three`, Fourths, and a 300-point outer grid, the optimal tested
assignment potentials give no numerical saving over the explicit
potentials: the integral difference is at floating point roundoff
scale. The coarse integration gives
$\Lambda\approx3.89964889$ and $D-\Lambda\approx-0.27432439$.
This is evidence that merely optimizing these assignment potentials
will not resolve the deficit. It does not rule out an additional rank
argument or a different frame.

## Reproduction

The scripts require Python, NumPy, and SciPy. They read only the adjacent
`trigamma_inputs.json`; no network or upstream checkout is required.

```bash
python trigamma_screen.py --output trigamma_screen_results.json
python trigamma_screen.py --frame G_three --certificate Fourths
python trigamma_lp_screen.py G_three Fourths 300
```

The first command reproduces all 16 floating point screens. The last
command writes `trigamma_lp_results.json` beside its script. None of
these files participates in the certified Catalan measure argument.
