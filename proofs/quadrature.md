# A smaller quadrature weight exponent

## Result and scope

For Litsey's design `(58, 9, 3, 5, 3)`, put

\[
g=\frac{1573}{10000},\qquad
a=\frac{2g}{1+g^2},\qquad
r=\frac{100000001}{100000000},\qquad
w_c=\frac{105211}{2000}=52.6055.
\]

The exact certificate `circle_1573.json` proves the circle bound

\[
\left|T_{\lceil53N/2\rceil}
 \left(\frac{2z^2-(1+a^2)}{1-a^2}\right)\right|
 |1-z|^{6N}\le 3e^{w_cN}
 \quad (N\ge1,\ |z|=r).
\]

Consequently, the existing quadrature construction has weight exponent
`w = 52.605501`, or any real `w > 52.6055`. This statement follows from the
existing generic theorem `gap_weight_bounds` in
`CatalanMeasure/GenD/Analytic/GapWeights.lean`; it is not a claim that the new
certificate has been checked by Lean. The certificate verifier here uses exact
rational and integer arithmetic.

The circle change alone does not prove an irrationality measure: the energy
residual field must also be bounded on the additional strips between the new
gap `0.1573` and the old gap `0.1604`. The [residual certificate](measure.md) supplies that extension and checks it
before this weight is used in the final measure. The companion file
`circle_1604.json` retains the old gap and certifies `w_c=52.74605`; it needs no
extension of the residual field domain.

## Why the contour can be close to the unit circle

The old contour radius is `1.001`. Its role in the weight proof is a factor
`(r-1)^(-2)` in a prefactor. The generic theorem accepts every fixed radius
`1 < r <= 2`.

In detail, with `H_0=78` and circle constant `C=3`, the existing proof gives

\[
|\operatorname{rowCommonFactor}(\tau_j)|\,|\beta_{j,k}|
\le \frac{8H_0C}{(r-1)^2}\,N e^{w_cN}.
\]

For every fixed `w>w_c`, the constant `8H_0C/(r-1)^2` is eventually at most
`108000 exp((w-w_c)N)`. Hence the required weight bound is
`108000 N exp(wN)`. Choosing a radius very close to one changes only that
constant. No limit depending on `N` is needed.

The side conditions `0<a<1`, `1-a^2<=4a`, and `1<r<=2` are also checked
exactly by the verifier.

## Certificate and proof

Let `s=|Re z|`. On the circle `|z|=r`,

\[
|z^2-1|^2=(r^2+1)^2-4s^2,\qquad
|z^2-a^2|^2=(r^2+a^2)^2-4a^2s^2.
\]

Each certificate cell `[lo,hi]` stores six rational numbers
`lo,hi,b1,b2,H,base` and checks

\[
\begin{aligned}
&0\le lo<hi\le r,\quad b_1,b_2\ge0,\\
&(r^2+1)^2-4lo^2\le b_1^2,\\
&(r^2+a^2)^2-4a^2lo^2\le b_2^2,\\
&b_1+b_2\le H(1-a^2),\quad H\ge1,\\
&base\ge H,\quad H^2-1\le(base-H)^2,\quad1\le base\le9,\\
&base^{53}(r^2+1+2hi)^6\le E.
\end{aligned}
\]

All these inequalities are rational comparisons. The cells cover `[0,r]`
with consecutive endpoints, which is checked separately.

For

\[
\omega=\frac{2z^2-(1+a^2)}{1-a^2},\qquad
\Theta=\frac{|\omega-1|+|\omega+1|}{2},
\]

the first inequalities give `1<=Theta<=H`. The standard Chebyshev bound

\[
|T_K(\omega)|\le
 (\Theta+\sqrt{\Theta^2-1})^K\le base^K
\]

then applies. Also `|1-z|^2<=r^2+1+2hi`. With
`K=ceil(53N/2)` and `2K<=53N+1`,

\[
\begin{aligned}
\bigl(|T_K(\omega)|\,|1-z|^{6N}\bigr)^2
&\le base^{53N+1}(r^2+1+2hi)^{6N}\\
&\le9 E^N.
\end{aligned}
\]

The certificate uses the integer

\[
E=4926707008427985110447915543287285660159303931.
\]

It verifies the exact inequality

\[
E\le\sum_{k=0}^{399}\frac{(2w_c)^k}{k!}<e^{2w_c}.
\]

Taking square roots yields the claimed circle estimate.

The choice `g=0.1573` uses 990 cells. The smaller radius with the original gap
uses the same certificate format and proof. The numerical supremum of the
circle objective is approximately `52.60548880703` for the new gap; that
floating point estimate is used only to choose a target cap and is not part
of the proof.

## Reproduction

`circle_1573.json` and `circle_1604.json` below are generated outputs. The
repository keeps the deterministic exact generator; the default command
generates and verifies its certificate in memory.

From the repository root:

```sh
python scripts/circle_certificate.py
python scripts/circle_certificate.py --gap 401/2500 --weight-cap 1054921/20000
```

Regenerate the certificates with:

```sh
python scripts/circle_certificate.py --output /tmp/circle_1573.json
python scripts/circle_certificate.py --gap 401/2500 --weight-cap 1054921/20000 --output /tmp/circle_1604.json
python scripts/circle_certificate.py --verify /tmp/circle_1573.json
```

The verifier uses only the Python standard library. It does not call a
floating point square root, logarithm, or exponential. The generator bounds
square roots by integer square roots followed by exact squaring; it proves
the exponential comparison with a positive rational Taylor polynomial.

## Source dependency

The argument uses the construction and generic lemmas in Sean Litsey's
[`catalan-irrationality-measure`](https://github.com/slitsey/catalan-irrationality-measure)
repository, specifically `Analytic/GapCircleGen.lean` and
`Analytic/GapWeights.lean` under `CatalanMeasure/GenD/`. The original numerical
circle is in `CatalanMeasure/GenD/D58/Circle.lean`. The new data change the
radius and the gap; the proof of the generic certificate inequalities is
unchanged. The upstream revision is pinned to
`aa2a42f4f3835347ad46608779e22dd52c2dc7bf`.
