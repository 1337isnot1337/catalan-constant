# A smaller quadrature gap and a retuned energy budget

## Result and dependency

The written argument below, combined with Litsey's determinant construction and
the separate exact circle certificate, gives

\[
  \mu(G)\le 531.55361.
\]

This is a mathematical derivation from the stated upstream theorems, with new
finite inequalities checked by exact rational Python arithmetic. It is not a
Lean proof of the new bound. It does not independently replay the upstream Lean
formalization or re-establish the determinant construction.

The upstream dependency is S. Litsey, *An irrationality measure for Catalan's
constant*, at repository commit
`aa2a42f4f3835347ad46608779e22dd52c2dc7bf` in
[slitsey/catalan-irrationality-measure](https://github.com/slitsey/catalan-irrationality-measure/tree/aa2a42f4f3835347ad46608779e22dd52c2dc7bf).
We keep its design `(58,9,3,5,3)`, arithmetic normalizer, rank-deficiency profile,
nonvanishing proof, first-case trial, and second-case trial sequences. The new
work changes the gap used for quadrature nodes and the scalar budget.

## Inputs retained from the upstream proof

Write `ell=log(2)`. The degree is `53N`. The second-case trial bounds are

\[
\mathcal N=0.7736205195,\qquad
\Phi=-2.53949899,\qquad
\mathcal R=-0.0631062,\qquad
\mathcal N_c=-0.77.
\]

Here `Ncal` bounds `2||u||²+||v||²/2`, `Phi` bounds the sum of the two field
suprema, `Rcal` bounds the residual field, and `Ncal_c` bounds the near field.
The first-case fixed-column cost is `4.09661`. The arithmetic gain is

\[
\chi=\frac{36235515874601938601596598}
{1642609663271115992578125}.
\]

Thus the common denominator has asymptotic exponent at most

\[
 A=\frac{2673}{8}\ell+116+\frac{24269}{4}-\chi.
\]

The exact gain is the area of the unchanged 102-piece upstream profile. It is
larger than the deliberately rounded `22.05325` used in the upstream final
integer theorem. The paper already discusses recovering this rounding loss;
that part is not a new arithmetic improvement.

## Extending the residual-field domain

The retained second-case trial has

\[
u_k=c_k+\operatorname{Re}\sum_j r_jz_j^k,\qquad c_k=0\ (k>160),
\]

with 75 geometric terms. Its residual field is

\[
R(x)=-\frac{53}{58}\log(1+x^2)
       -2\sum_{k\ge1}\frac{u_kT_k(x)}{k}.
\]

The upstream certificate proves `R(x)<=-0.0631062` for
`401/2500 <= |x| <= 1`. We extend the gap to

\[
g=\frac{1573}{10000}=0.1573
\]

by checking the added strips exactly. On each strip we use 32 rational cells.
The derivative is a polynomial plus rational functions because

\[
\frac{d}{dx}\sum_{k\ge1}\frac{u_kT_k(x)}{k}
 =\sum_{k=1}^{160}c_kU_{k-1}(x)
   +\operatorname{Re}\sum_j\frac{r_jz_j}{1-2xz_j+z_j^2}.
\]

Exact interval evaluation certifies positive derivative on the negative strip
and negative derivative on the positive strip. Consequently their maxima are
at `-g` and `g`. Rounded display values of the exact enclosures are:

| Quantity | Verified enclosure, rounded outward |
|---|---:|
| `R(-g)` | `[-0.063154435755,-0.063154435754]` |
| `R(g)` | `[-0.203873141965,-0.203873141964]` |
| `R'` on `[-0.1604,-0.1573]` | `[0.75295894,0.80025858]` |
| `R'` on `[0.1573,0.1604]` | `[-1.68973110,-1.63522148]` |

Both endpoint upper bounds are strictly below `-0.0631062`. Hence the same
residual cap holds throughout `g <= |x| <= 1`.

`residual_certificate.py` performs these checks using `fractions.Fraction`.
It evaluates the finite Chebyshev sum exactly. For each geometric term it uses

\[
-2\mathsf T_j(x)=\operatorname{Re}\bigl(r_j\log(1-2xz_j+z_j^2)\bigr).
\]

The real part of every logarithm argument at the two checked endpoints is
positive. Logarithms are enclosed by the atanh series after reducing their
positive arguments to `[1,2]`, with an explicit geometric tail. Arguments are
enclosed by alternating arctangent series and rational argument reduction,
using the Machin identity `pi/4=4 atan(1/5)-atan(1/239)`. The function is analytic
on the real interval because `|z_j|<1`; its logarithm argument cannot lie on the
negative real axis. All interval rounding is outward to rational dyadic bounds.
The derivative polynomial is formed exactly in a shifted power basis, then
evaluated with rational interval Horner arithmetic. No floating-point value is
used in an assertion.

The JSON witness is an exact transcription of the upstream `P` trial. Its
source blob is `c401f993810de11834f6db6ce5eda4064be09021`, and the upstream commit
and SHA-256 are recorded in `certificates/trial_data.json`. The identical Git
blob occurs at both that original record commit and the current pinned revision.

## Circle bound

Take

\[
a=\frac{2g}{1+g^2},\quad
r=\frac{100000001}{100000000},\quad
w_c=52.6055,\quad w=52.605501>w_c.
\]

The companion circle certificate checks the upstream `CircPiece` inequalities
on a finite rational cover. It proves the quadrature-weight exponential rate
`w_c` for this smaller gap. The fixed factor involving `(r-1)^(-2)` affects only
the threshold for sufficiently large `N`, and is absorbed by `w>w_c`.

## Retuned scalar budget

Choose

\[
U=2.2558577253,\qquad c_2=4.2881501.
\]

Let

\[
m=\frac{41}{58}\ell-\mathcal N-\Phi-U,\qquad
s=\frac{76}{29}\ell-\Phi+\mathcal R-c_2.
\]

The exact scalar certificate checks

\[
m>0,\qquad s^2\le8\ell m,\qquad
\ell-\mathcal R+\mathcal N_c<0.
\]

These are the hypotheses of the upstream second-case budget lemma. The
first-case budget remains valid because `U` has decreased from `2.255858836`,
and `4.09661<c2`. The determinant estimate therefore holds in the neighborhood
with exponential radius

\[
\rho=58c_2+w=301.3182068.
\]

After the unchanged denominator clearing, the decay rate can be taken to be

\[
\eta=30.0437525
 <3364U-\frac{16129}{8}\ell-\frac{24733}{4}+\chi.
\]

The strict inequality leaves room for the asymptotic `o(N²)` terms. No explicit
denominator threshold is claimed.

## Final irrationality criterion

Set

\[
B=531.55361,\quad\kappa=B/\rho,\quad
\delta=10^{-10},\quad\omega=3/4.
\]

Exact rational arithmetic checks every numerical hypothesis of the upstream
free-window criterion:

\[
0<\omega\le1,\quad2\omega<\kappa,\quad0<\eta<106,
\]

\[
1<2\bigl(\omega-\delta(2\kappa-\omega)\bigr),\qquad
53+212\delta\kappa<\eta\kappa.
\]

The last inequality follows also from the exact threshold

\[
\frac{53\rho}{\eta-212\delta}
 =\frac{39924662401000}{75109381197}
 <\frac{53155361}{100000}.
\]

The prime number theorem supplies the chosen `delta` beyond a sufficiently
large threshold. The unchanged construction therefore gives
`|G-p/q|>q^(-531.55361)` for every integer `p` and every sufficiently large
positive integer `q`, and hence the stated irrationality-exponent bound.

## Reproduction

Run all new finite certificates from the repository root with ordinary Python 3:

```text
python scripts/verify.py
```

For the individual residual and scalar checks:

```text
python scripts/residual_certificate.py
python scripts/scalar_certificate.py
```

The residual check computes large rational polynomial intervals and takes about
15 seconds in the environment used for this result. The scalar check is short. The separate circle
certificate and upstream gain-area check must also pass. Passing these checks
validates the new finite inequalities; the theorem still depends on the cited
upstream determinant, energy, denominator, and irrationality-criterion proofs.
