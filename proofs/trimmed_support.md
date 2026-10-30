# Lowering the residual cap by trimming the node support

The previous node construction retained quadrature nodes arbitrarily close to
the negative endpoint. The residual field is largest there. A stricter
residual cap becomes available after moving that endpoint slightly inward and
adjusting the two inner endpoints.

This changes the auxiliary interpolation nodes and the real-place scalar
budget. The determinant, its arithmetic normalizer, and its degree are
unchanged.

## Exact support and residual cap

Use the energy-coordinate set

$$
S_x=\left[-\frac{2409}{2500},-\frac{19501}{100000}\right]
\ \cup\
\left[\frac{98749}{1000000},1\right].
$$

The residual certificate must prove

$$
\mathcal R(x)\le C_R=-\frac{883}{10000}=-0.0883
\quad(x\in S_x),
$$

for the same fixed trial sequence as before. This is a strictly stronger
bound on a smaller domain. The old residual cap alone does not imply it.

Map the four endpoints to the quadrature coordinate by
`t=2x/(1+x^2)`. The degree-130 polynomial in
`inverse_image_trimmed_130.json` has 61 inverse branches in the resulting
left interval and 69 in the right interval. Its exact rational control-point
witness is checked by `inverse_image_certificate.py`. The format `v2`
records the additional endpoint `outer_minus=2409/2500`.

The arbitrary-degree construction in `inverse_image_general_degree.md`,
with `m=130`, then produces exactly `53N` interpolation nodes in these
intervals. All prefactors arising from removal of at most 129 surplus roots
are fixed constants, independent of `N`.

## An eventual near-point estimate

The near-point field before the earlier coarse rounding has the coefficient

$$
a_N=\frac{48N-1}{58N}
$$

in front of `log(y)`, for `0<y<1`. The previous proof bounded this from below
by `47/58`, which is valid even for `N=1`. An irrationality exponent only
uses sufficiently large `N`. For `N>=1000000`,

$$
a_N\ge\alpha:=\frac{47999999}{58000000}.
$$

Since `log(y)<0`, replacing `a_N` by `alpha` gives an upper bound on the
near-point field. The first trial coefficient is exactly

$$
u_1=\frac{199568949785990693712071}
 {1099511627776000000000000}.
$$

Thus the main part of the grouped field is bounded above by

$$
F(y)=-\frac{53}{58}\log(1+y^2)+\alpha\log y-u_1y.
$$

The near-field certificate proves

$$
\sup_{0<y<1} F(y)\le C_N=-0.78145547.
$$

This is a one-variable estimate. Multiplying `F'(y)` by the positive number
`y(1+y^2)` gives the cubic

$$
p(y)=\alpha-u_1y+(\alpha-106/58)y^2-u_1y^3.
$$

All coefficients of `p'(y)` are negative on `(0,1)`, so `p` decreases
strictly. Its unique zero is the unique maximizer of `F`. Rational bisection
isolates that zero, and exact logarithm enclosures certify the stated value.

The actual grouped field also contains the positive term
`log(1+y^2)/(58N)`. It is at most `log(2)/(58N)`. The exact certificate checks
that the main-field upper bound plus `log(2)/(58*10000000)` is still strictly
below `C_N`. Therefore the complete grouped near field is bounded by `C_N`
for every `N>=10000000`.

The third hypothesis of the existing second-case budget is then satisfied:

$$
\log2-C_R+C_N<0.
$$

The existing formal record `SecondTrialBounds.near` requests a near estimate
for every positive `N`. The new eventual estimate is not an instance of that
unchanged record. In the written energy proof, intersect its eventual tail
with `N>=10000000` before applying the pointwise second-case estimate.
Every later determinant and prime-selection assertion is already eventual
in `N`, so this change of starting index preserves the conclusion. No claim
is made that the new all-in-one formal record has been constructed in Lean.

## Remaining scalar assembly

The fixed norm and field bounds are unchanged:

$$
\mathcal N=0.7736205195,\qquad \Phi=-2.53949899.
$$

With `C_R=-0.0883`, the second-case scalar budget becomes

$$
\begin{aligned}
M&=\frac{41}{58}\log2-\mathcal N-\Phi-U>0,\\
\left(\frac{76}{29}\log2-\Phi+C_R-c_2\right)^2
&\le8(\log2)M.
\end{aligned}
$$

The near-point inequality above supplies its remaining hypothesis. The
separately certified circle exponent gives `w_c`, and choose any `w>w_c`.
The determinant perturbation exponent is `rho=58c2+w`. Its normalized decay
is still

$$
\eta<3364U-\frac{16129}{8}\log2-\frac{24733}{4}+\chi,
$$

where `chi` is the unchanged exact arithmetic-profile gain. The scalar
certificate checks these conditions and the same prime-selection criterion
as in the preceding bounds.

The numerical search that selected this support and degree is not part of the
proof. The proof consists of the exact residual-domain and near-field
certificates, the rational inverse-branch witness, the exact circle
certificate, the scalar inequalities, and the written interpolation and
determinant argument.
