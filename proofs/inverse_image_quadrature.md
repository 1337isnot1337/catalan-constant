# Polynomial inverse-image quadrature on asymmetric intervals

## Change to the construction

The determinant, its rational coefficients, the arithmetic normalizer, and its
degree remain those of Litsey's design `(58,9,3,5,3)`. Only the interpolation
nodes used to bound the coefficient matrix at the real place change.

Let

$$
g_-=1573/10000,\qquad g_+=857/10000,\qquad
L=-\frac{2g_-}{1+g_-^2},\qquad
R=\frac{2g_+}{1+g_+^2}.
$$

The exact rational polynomial `P` in `inverse_image_53.json` has degree 53. It
is stored in the ordinary Chebyshev basis: `P(t)=sum_{k=0}^{53} c_k T_k(t)`.
For every `y` in `[-1,1]`, the equation `P(t)=y` has exactly 25 simple real
solutions in `(-1,L)` and 28 in `(R,1)`. Define

$$
H_N(t)=T_N(P(t)).
$$

The `53N` roots of `H_N` are the new quadrature nodes. They lie in the larger,
asymmetric allowed set `(-1,L) union (R,1)`.

The companion residual certificate verifies the inherited residual-field cap
on `[-1,-g_-] union [g_+,1]` in the energy coordinate. The map from that
coordinate `x` to the quadrature coordinate is

$$
t=\frac{2x}{1+x^2}.
$$

It is strictly increasing on `(-1,1)`, so every new node satisfies the required
residual-field cap. The first-case energy estimate has no new node-domain
condition. The second-case estimate uses this residual cap and the existing
near-point bound.

## Exact certificate for the inverse branches

The certificate stores 26 rational control points in `[-1,L]` and 29 in
`[R,1]`. In each group the control points increase strictly, the values of `P`
alternate in sign, and every value has absolute value strictly greater than
one. The verifier evaluates `P` at these rational points by the Chebyshev
recurrence using `Fraction` arithmetic.

Fix `y` in `[-1,1]`. Consecutive control values in either group straddle `y`,
so the intermediate value theorem gives one root of `P(t)-y` in each open
interval between them. This gives 25 roots on the left and 28 on the right.
The intervals are pairwise disjoint. A nonzero polynomial of degree 53 has
at most 53 roots, counted with multiplicity. Hence these are all its roots,
and every one is simple.

This proves more than root placement for `P(t)=0`: it proves root placement
and simplicity uniformly for every level `y` in the whole closed interval
`[-1,1]`. The exact smallest excess of an absolute control value over one is

$$
\frac{500000689000689}{500000000000000000000}>10^{-6}.
$$

Let `S=P^{-1}([-1,1])`. The preceding argument places `S` inside the two
bounded control-point intervals. The set `S` is closed, so it is compact.
Since `P'` is nonzero at every point of `S`, compactness gives a constant

$$
c=\min_{t\in S}|P'(t)|>0.
$$

No numerical value of `c` is needed for an asymptotic irrationality measure.
It is a fixed positive constant, independent of `N`.

## Cardinal-polynomial bound

The roots of `T_N` are `y_j=cos((2j-1)pi/(2N))`, for `1<=j<=N`. Each level
`y_j` has 53 distinct preimages under `P`. Different levels have disjoint
preimages. Therefore `H_N` has exactly `53N` distinct real roots in the allowed
set and has degree `53N`.

At any root `tau` of `H_N`, write `P(tau)=cos(theta)`, where
`theta=(2j-1)pi/(2N)`. Then

$$
|H_N'(\tau)|
 =N\,|U_{N-1}(P(\tau))|\,|P'(\tau)|
 =\frac{N|P'(\tau)|}{|\sin\theta|}\ge Nc.
$$

The cardinal polynomial attached to `tau` is

$$
\ell_{\tau,N}(z)
 =\frac{H_N(z)}{H_N'(\tau)(z-\tau)}.
$$

Choose the fixed rational radius `r=100000001/100000000`. Every node has
absolute value less than one, so `|z-tau|>=r-1` on `|z|=r`. Thus

$$
|\ell_{\tau,N}(z)|\,|1-z|^{6N}
\le\frac{|H_N(z)|\,|1-z|^{6N}}{Nc(r-1)}.
$$

Suppose the separate circle certificate establishes

$$
\sup_{|z|=r}\left(2|P(z)(1-z)^6|+(r+1)^6\right)\le e^{w_c}.
\tag{1}
$$

For every complex `u`, the elementary Chebyshev estimate
`|T_N(u)| <= (2|u|+1)^N` follows from the two roots of `v^2-2uv+1=0`.
Consequently,

$$
\begin{aligned}
|H_N(z)|\,|1-z|^{6N}
&\le\left((2|P(z)|+1)|1-z|^6\right)^N\\
&\le\left(2|P(z)(1-z)^6|+(r+1)^6\right)^N\\
&\le e^{w_cN}.
\end{aligned}
$$

This proves the needed cardinal bound with the fixed prefactor
`1/(Nc(r-1))`.

## Link to the existing quadrature and determinant estimates

The original row polynomials have a common factor of degree `25N`; their
residual polynomials have degree at most `53N-1`. Interpolation at the new
`53N` distinct nodes is therefore exact. The product of a cardinal polynomial
with the common factor has degree at most `78N-1`, so the original coefficient
functional with cutoff `H=78N` applies without extension.

The design-generic theorem
`polynomialFunctional_common_factor_le` bounds this functional by `4H`
times the circle bound for `ell(t)(1-t)^(h+q)`. Here `h+q=6N`, so

$$
|\operatorname{rowCommonFactor}(\tau)|\,|\beta_{\tau,k}|
\le\frac{312}{c(r-1)}e^{w_cN}.
$$

For every fixed `w>w_c`, this is eventually at most
`108000 N exp(wN)`, exactly the hypothesis consumed by
`weighted_atom_point_of_sheet`. The full-interval coefficient formula
`filteredCatalanCoeff_full_weights` requires only distinct nodes, no node
equal to zero or one, and a sufficient node count. All hold here; neither
symmetry of the nodes nor a quadratic gap map is required.

The node-dependent hypothesis of `weighted_atom_det` is a predicate `G` on
the energy coordinate. Use
`G(x) := (-1<x and x<=-g_-) or (g_+<=x and x<1)`.
The added-strip residual certificates establish the inherited residual cap
on this set. The rest of the fixed-column energy estimate is unchanged.

It follows that the inherited determinant smallness estimate holds with

$$
\rho=58c_2+w,
\qquad
\eta<3364\left(U-\frac{\log2}{2}\right)
 -\left(\frac{24733}{4}+\frac{2673}{8}\log2-\chi\right),
$$

where `U,c2` satisfy the inherited scalar budget and `chi` is the already
certified arithmetic-profile gain. The prime-selection criterion then
applies as before. This note proves the new quadrature link; the numerical
irrationality exponent also requires the separate circle, residual, and
scalar certificates to pass.

## Reproduction and proof status

```sh
python scripts/inverse_image_certificate.py --verify certificates/inverse_image_53.json
```

The polynomial candidate was found by a numerical minimax search on the two
allowed intervals, followed by removal of a gap root and scaling. Those
search steps are untrusted. The rational polynomial, rational control points,
and exact sign checks are the certificate. The analytic argument above is a
written proof, not a Lean formalization.

The upstream dependencies are in Sean Litsey's
[`catalan-irrationality-measure`](https://github.com/slitsey/catalan-irrationality-measure):
`CatalanMeasure/Parametric/PolynomialFunctional.lean`, and the files
`FullInterval.lean`, `AtomBase.lean`, and `WeightedAtom.lean` under
`CatalanMeasure/GenD/Analytic/`. The pinned upstream revision is `aa2a42f4f3835347ad46608779e22dd52c2dc7bf`.
