# The inverse-image construction at any fixed degree

The degree-53 construction extends to every fixed degree `m`. This permits
better finite polynomial approximations to the asymmetric allowed set without
changing the degree `53N` of the interpolation space.

## Hypotheses

Let `P` be a fixed real polynomial of degree `m`. Suppose that, for every
`y` in `[-1,1]`, `P(t)=y` has exactly `m` distinct real roots in the permitted
two bands contained in `(-1,1)`. The rational alternating-control certificate
proves this property. As in the degree-53 argument, compactness supplies a
constant

$$
c=\min_{P(t)\in[-1,1]}|P'(t)|>0.
$$

Let `r>1` be fixed. Suppose a circle certificate proves

$$
(2|P(z)|+1)^{53}|1-z|^{6m}\le e^{m w_c}
\qquad (|z|=r).
\tag{1}
$$

All constants, including `m`, are independent of `N`.

## Exact node count

Put

$$
K_N=\left\lceil\frac{53N}{m}\right\rceil,
\qquad s_N=mK_N-53N\in\{0,\ldots,m-1\},
\qquad H_N(t)=T_{K_N}(P(t)).
$$

The inverse-branch argument gives `m K_N` distinct allowed roots of `H_N`.
Remove any `s_N` of them, and let

$$
E_N(t)=\prod_{j=1}^{s_N}(t-\sigma_{j,N}),
\qquad F_N(t)=\frac{H_N(t)}{E_N(t)}.
$$

The quotient `F_N` is a polynomial of degree exactly `53N`, with `53N`
distinct roots in the allowed bands. Those roots are the interpolation nodes.
The degree of the common factor times any cardinal polynomial is again at
most `78N-1`. Thus the original coefficient-functional cutoff needs no change.

## Removing a bounded number of roots costs a fixed factor

For every retained root `tau`,

$$
|H_N'(\tau)|\ge K_Nc,
\qquad
|F_N'(\tau)|=\frac{|H_N'(\tau)|}{|E_N(\tau)|}
\ge\frac{K_Nc}{2^{s_N}}.
$$

The last inequality uses `|tau-sigma|<2`, since all nodes are in `(-1,1)`.
On the circle, each removed factor has absolute value at least `r-1`, so

$$
|F_N(z)|\le\frac{|H_N(z)|}{(r-1)^{s_N}}.
$$

Consequently every retained cardinal polynomial satisfies

$$
|\ell_{\tau,N}(z)|
\le\frac{2^{s_N}}{K_Nc(r-1)^{s_N+1}}|H_N(z)|.
\tag{2}
$$

This factor is at most a fixed constant times `1/N`: `s_N<=m-1` and
`K_N>=53N/m`. It has no exponential cost in `N`.

## The circle exponent

Write `A(z)=2|P(z)|+1>=1`. The elementary Chebyshev bound gives

$$
\begin{aligned}
|H_N(z)||1-z|^{6N}
&\le A(z)^{K_N}|1-z|^{6N}\\
&=A(z)^{s_N/m}
  \left(A(z)^{53/m}|1-z|^6\right)^N\\
&\le \left(\max_{|z|=r}A(z)\right)e^{w_cN},
\end{aligned}
$$

where the last step uses `(1)` and `0<=s_N/m<1`. The maximum is finite because
the circle is compact. Combining this with `(2)` proves the same cardinal
estimate as before, up to a fixed prefactor.

The generic coefficient-functional bound then implies the required weight
estimate for every `w>w_c`, eventually in `N`. All remaining determinant,
energy, arithmetic, and prime-selection arguments are unchanged. In
particular, the degree of the integer polynomial in the rational-approximation
criterion stays `53N`; `m` is only the fixed degree of an auxiliary node map.

## Exact circle checking without fractional powers

For `s=cos(theta)` and `z=r exp(i theta)`, the quantity `|P(z)|^2` is a real
polynomial in `s`, expressible in the Chebyshev basis by autocorrelation of
the power coefficients of `P`. The factor `|1-z|^2=r^2+1-2rs` is affine in
`s`.

On each rational interval in `s`, an exact Bernstein enclosure bounds
`|P(z)|^2` by a rational upper bound `M`. A rational upper bound `B` for
`sqrt(M)` can be checked by `B^2>=M`. The circle condition follows from

$$
(2B+1)^{106}(r^2+1-2r s_{\rm lo})^{6m}
\le e^{2m w_c}.
$$

This squared form uses only integer powers and rational comparisons. An
integer or rational threshold below the exponential is certified with a
finite positive Taylor sum. A finite chain of rational intervals covering
`[-1,1]` completes the proof.

## The filtered cell certificate used in the implementation

To reduce interval overestimation, write $6m=53k+\ell$, where
$0\le\ell<53$, and form $Q(z)=P(z)(1-z)^k$. Then

$$
(2|P(z)|+1)^{53}|1-z|^{6m}
=\bigl(2|Q(z)|+|1-z|^k\bigr)^{53}|1-z|^\ell.
$$

On a cell $[a,b]$ in $s=\cos\theta$, the exact Bernstein enclosure gives
$|Q(z)|^2\le M^2$ for an explicitly checked integer $M$. Set

$$
A=2M+\lceil(r+1)^k\rceil,\qquad D=r^2+1-2ra.
$$

It suffices to check $A^{106}D^\ell\le E<\exp(2mw_c)$.
The checker constructs $E$ using a rational lower bound for $e$ and a finite
positive Taylor sum for the fractional part of $2mw_c$. The dyadic cells
cover $[-1,1]$ exactly. This proves (1) using integer powers alone.
