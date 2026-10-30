# A three-tangent certificate for the sharp circle bound

This note explains the circle certificate used by the degree-130 Lean
formalization. It gives the same weight cap as the earlier Bernstein
certificate, with three scalar comparisons after the root enclosures.

The exact input data are in
[`root_tangent_130.json`](../certificates/root_tangent_130.json). The polynomial
is the rational polynomial in
[`inverse_image_trimmed_130.json`](../certificates/inverse_image_trimmed_130.json).
Write its leading coefficient as \(L\), and put

\[
r=1+10^{-8},\qquad w_c=52.18435.
\]

The required fixed-degree inequality is

\[
(2|P(z)|+1)^{53}|1-z|^{780}\le e^{130w_c}
\quad (|z|=r).
\]

## Root distances become affine functions

The certificate gives 130 disjoint rational intervals \([a_i,b_i]\) inside
\([-1,1]\). Exact endpoint sign comparisons and the intermediate value
theorem give one zero \(t_i\) in each interval. The exact degree is 130, so

\[
P(X)=L\prod_{i=1}^{130}(X-t_i).
\]

For \(x=\operatorname{Re}z\) on the circle, \(-r\le x\le r\), and

\[
|z-t_i|^2=r^2-2t_ix+t_i^2.
\]

Define the outward affine majorant

\[
g_i(x)=r^2+a_i^2+2(b_i-a_i)(r+1)-2a_ix.
\]

Indeed,

\[
(t_i^2-2t_ix)-(a_i^2-2a_ix)
=(t_i-a_i)(t_i+a_i-2x)
\le 2(b_i-a_i)(r+1).
\]

Each \(g_i\) is strictly positive at both endpoints \(-r,r\), as an exact
rational check shows. It is therefore positive throughout the interval.
Set

\[
B(x)=L^2\prod_i g_i(x),\qquad D(x)=r^2+1-2x.
\]

Then \(|P(z)|^2\le B(x)\) and \(|1-z|^2=D(x)\).

## A global tangent inequality

For a positive affine function \(g\), the inequality \(1+u\le e^u\)
implies

\[
g(x)\le g(c)\exp\left(\frac{g'}{g(c)}(x-c)\right).
\]

Multiplying these inequalities, including the factor \(D^{780}\), gives

\[
F(x):=B(x)^{53}D(x)^{780}
\le F(c)e^{S(c)(x-c)},
\]

where the rational slope at a rational point is

\[
S(c)=53\sum_i\frac{-2a_i}{g_i(c)}-\frac{1560}{D(c)}.
\]

No numerical maximization result is assumed. A numerical search selects the
tangent point; exact rational inequalities certify the point that it found.

## The central interval

Use

\[
c=-\frac{14335156893077131701}{10^{20}},\quad
\varepsilon=10^{-10},\quad M=10^{10}.
\]

The certificate checks \(2r|S(c)|\le\varepsilon\). Therefore
\(F(x)\le F(c)e^{\varepsilon}\) throughout \([-r,r]\).

When \(|x|\le3/4\), completing the square gives

\[
|z-t_i|^2\ge r^2-x^2\ge r^2-9/16.
\]

An exact comparison proves
\(L^2(r^2-9/16)^{130}\ge M^2\), hence \(|P(z)|\ge M\).
Consequently

\[
2|P(z)|+1\le(2+M^{-1})|P(z)|.
\]

Let \(A_c\) be the recorded integer upper bound for \(B(c)\). The
central finite comparison is

\[
(2+M^{-1})^{106}A_c^{53}D(c)^{780}
\le e^{260w_c-\varepsilon}.
\]

The tangent inequality now bounds the square of the required expression by
\(e^{260w_c}\).

## The two outer intervals

At \(c_-=-3/4\) and \(c_+=3/4\), the exact slope checks give
\(S(c_-)\ge0\) and \(S(c_+)\le0\). Thus

\[
F(x)\le F(c_-)\quad(x\le-3/4),\qquad
F(x)\le F(c_+)\quad(x\ge3/4).
\]

For every \(p\ge0\), splitting into \(p\le1\) and \(p\ge1\) proves

\[
(2p+1)^{106}\le3^{106}(p^{106}+1).
\]

Also \(D(x)^{780}\le(r+1)^{1560}\). The two remaining exact comparisons,
with the recorded integer bounds \(A_-,A_+\), are

\[
3^{106}\left(A_\pm^{53}D(c_\pm)^{780}+(r+1)^{1560}\right)
\le e^{260w_c}.
\]

Taking nonnegative square roots proves the desired circle bound in all
three regions.

## How the exponential comparisons are checked

For each rational target exponent \(X\), use \(j=19574\) and a rational
upper bound \(h=693147180559945310/10^{18}\) for \(\log2\). The recorded
argument \(t=X-jh\) is nonnegative. Therefore

\[
2^j\sum_{k=0}^{15}\frac{t^k}{k!}
\le 2^je^t\le e^X.
\]

The certificate compares the rational left side of each desired inequality
against this rational Taylor lower bound. Lean checks those comparisons by
kernel reduction, and proves the logarithm enclosure and Taylor remainder
inequalities separately. The integer caps on \(B(c)\) keep intermediate
fractions smaller without changing the logical argument.

The main Lean modules are `RootCircle`, `Sharp130Finite`,
`Sharp130Tangent`, `Sharp130CircleCore`, and `Sharp130Circle`, under
`Submission/Refinement/`. The root brackets and factorization are supplied by
`Trimmed130ZeroData`, the integer sign chunks, and `Trimmed130ZeroRoots`.
