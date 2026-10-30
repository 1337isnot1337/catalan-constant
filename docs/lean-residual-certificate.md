# Trimmed residual certificate in Lean

The residual field uses the same trial sequence as the upstream K590 certificate:

\[
R(x)=-\frac{53}{58}\log(1+x^2)-2\sum_{k\ge1}\frac{u_kT_k(x)}k.
\]

The new support is

\[
E=[-2409/2500,-19501/100000]\cup[98749/1000000,1],
\]

and the required cap is \(R(x)\le-883/10000\) on \(E\).

`Submission.Improvement.Fields.ResidualTrimmed` assembles 54 blocks containing
98 Taylor cells. The cells use a grid of spacing \(2^{-40}\). The cover extends
each rational support endpoint outward by less than two grid spacings.

Every block and cell is checked through the existing upstream `CellCert`
soundness theorems. The checks include:

1. A rational logarithm enclosure at the cell center, including complex
   arguments in every quadrant.
2. The first five derivatives of the residual, split into the finite
   Chebyshev polynomial and the 76 rational derivative poles.
3. Four further derivatives of the polynomial part and a block bound for
   its ninth derivative. The block bound uses the existing Taylor table
   through derivative order 70.
4. Positive lower bounds for all pole distances on the cell.
5. The final Taylor inequality and the complete cover of both intervals.

The imported `Cert590.RTab` table and `Cert590.RZ` coefficient identity connect
the finite polynomial to the actual trial. The imported `resSpecW_sound`
theorem connects the computed values and derivatives to the infinite residual
series. No Python value is accepted as a real-number bound without this link.

## Reproduction

The generator selects rational witnesses. The Lean kernel checks the resulting
proofs independently:

```sh
python3 scripts/generate_residual_lean.py
lake build Submission.Improvement.Fields.ResidualTrimmed
```

The selected data are also recorded in
`certificates/residual_lean_witness.json`. To regenerate the Lean files directly
from this witness, use `python3 scripts/generate_residual_lean.py --from-witness`.
This faster path has the same kernel checks. The generator's derivative and pole
calculations were compared exactly with the upstream `RM000` first-cell
witnesses before generating this cover.

## Near field and the eventual energy contract

`NearTrimmed` proves the stronger main near-field cap
\(-0.781455472\), using a rational cubic root bracket
\([0.7758761519,0.7758761520]\). The logarithmic coefficient is bounded below
by \((48-10^{-6})/58\) for \(N\ge10^6\). The first trial coefficient exceeds
the rational lower bound \(0.1815069024687\).

For \(N\ge10^7\), the grouped correction satisfies
\(\log(1+y^2)/(58N)\le1/(58\cdot10^7)<2\cdot10^{-9}\).
The complete grouped near field therefore has cap \(-0.78145547\).

`SecondEventually` replaces the upstream all-positive-scale near-field
hypothesis with an eventual hypothesis. Its proof intersects that event with
the other eventual events already used in the second-energy argument.
`DecayEventually` transfers the resulting energy estimate through the same
grouped-product, marked-sheet and weighted-atom arguments. It accepts an
arbitrary quadrature support predicate.
