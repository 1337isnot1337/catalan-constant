# Catalan constant: irrationality exponent research

Goal: improve the best upper bound on the irrationality exponent of Catalan's constant

\[
G=\sum_{n\geq0}\frac{(-1)^n}{(2n+1)^2}.
\]

The [Big O Speedrun table](https://bigospeedrun.com/other/catalan), checked on 2026-10-30, lists the leading claimed bound as **532**, due to S. Litsey. A smaller exponent is better. The site labels this result **Claimed**, not independently Lean Verified.

## Current status

Research is in progress. This repository does not yet claim an improved bound. We are auditing the published constants and exponent criterion, searching the five-parameter construction, and improving finite certificates. Proven implications, numerical candidates, and unresolved assumptions will be stated separately.

## Starting sources

- [S. Litsey, catalan-irrationality-measure](https://github.com/slitsey/catalan-irrationality-measure), leaderboard record commit `4d338bf4c56ddfa60657b64d23100c3404d039ad`.
- [M. C. S. Carreira, catalan-designs](https://github.com/MarcosCarreira/catalan-designs).
- [OpenAI, Catalan's constant is irrational](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Catalans-constant-is-irrational-September-24-2026).

The leading construction uses design `(58, 9, 3, 5, 3)`, polynomial degree parameter `d=53`, neighbourhood exponent `rho=301.54258`, decay `eta=30.041`, and `delta=2.9e-7`. Its stated criterion is `M > d*rho/(eta-4*d*delta)`, approximately `531.99924`.

Any result here that reuses this construction will explicitly credit the original authors and identify its upstream dependencies. New written arguments are not represented as Lean formalizations.
