# Proof-only dependency refactors

The submission vendors the pinned upstream source at
`aa2a42f4f3835347ad46608779e22dd52c2dc7bf` and prefixes its local imports with
`Submission.`. The converter also applies a small, explicit list of guarded
proof-only changes. It requires exactly one match for every source replacement.
The manifest records both the original and converted file hashes.

## Lean 4.34.1 Boolean proof compatibility

In `CatalanMeasure/GenD/Cert/Assembly.lean`, the proof of `blockOK_ofS` uses an
existing Boolean equality hypothesis directly. The older proof applied
`of_decide_eq_true` although the remaining goal was already that equality.
No statement or definition changes. The repaired module compiled, and its
printed certificate axioms are the three allowed logical axioms.

## Elementary atom facts

`GenD/Analytic/WeightedAtom` previously imported the fixed-design `Lemma6`
development for only two elementary facts: invariance of the absolute
determinant under equivalent finite indices, and the mass of the real-pair
measure. The copied proofs now live in
`Submission/Improvement/Fields/AtomMeasureFacts.lean` under distinct names.
The import and the single use site change; all weighted-atom statements stay
the same. The refactored generic chain through `DeltaChain` and the new
`DecayEventually` theorem compile.

## Elementary denominator facts

`GenD/Nonvanishing` previously imported the fixed-design
`SquareNonvanishing` development for `prime_mul_div_den_unit`. That lemma
and its small helper `rat_div_den_unit` now live in
`Submission/Refinement/PrimeDenominator.lean`.

Their statement and proof bodies are byte-identical to the pinned originals.
[`prime_denominator_provenance.json`](../certificates/prime_denominator_provenance.json)
records the source identities and comparison. Only the import and helper
namespace at the use site change. This removes unrelated fixed-design
numerical certificates from the target's dependency graph.

The two dependency refactors reduce the reachable local module count from
1,411 to 1,135 at this checkpoint. The original upstream files remain available
in the vendored tree for provenance. These changes reduce build work; they
neither assume nor weaken a mathematical premise.
