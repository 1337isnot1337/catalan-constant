# Verifier source layout and build scope

The official Catalan profile selects `Race.bound` from module `Submission`,
with source root `Submission`, Lean 4.34.1, and the `github-split` runner.
The root theorem states the reduced rational bound `6602911/12500 = 528.23288`.

## Build scope

The trusted Lake configuration declares `[[lean_lib]] name = "Submission"`
without explicit globs. In Lean 4.34.1, `LeanLibConfig` defaults to
`roots := #[name]` and `globs := roots.map Glob.one`. The library build collects
those root modules and their transitive local imports.

Consequently, `lake build Submission` compiles the root theorem's import
closure. It does not compile every file below `Submission/`. Unused alternate
proof modules do not become build gates merely by being present in that
directory. This was checked against the exact Lean 4.34.1 Lake source, including
`Lake/Config/LeanLibConfig.lean` and `Lake/Build/Library.lean`.

## Staging constraints

The verifier still stages every tracked `.lean` file under its permitted source
root, including unimported files. All must satisfy:

- Git mode `100644`, with regular-file contents and no executable bit.
- Ordinary module paths matching
  `[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*`.
- At most 20,000,000 bytes per file and 150,000,000 bytes in total.
- No imports of reserved `VerifierChallenge` or `VerifierAudit` modules.

Only root `Submission.lean` and `Submission/**/*.lean` are used. Repository
Lake configuration, scripts, and precompiled objects are ignored. Mathlib is
provided at the verifier's fixed profile pin. Other imported source roots must
be vendored below `Submission/`.

## Canonical statement and module interfaces

`Submission/CatalanStatement.lean` is an unchanged copy of the trusted statement.
Its SHA256 is
`9ba7370f1256ef680ccf674e653b5456735c478f9ac80fcffc90f130ac4a2ce6`, matching the
official Catalan profile. The verifier compares the submitted theorem against
its own trusted statement; it does not trust this local copy.

The statement is an old-style Lean file. The root entrypoint and its direct
bridges therefore also use old-style imports. Newer `module` files do not
import those old-style files. The source closure includes the required
`Submission/CatalanCore` modules as well as the other vendored roots.

## Reproduce the layout audit

Run from the repository root:

```sh
python3 scripts/audit_submission_layout.py .
```

After all source edits are complete, record the exact final snapshot:

```sh
python3 scripts/audit_submission_layout.py . --output certificates/lean_source_audit.json
```

The audit checks source sizes, ordinary file paths and modes, the canonical
statement hash, import cycles, missing local imports, reserved imports,
unexpected external roots, and newer-module imports of old-style local files.
The output records source hashes and the reachable module order. It does not
prove that the Lean code compiles. It also cannot certify the remote Git tree
modes: the exact submitted commit must contain every intended Lean file at mode
`100644`.

## Proof gate

The final build must succeed and `#print axioms Race.bound` must report only
`propext`, `Classical.choice`, and `Quot.sound`. The official verifier then
compares the exact target and replays the proof in Lean's kernel. A source
layout audit or an author-supplied build log does not replace that receipt.

## Primary sources

- [Official Catalan profile](https://github.com/bigospeedrun/verifier/blob/main/profiles/direct.json),
  inspected Git blob `6b8989dc9392af957b0a64e8e2549b192837788c`.
- [Verifier controller](https://github.com/bigospeedrun/verifier/blob/main/scripts/verifier.py),
  inspected Git blob `5d03bd81b432392a885f330cccd1a9a653cb1101`; see
  `plan_sources`, `lakefile`, `prepare`, and `build`.
- [Layout conversion guide](https://github.com/bigospeedrun/verifier/blob/main/docs/convert-layout.md)
  and [execution guide](https://github.com/bigospeedrun/verifier/blob/main/docs/execution.md).
- [Lean 4.34.1 library configuration](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Config/LeanLibConfig.lean)
  and [library build](https://github.com/leanprover/lean4/blob/v4.34.1/src/lake/Lake/Build/Library.lean).
