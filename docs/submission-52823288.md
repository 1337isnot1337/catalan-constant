# Catalan verifier submission #87

[Submission issue #87](https://github.com/bigospeedrun/verifier/issues/87) was opened on October 30, 2026. An earlier attempt to create the issue through a GitHub integration returned HTTP 403, but the submission was subsequently posted successfully.

The exact source commit is `3c4515314bda407d032cb55f60bfc56b03c1d3f9`. Its published Lean sources and manifest passed the byte and Git-mode audit. The complete local Lean build and final `Race.bound` axiom audit are still pending. The verifier bot acknowledged receipt and posted a file-hash derivation report, but neither is a passing proof check. The result remains Claimed.

[View the submitted issue and verifier responses](https://github.com/bigospeedrun/verifier/issues/87).

## Issue title

[Lean submission] Catalan: μ(G) ≤ 528.23288

## Exact issue body

```markdown
### Problem

catalan

### Repository URL

https://github.com/1337isnot1337/catalan-constant

### Commit SHA

3c4515314bda407d032cb55f60bfc56b03c1d3f9

### Bound

6602911/12500
```

## Verification status

- Written bound: `6602911/12500 = 528.23288`.
- Canonical statement: unchanged.
- Source-layout and published-byte audits: passed.
- Complete local kernel build: in progress.
- Final `Race.bound` axiom audit: pending.
- Official submission: issue [#87](https://github.com/bigospeedrun/verifier/issues/87) acknowledged. The bot states that verification runs periodically and processes one proof at a time.
- Automated derivation report: file-hash comparison posted; it explicitly does not judge the proof.
- Official verification: no passing or failing proof verdict reported as of October 30, 2026.
