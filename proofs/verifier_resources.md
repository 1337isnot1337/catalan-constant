# Verifier resources and certificate layout

The official Catalan verifier uses a split build and verification workflow.
Its trusted entrypoint sets `LEAN_NUM_THREADS=4`. The controller applies a
400% CPU quota, a 14G memory maximum, no swap during the build and initial Lean
check, and `TasksMax=4096`. Each job has its own 320-minute controller deadline.
The build stops 15 minutes early for artifact packing, leaving a maximum of
305 minutes measured from that job's prepare step. Only the later nanoda phase
receives swap.

Submission Lake settings and shell scripts cannot change these limits.

## Measured local compiler sizes

A snapshot during final proof preparation recorded these peak resident sizes:

| Module | Peak RSS |
|---|---:|
| `ResidualBlock053` | 2,123,792 KiB |
| `ResidualBlock025` | 2,130,948 KiB |
| `WCells` | 1,592,716 KiB |
| `HPrime` | 1,488,112 KiB |
| `HmProf` | 1,205,036 KiB |

The local arithmetic Lake process peaked at 907,264 KiB and had three active
child Lean compilers when configured with `LEAN_NUM_THREADS=3`. The residual
checks ran as two separately bounded compiler processes.

A later one-worker retry measured about 3.1 GiB RSS for the heavier arithmetic
module `CellP3`. Earlier `CellP1`/`CellP3` attempts were killed for memory pressure
when two residual compilers, three arithmetic jobs, and a helper check overlapped
locally. The heavy arithmetic cells were then retried sequentially. This is a
concrete reason to bound overlapping local build jobs.

Four residual compilers at the observed maximum would account for about
8.13 GiB of summed RSS, or about 9 GiB including the observed Lake-controller
peak. A heavier mixed wave with two arithmetic compilers at 3.1 GiB each and two
residual compilers at 2.1 GiB each accounts for about 10.4 GiB before the
controller and other overhead. These measured cases suggest headroom under the
hosted limit, but neither is a universal memory bound or a guarantee that the
scheduler runs at most four compilers. Summed RSS can also count shared mappings
more than once.

## Why the certificate is split into modules

The 98 new residual cells are divided into 54 Lean modules. Each uses
`Elab.async=false`, so many heavy independent proof evaluations are not
elaborated concurrently inside one module. All finite comparisons retain
ordinary kernel checking; no evaluator shortcut or additional axiom is used.

Lake runs compiler jobs through blocking `IO.Process.output`. The observed
local build ran roughly one compiler per Lake worker. However,
`LEAN_NUM_THREADS` is not a process-memory semaphore: Lean can create replacement
workers when a task waits on another task. The verifier itself documents this
behavior. A hard concurrency guarantee therefore does not follow from the
number four alone.

The present separate-module layout is retained on the measured evidence. If a
concrete later peak threatens the hosted limit, an ordinary source dependency
layout can restrict concurrency: for example, block `i` can import block
`i-2`, producing two independent chains. Such a change preserves every theorem
statement, finite witness, and kernel check, but adds sequential build time and
larger per-module import closures. It should not be applied without accounting
for that tradeoff.

The completed hosted receipt remains the evidence that the full proof fits
the verifier's actual limits.

## Primary sources

- [Trusted verifier entrypoint](https://github.com/bigospeedrun/verifier/blob/main/scripts/inside.py),
  inspected Git blob `5806633334420e499230ac38c36b19b5a0e7ff08`.
- [Verifier controller](https://github.com/bigospeedrun/verifier/blob/main/scripts/verifier.py),
  inspected Git blob `5d03bd81b432392a885f330cccd1a9a653cb1101`.
- [Official execution guide](https://github.com/bigospeedrun/verifier/blob/main/docs/execution.md),
  including the split-build and task-limit descriptions.
- Lean 4.34.1 sources: `Lake/Util/Proc.lean`,
  `Lake/Build/Job/Monad.lean`, and `Init/System/IO.lean`.
