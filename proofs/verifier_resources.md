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

The final local run reported an 8 GiB cgroup memory limit. During a later
three-worker pass, the inherited `NormLogP1` certificate was also killed with
exit status 137. The remaining build was restarted with `LEAN_NUM_THREADS=1`.
This local resource failure is distinct from the hosted verifier's 14G limit;
it does not report a failed mathematical assertion.

The norm checks reached about 3.66 GiB RSS, including about 1.18 GiB of stable
file-backed mappings that can be shared. An overlap projection using the local
baseline was `4 * (3.66 - 1.18) + 1.18 + 1.8 + 0.36 = 13.26` GiB. It aligns
four private-memory peaks, counts the common mappings once, and adds about
1.8 GiB of other anonymous and nonreclaimable kernel memory plus 0.36 GiB of
other mappings. The resulting estimate of about 13.3 GiB leaves little room
under the hosted limit. It is not a measured hosted peak or a certified upper
bound; the V-file peaks have not yet been measured.

The source therefore now constrains this particular heavy layer to two
dependency chains. `NormLogP0` and `NormLogP1` both completed before this
scheduling change.

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

The residual block layout remains unchanged. The inherited norm layer uses
the flattened order `NormLogP0` through `NormLogP6`, then `NormLogV0` through
`NormLogV6`. Each file at index `i >= 2` imports file `i - 2`. Consequently,
at most two of these fourteen heavy norm modules can compile simultaneously,
regardless of the number of Lake workers. Other independent modules can still
compile concurrently, so this is not a bound on total build memory.

The twelve new imports preserve every theorem statement, definition, proof
body, finite witness, and kernel check. They add sequential build time and
larger import closures for later norm files. The exact guarded changes are
documented in [the dependency audit](dependency_refactors.md).

A successful hosted run is still needed to establish that the full proof fits
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
