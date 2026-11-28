# CRTT v1.0 — T32 release candidate 1

**Status: VERIFIED on Lean 4.36.0 — release candidate kernel-checked.** All
twenty-one modules compile with exit 0 and zero diagnostics; 524 inherited + 18
Release = 542 axiom reports are audited by exact name and by fully-qualified
name, with only `propext` and `Quot.sound` permitted; no `sorryAx`, no
`Classical.choice`, no warning, no error. `ReleaseMain.lean` is the executable
entry point and declares no theorems. Toolchain
`Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117)`.
The journal is `T32-KERNEL_CHECK.log`, kept outside this immutable package.
The T31 parent is verified according to its supplied Lean 4.36.0 log: 19
modules, 524/524 audited reports, zero errors/warnings, no `sorryAx` or
`Classical.choice` in those reports. Both strict auditors were replayed locally;
all 19 parent sources are unchanged. The previous 112 listed hashes, 18 upstream
pins and nine separately archived historical manifests passed. The parent is
pinned by `PARENT_ARCHIVE_SHA256.txt`. Its finite closure test output was
reproduced byte-for-byte. The new `Release.lean` contains 18 new audit targets
(542 total); `ReleaseMain.lean` is the CLI with no additional proof targets.
The preparation environment has no Lean executable. The new declarations and
CLI must pass the final acceptance command; Python success is not that pass.

## One execution boundary

`CRTT.Release.run` takes fixed indexed source/target tasks, a typed funded
`Machine`, fixed `Provider`, declared schedule length, and a thunk returning
an actual connected `MetaClosure.Run`. `runList` builds such a Run from a
finite list of typed T31 plans. Both use the same verified `closeRun`: execute
the installed finite policy, then complete the remaining funded root search.
The returned `Closed` object retains the connected upgrade trace, actual
acquisition events, execution/finish equalities and the final Session. The
caller's preparation work is not automatically free. Closed witnesses can
supply state-specific certified transition schedules, while the list runner
uses generic factories typed at the current state. No new search method,
learned-state migration, parser of untrusted certificates, or meta-level is
introduced. `runList_eq_close` is an explicit definitional bridge to T31.

The funded reference scope intentionally excludes an unfunded initial root.
This is not a general input interface `budget -> solve arbitrary problem`.
A deferred or blocked intermediate action does not cause false completion:
the existing protected fallback completes the fixed root. The terminal tag
`impossible` is the empty fully exhausted canonical certificate list, which
implies no T20 morphism exists; `complete` is a nonempty complete list of
canonical representatives. An unfunded problem is outside this API and must
not be assigned either status. T22.9 retains its separate inconclusive prefix
interface. No unsupported general unresolved-state API has been invented.

## Final obligations (new source targets)

`result_complete`, `result_exhausted`, `result_impossible_iff`, `result_funds`,
`result_history`, `result_bill`, `result_steps` lift the verified closure laws.
The final empty list is equivalent to nonexistence of a morphism, not merely
absence of a result so far. `summary_exhausted`, `summary_bill`, and
`summary_conserved` connect the readable report to the actual proof-bearing
result. Reporting does not recompute `discoverAll` or `policyBill`.

`Summary` retains source/target tables and dimensions, initial and final
balance/spend/reserve, final jobs, actual finish bill, predecessor/final
canonical maps, all upgrade verdicts including deferred, paid upgrade history
with bounds and trees, observed answers, prepared offer rows/migration/labels,
root attempt verdicts, ordered relative journal, legacy history and ordered
search receipts, installed tree and fee schedules. The exact functions and
proofs remain in the typed value; the displayed rule costs and metadata do
not identify or serialize arbitrary rule functions. Prior legacy ledgers are
ordered separately; no global timestamp order across old ledgers is fabricated.

## Fixed nine reference cases

See `FINITE_RELEASE.log` and `FINITE_RELEASE.json` (independent Python output).

| Case | All-in bill | Terminal | Intermediate outcome |
|---|---:|---|---|
| baseline | 7 | impossible | keep |
| single | 6 | impossible | one accepted meta-upgrade |
| mixed | 7 | impossible | accepted then paid rejection |
| double | 6 (from 8) | impossible | two accepted meta-upgrades |
| fallback | 7 | impossible | two free deferred plans, observation blocked |
| liquidity-baseline | 4 | impossible | root switch accepted |
| liquidity-rejected | 10 | impossible | paid meta-rejection, then root liquidity rejection |
| nonempty | 11 | complete | two canonical maps |
| predecessor | 11 | complete | one pre-existing certificate, two at completion |

All numbers are explicit modeled tariffs, not wall-clock or physical resource
measurements. For the positive policy witness 7 -> 6, the final 6 includes one
unit each for setup, query, preparation, root validation, migration and root
completion. The old baseline is deliberately specified; it is not the best
possible policy on every objective. The two-acceptance case starts from a
redundant incumbent. The liquidity counterexample establishes that a paid
rejection can change future affordability; a blanket fee-only monotonicity law
for all-in policy bill would be false. The predecessor case checks completion
of the actual partly explored frontier, not a restart from scratch.

The separate Python comparator checks actual Lean CLI metrics, canonical map
lists, predecessor maps, per-case statuses, observed answers, prepared paired
rows/migration, ordered debits and paid search steps. Its 12 synthetic parser
controls (one clean and 11 corrupted) are explicitly marked as parser fixtures,
not runtime or kernel evidence. Independent Python fixtures have passed. The
actual Lean output comparison is still required.

## Verify the final candidate

Lean 4.36.0 is pinned in `lean-toolchain`; the runner checks the same compiler
commit recorded in the parent. Python 3 (standard library only). Run from a
fresh extraction, saving the log OUTSIDE the immutable manifest:

```bash
set -o pipefail
bash run_verify.sh 2>&1 | tee ../T32-KERNEL_CHECK.log
```

This is one fail-closed command: complete manifest, 19 upstream pins,
standalone historical checks, old and new audit fixtures, exact toolchain,
20 proof modules + CLI compilation, 542 exact qualified audit reports,
all inherited finite stands, the 9 new independent reference cases, the
actual `lean --run ReleaseMain.lean` output and its reference comparison.
CLI diagnostics or nonzero exits also fail. No log is overwritten in the
release directory. `verify_integrity.py` rejects unlisted/missing flat files.
In an environment without Lean it fails closed with exit 127.

## Release freeze

See `ARCHITECTURE_RU.md`, `RELEASE_ACCEPTANCE.md` and `DEPENDENCIES.txt`.
The two immutable historical ZIPs preserve earlier standalone results;
these are NOT imported by the T19–T32 executable stack and their separate
historical audit policies are not counted as new strict-stack declarations.
No T33 is planned. If a mandatory condition fails, repair the integration
within T32 or explicitly report the blocker. Upon the final pass, label this
scope CRTT v1.0 and freeze the source bytes, manifest, toolchain, and actual
verification log. Further generalizations are independent research.

## Limits

This is a deterministic finite proof-carrying reference implementation.
It does not guarantee the best arbitrary algorithm, unrestricted self-rewrite,
indefinite improvement, physical speedup, external IO/persistence safety,
statistical validity, automatic discovery of all proof factories, or arbitrary
paradigm translation. The provider, task pair, tariff authority and checker
stay fixed within the episode; schedules, economic evidence and proofs are
supplied under explicit types. The pure `Unit` thunks model operations, not
real-world side effects. The proof kernel is never replaced. Historical and
new finite cross-checks are distinct from Lean kernel verification.

## Recorded outcome

`run_verify.sh` exits 0 on a fresh extraction of this archive, with no repair
needed to any module. Every module reports `Lean exit=0` and passes both
auditors, for 542 reports in total. `Release.lean` reports `18/18 axiom reports;
Lean exit=0; dependencies={'Quot.sound': 18, 'propext': 18}`.

Beyond compilation, the run checks the actual Lean runtime projection against
the independent finite reference and reports agreement across every surface:
`{'T32': 9, 'T32CERT': 4, 'T32EVENT': 12, 'T32JOURNAL': 18, 'T32PRIOR': 1,
'T32SEARCH': 47, 'T32STATUS': 9, 'T32UPGRADE': 8}`. Nine independent release
fixtures, complete canonical membership, predecessor preservation and ordered
paid ledgers also pass.

This package is immutable: `verify_integrity.py` fails closed on any unlisted
file, so the verification journal lives **outside** the archive, next to it, as
`T32-KERNEL_CHECK.log`. Run:

    set -o pipefail
    bash run_verify.sh 2>&1 | tee ../T32-KERNEL_CHECK.log

A recorded PASS is not a substitute for kernel acceptance on the consumer's
machine: rerun the script and read the `#print axioms` output yourself.
