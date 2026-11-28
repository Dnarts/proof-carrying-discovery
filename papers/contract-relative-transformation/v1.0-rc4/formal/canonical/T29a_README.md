# CRTT-T29a-v0.1 — Relative Evidence, isolated repair gate

Status: **VERIFIED on Lean 4.36.0.** Gate T29a is closed: all fifteen modules
compile with exit 0 and zero diagnostics; 395 inherited + 21 RelativeEvidence =
416 axiom reports are audited by exact name and by fully-qualified name, with
only `propext` and `Quot.sound` permitted; no `sorryAx`, no `Classical.choice`,
no warning, no error. Toolchain
`Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117)`.
See `KERNEL_CHECK.log`.
This is the first of three repair gates replacing the failed monolithic T29
candidate. The gate has since been compiled and audited successfully; see the recorded
outcome below. The failed T29-v0.1 remains
historical; its exact archive and raw compiler log are not available in this
preparation environment. The reconstruction uses the previously presented
source and Hermes' reported diagnosis, not a byte-for-byte extraction of the
failed revision. See FAILURE_REPORT.md and NEXT_GATES.md.

## Parent and integrity

Parent: CRTT-T28-v0.1.1-verified (1).zip. The 58 entries of its main manifest
passed, and the four omitted historical manifests were independently compared
with their original archives. All 14 parent Lean modules are unchanged. Both
strict auditors replayed all 395 reports from the supplied parent kernel log.
That is a log replay, not a new parent compilation. All original parent files
are retained; the parent README, manifests, logs, runner and next-gates file
are stored under T28_ names. This revision's main manifest covers every payload
file except itself, including all historical manifests.

## Scope

Only RelativeEvidence.lean is introduced. It defines a correlated row test and
proof-carrying offers indexed by the exact T28 continuation. It intentionally
does NOT define a session, a dependent admission decision, a charged transition,
or an indexed recursive trace. In particular it does not attempt to prove the
failed check_accepted_iff, apply_charge, apply_funds, Step or Chain lemmas.

For actual old/new remaining completion costs O,N and total proposed transition
fee F, a row (L,U) bounds O >= L and N <= U jointly. The actual-pair coverage
proof requires at least one such row. If all rows satisfy F+U<L, paired_gain
implies F+N<O. The row scan can be vacuously true for the empty list; coverage_nonempty and offer_nonempty explicitly exclude that list from a typed offer.
Subset refinement preserves passing arithmetic, but a new offer must separately
carry coverage of the actual pair. No claim of truth from a passing scan alone.

Candidate retains T28's exact root, frontier rebase, certified rules, equal base
fees, reserve proof and migration cost. proposed_reserve explicitly connects the
candidate's stated reserve to the actual installed continuation's reserve.
proposed_same, proposed_fees and proposed_bill_le_reserve expose the verified T28
properties to the next gate. fromAbsolute preserves the exact T28 proposed
continuation and embeds the old absolute economic test in one row.

The T27 adapter fromDecision uses the decision certificate to bound the new
bill by reference + epsilon in each compatible hypothesis. It requires an
additional joint witness relating the incumbent and the selected controller's
bills to the two exact continuation costs. A strict incumbent margin is needed
in decision_offer_gain: low regret or optimality alone cannot authorize a
strictly profitable switch. This adapter does not acquire, validate or generate
its external hypotheses; preparation cost is not optimized or hidden by proof
erasure. Migration and checking fees are both included in the gain inequality.

## Evidence and limits

The independent Python check covers 33,800 jointly covered actual pairs,
10,204 subset refinements, 78,800 actual-coverage refinement cases, 625
singleton embeddings and 10,000 T27 bridge cases. 42 small finite row-gate
cases demonstrate a strictly stronger paired test than the rectangular test.
The T28 depth-obstruction fixture has old/new modeled completion bills 7/1;
fees 2 give net gain 4. An extra synthetic row (70,64) preserves the passing
relative test while making mixed independent extrema fail. It is a deliberately
constructed conservative enclosure, not a second measured physical execution
world. Tests include empty and uncovered evidence and no strict improvement.
These are independent finite checks, not execution of Lean or measured runtime.
No theorem about arbitrary tariff changes or arbitrary algorithms is claimed.

## Acceptance gate

Lean 4.36.0. Expected: **15 modules, 395 inherited + 21 new = 416 reports**.
Only propext and Quot.sound are allowed by the unchanged auditors. Compiler
exit zero, no errors or warnings, every exact report, manifests and finite
checks must pass. No declaration is removed merely to pass the audit. The
new module is small enough for isolated diagnosis. No local Lean executable
is installed in the preparation environment; the runner fails closed (127).

    set -o pipefail
    bash run_verify.sh 2>&1 | tee ../T29a-KERNEL_CHECK.log

**Recorded outcome.** `run_verify.sh` exits 0 on a fresh extraction of this
archive, with no repair needed to any module. Every module reports `Lean exit=0`
and passes both auditors, for 416 reports in total. `RelativeEvidence.lean`
reports `21/21 axiom reports; Lean exit=0;
dependencies={'Quot.sound': 17, 'propext': 17}`. All ten auditor fixtures pass,
and the finite checks pass, including the new relative-evidence model: coverage,
refinement, singleton embedding, the T27 margin and the T28 reference witness.

The gate criterion stated in `NEXT_GATES.md` for T29a — 21 new reports passing on
Lean 4.36.0 alongside the 395 inherited ones, with exact source names and axioms
audited — is met.

T29b and T29c are NOT supplied as executable modules: their interfaces are frozen
as proposed contracts in `NEXT_GATES.md`. `KERNEL_CHECK.log` is included in this
archive and records the run; a recorded PASS is not a substitute for kernel
acceptance on the consumer's machine.
