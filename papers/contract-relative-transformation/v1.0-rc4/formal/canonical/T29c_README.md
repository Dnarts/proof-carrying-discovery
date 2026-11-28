# CRTT-T29c-v0.1 — RecursiveTrace (isolated final T29 repair gate)

Status: **VERIFIED on Lean 4.36.0.** The final T29 repair gate is closed: all
seventeen modules compile with exit 0 and zero diagnostics; 451 inherited + 33
RecursiveTrace = 484 axiom reports are audited by exact name and by
fully-qualified name, with only `propext` and `Quot.sound` permitted; no
`sorryAx`, no `Classical.choice`, no warning, no error. Toolchain
`Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117)`.
See `KERNEL_CHECK.log`.
Parent: `CRTT-T29b-v0.1.1-verified.zip`. Its 81 listed SHA-256 records
passed. The six historical manifests excluded by the parent manifest were
compared with their original archives and matched. All sixteen inherited
Lean sources are preserved byte-for-byte. AdmissionAccounting.lean matches
the original T29b candidate. Both strict log auditors passed all 451 parent
reports, including 35/35 AdmissionAccounting reports (only propext and
Quot.sound, zero diagnostics in the supplied compiler log). The original
parent log and manifests remain archived; no new local Lean execution is
claimed. The independent T29b full finite replay exceeded the preparation
runtime limit; its previously supplied log is retained, not relabelled as a
new successful replay. The ten audit-parser fixtures were rerun successfully.

## Scope and repair

Only RecursiveTrace.lean and the independent check_trace.py model are new
mathematical/executable components. T29a and T29b remain unchanged. The
new module is the third isolated repair gate for the failed T29-v0.1. The
old two-endpoint indexed Step/Chain family is NOT reused.

First, `run_shift_spent`, `execute_prefix_bill` and `remainingBill_prefix`
separate ordinary paid execution from histories. The deterministic quote
is independent of the spent field and every quoted fee is positive. Running
a prefix then completing the exact remaining state with its remaining reserve
and a reset local spent counter gives the same total bill as completing the
original state. The same statement covers cycles of the generic quote runner;
it is not a claim of unconditional exhaustion of a cyclic state machine.

`advance` invokes the actual T28 advance, retaining the T29b journal.
`advance_spent`, `advance_funds`, and `advance_objective` lift exact accounting
to the T29b Session. `Preserves` relates endpoints by fixed base fees, appended
certificates, prepended search receipts and relative journal entries, and
unchanged T28 history. Its reflexivity/transitivity and all three local
preservation lemmas use verified T28/T29b behavior.

## Actual actions and connected finite traces

    Action(s) = Advance(fuel)
              | Attempt(RelativeOffer(s.current), baseCheck)
              | Evidence(label, baseFee, affordabilityProof)
    perform(s,a) = actual next Session
    Transition = { before : Session, action : Action(before) }
    after(t) = perform(t.before,t.action)
    ValidTrace([], s, t) = (s = t)
    ValidTrace(x::xs, s, t) = (x.before = s) AND ValidTrace(xs, after(x), t)

`Action` has one state parameter and no computed endpoint index. A Transition
contains no separately chosen after-state. The trace is an ordinary list,
with explicit adjacency evidence. `ValidTrace` is a proposition, not a
claimed executable equality procedure on function-bearing Sessions. Arbitrary
unconnected histories or stale offers are not legal simply because their
endpoints satisfy a desired cost relation. `singleton_valid`, `valid_append`
and `trace_laws` quantify over actual operations and all finite connected
histories, without requiring an optimal policy or a preselected trajectory.

## Economic laws

`objective(s) = spent(s) + remainingBill(s.current)` is specification-only.
For each action the Delta contains net accepted gain, nonproductive overhead,
paid attempt count and accepted count. It is NOT used by perform or the gate
to evaluate prospective runs. A recorded acquisition is a positive external
charge, not a proof of actually obtaining evidence. An accepted attempt's
net gain is the exact decrease of objective after its check and migration
fees; those fees must NOT be counted again as rejection overhead. Rejected
checks add their actual check fee, deferred attempts add zero, and ordinary
execution conserves objective. `Laws` collects these accounting facts plus
preservation. `laws_compose` lifts the identities by addition.

The target theorem `trace_objective` states:

    Phi(final) + sum(netAcceptedGain) = Phi(start) + sum(nonproductiveOverhead).

`trace_final_gain_iff` is the corresponding strict end-to-end improvement
criterion: the completed endpoint costs less than completing the initial
continuation iff accepted net gains exceed rejected-check and external-evidence
charges. `trace_funds`, `trace_paid_bound`, `trace_accepted_bound` and
`trace_preserves` establish resource and historical laws. `trace_completion`
uses the funded T28 root completion property at any endpoint. All sessions
remain typed at the same root task pair. Repeated accepted local improvements
are not necessarily globally cheaper once paid failed attempts are counted.

## Independent finite verification

`FINITE_TRACE.log` is generated by the new independent Python program using
T28's literal finite discovery model and T29b's numeric gate. It is not Lean
execution. It checks 49 task pairs, 149 full connected chains, 887 local
transition laws (396 attempts, 295 advances, 196 external evidence charges),
173 paid attempts and 35 acceptances; 19 chains finish strictly cheaper. It
also checks 146 disconnected predecessor and 146 forged endpoint rejections,
11,760 generic prefix-bill cases, and 35,280 generic spent-counter shifts.
Reference completion is checked against independently enumerated canonical
morphisms. These finite checks do not establish the uncompiled Lean proofs.

Two closed concrete Lean proof candidates and Python examples use the same
verified depth-obstruction task, fixed base and rule tariffs, and T29a paired
enclosure as earlier gates. Original finish bill = 7. A 1-unit external
receipt followed by the profitable switch (net gain 4 including switch fees)
and ordinary completion yields total bill 4. A 5-unit rejected check followed
by the same profitable switch yields total bill 8. The latter is a strict
counterexample to treating local accepted improvements as cumulative gain.
The new Lean witness declarations still require kernel validation.

## Boundaries and closure

The model stays inside static T23 pruning controllers, with proof-bearing
supplied economic evidence. It does not implement an actual evidence-query
service, model synthesis, persistent ledger, measured CPU/RAM tariffs, or
replacement of full LearningDiscovery state. The finite trace theorem is
not an autonomous scheduler or an arbitrary-depth recursive-policy theorem.
Paid attempts are bounded by initial uncommitted balance; free deferred or
zero-work advances can still repeat without limit. T30 must integrate actual
paid observations and a bounded executable policy with the fixed verifier.
T31 closes the chosen invariant under policy replacement, T32 integrates,
checks and freezes. The mandatory finite reference scope is unchanged; see
NEXT_GATES.md and the archived T29a_NEXT_GATES.md.

## Kernel verification

Expected: 17 modules, 451 inherited + 33 new = **484** axiom reports. No
new proof is labelled VERIFIED until all reports pass the existing strict
auditors and Lean exit checks. Lean is absent in the preparation environment.
Run on the same Lean 4.36.0 toolchain, with the log outside the immutable
manifest:

    set -o pipefail
    bash run_verify.sh 2>&1 | tee ../T29c-KERNEL_CHECK.log

**Recorded outcome.** `run_verify.sh` exits 0 on a fresh extraction of this
archive, with no repair needed to any module. Every module reports `Lean exit=0`
and passes both auditors, for 484 reports in total. `RecursiveTrace.lean`
reports `33/33 axiom reports; Lean exit=0;
dependencies={'Quot.sound': 33, 'propext': 33}`. All ten auditor fixtures pass,
and the finite checks pass, including the new trace model: deterministic prefix
bills, connected finite histories, exact cumulative ledger, provenance and root
completion.

This gate carried the hardest defect from the failed monolithic T29 — dependent
case elimination over `Step`/`Chain` whose endpoint index is a computed
projection `(tryRelative ...).2`, which in the monolith produced
`Too many variable names provided at alternative 'attempt'`. It now elaborates
without qualification.

The complete manifest includes all historical manifests. Original archive
filenames referenced inside historical manifests are historical, not current
paths. The runner keeps all existing checks and adds `check_trace.py`.
`KERNEL_CHECK.log` is included in this archive and records the run; a recorded
PASS is not a substitute for kernel acceptance on the consumer's machine.
