# CRTT-T28-v0.1 — Certified Controller Replacement

Status: **VERIFIED on Lean 4.36.0, including ControllerReplacement.lean.** All
fourteen modules compile with exit 0 and zero diagnostics; 352 inherited + 43
ControllerReplacement = 395 axiom reports are audited by exact name and by
fully-qualified name, with only `propext` and `Quot.sound` permitted; no
`sorryAx`, no `Classical.choice`, no warning, no error. Toolchain
`Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117)`.
See `KERNEL_CHECK.log`.

The parent is `CRTT-T27-v0.1.1-verified.zip`, pinned in
`PARENT_ARCHIVE_SHA256.txt`. All thirteen inherited Lean sources are byte-identical.
The parent's 49 listed SHA-256 entries passed; its three uncovered historical
manifests were checked directly against the original T24.7, T25 and T26 archives.
All 352 supplied parent kernel reports were replayed with both strict auditors.
The historical log, README, manifests and next gates are archived under T27_*
names. The new manifest covers every package file except itself.

## Contract and scope

The new module imports DecisionEvidence and implements a concrete gate for
changing a live **static BudgetedPruning controller**. The root tasks S,T
remain fixed by the dependent types. A Controller holds a library of certified
rules and base tariffs. `Offer old` has a proof of equal base tariffs; each rule
cost belongs to the declared external abstract tariff model. No universal
comparison between incompatible accounting systems is claimed.

`rebaseJob` replaces only pending port-rule queues; every port region and every
remaining action list is preserved. It may restart some previously consumed
rule tests on a still-pending node, and those repeated tests are paid normally.
`SameContinuation` requires exact certificate/receipt list equality and an
iff for coverage of every morphism by unresolved jobs. Thus this is stronger
than merely claiming the eventual answer set is unchanged. It does not claim
an unchanged traversal, runtime or list multiplicity after completion.
`same_refl`, `same_trans`, `rebase_same`, `same_correct` are the relation and
preservation obligations. Rebase with the same rule library need not be literal
identity on a partially consumed queue.

`Continuation` packages the current controller, frontier, correctness proof,
sufficient reserve and a potential-bound proof. `Offer old` is indexed by the
exact old continuation, supplies a new controller, reserve Rnew, migration
fee K, upper bound U on the actual remaining completion bill of the candidate,
and lower bound L on the actual completion bill of the incumbent. All bounds
carry proofs. The evidence label is metadata, not cryptographic authenticity.
A different frontier requires revalidation, not mere label or hash matching.

## Admission

Let B be balance, Rold the existing reserve and H the fee for one attempt
(the public wrapper charges baseCheck+1). The numeric gate is:

1. If H+Rold>B, defer without a debit or mutation. This avoids consuming the
   incumbent's ability to complete even when validation fails.
2. Otherwise, if H+K+Rnew>B, reject for liquidity and charge H.
3. Otherwise, if H+K+U>=L, reject for economics and charge H.
4. Otherwise, accept, charge H+K and install the rebased continuation.

This is conservative: it does not admit an attempt that could rescue an
underfunded incumbent or that would require risking the protected fallback.
A typed `Admission` constructor carries the guard proof, and `applyAdmission`
uses the very same decision object. No untyped candidate callback executes
inside the numeric checker. This is a pure Lean interface; it is not a hostile
input decoder, proof file parser, or process sandbox. Proof-bearing offers are
already kernel-typed before the checker runs; the production cost of obtaining
and independently checking those proofs is NOT automatically charged by this
module. The supplied H models the admission attempt, and K models deployment.
Any additional acquisition expense must be accounted for explicitly in a
larger ledger or in the comparison horizon. Do not label this full-lifetime
amortization. Rejected paid attempts are real costs, not undone by a later win.

## Execution and accounting

`Live` enforces current.reserve <= balance. `advance` executes a bounded prefix
of the actual T23 quote function using the reserved amount, retains the surplus
balance and carries the remaining reserve forward. `finish` executes that
same continuation to exhaustion. No budget charge is made merely because
funds are reserved. `spent` is derived from the existing search receipts plus
replacement attempt receipts. Each accepted/rejected record preserves the
original continuation, the proof-bearing offer, balance before the attempt,
check fee and typed reason/status. Old history is never deleted. Deferred
attempts leave the state identical (they are not paid events).

The source claims:
- `checked_accept_iff`, `apply_liquid`: exact numeric gate and preserved funding.
- `apply_nonaccepted_current`, `apply_same`, `tryReplace_same`: rejection keeps
  the old continuation and acceptance preserves unresolved semantics.
- `apply_balance`, `apply_exact_charge`, `apply_conserves`, `advance_conserves`:
  precise resource conservation and verdict-dependent paid expense.
- `apply_history`, `advance_history`, `advance_certificates`, `advance_receipts`:
  preservation of actual accumulated evidence.
- `finish_full`, `finish_exhausted`, `finish_after_attempt_full`: completion
  continues to return exactly the reference certificate membership, regardless
  of the admission outcome.
- `economic_sound`, `accepted_finish_gain`, `tryReplace_accepted_gain`: strict
  gain for the accepted switch followed by immediate completion relative to
  continuing the exact old controller, including this check and migration.
  This is conditional on certified cost bounds and fixed tariff semantics.
  It is not an online optimality or unconditional benefit theorem for a stream
  of attempted switches.

## Independent finite check

`check_replacement.py` operates on the inherited finite T23 reference runner
and literal h,p,a enumeration. It independently executes 400 task pairs,
2000 prefixes, 34705 attempts (1753 accepted, 10701 rejected for liquidity,
10251 rejected for economics, 12000 deferred), and all 34705 resulting full
completions. It checks 158831 operational-pair coverage comparisons, 2000
migration compositions, 746 retained action suffixes and 12122 retained
port regions. There are 50 accepted replacements with a live action job and
3 with already emitted certificates. Stale offers and base repricing are
rejected by the Python model. The closed depth witness costs 7 to finish
unchanged and 3 after replacement (1 validation + 1 migration + 1 root rule),
with no change in base tariffs. A balance of 100 defers a check that would
consume the old reserve; a balance of 101 permits the check but not the
candidate's declared 100-unit reserve plus migration. A sequence of three
accepted policy changes strictly improves the declared completion total;
repeated rejected checks consume only surplus until deferred.

The finite test constructs prospective cost evidence OFFLINE from exact
completion simulations. This is not an operational way of obtaining cheap
evidence, a measurement of wall-clock time, or a test of compiled Lean.
The program tests its own reference-model calculations, not the new Lean code.

## Boundaries

No formal bridge yet converts a T27 regret certificate directly into the
strict pair of bounds required by Offer. A regret bound relative to an
arbitrary benchmark is not itself a strict improvement over the incumbent.
The scope is static pruning continuations; transporting all state of a live
LearningDiscovery machine, arbitrary controller code, persistent external
identity, crash durability, simultaneous liabilities, and autonomous policy
replacement remain open. The cost model does not bound memory, actual
verification time or physical execution; holding historical snapshots also
has costs not quantified by the abstract tariffs here.

## Verification

Expected: 14 modules, 352 inherited + 43 new = **395** axiom reports. The
strict auditors and ten fixtures are unchanged. The runner compiles into a
temporary directory, audits names and axioms even on compiler failure, rejects
warnings/errors/unknown axioms/missing reports, and runs all inherited finite
checks plus check_replacement.py. All historical logs are retained as evidence
of their original revisions only.

    set -o pipefail
    bash run_verify.sh 2>&1 | tee ../T28-KERNEL_CHECK.log

**Recorded outcome.** `run_verify.sh` exits 0 on a fresh extraction of this
archive, with no repair needed to any module. Every module reports `Lean exit=0`
and passes both auditors, for 395 reports in total. `ControllerReplacement.lean`
reports `43/43 axiom reports; Lean exit=0;
dependencies={'Quot.sound': 40, 'propext': 43}`. All ten auditor fixtures pass,
and the finite checks pass, including the new controller model: repeated
replacements, stale evidence, rejected-check charge and fallback reserve
protection, plus the actual finite frontier model.

`KERNEL_CHECK.log` is included in this archive and records the run. A recorded
PASS is not a substitute for kernel acceptance on the consumer's machine:
rerun the script and read the `#print axioms` output yourself.
