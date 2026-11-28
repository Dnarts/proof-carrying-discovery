# CRTT-T29b-v0.1 — Admission Accounting, isolated repair gate

Status: **VERIFIED on Lean 4.36.0.** Gate T29b is closed: all sixteen modules
compile with exit 0 and zero diagnostics; 416 inherited + 35 AdmissionAccounting
= 451 axiom reports are audited by exact name and by fully-qualified name, with
only `propext` and `Quot.sound` permitted; no `sorryAx`, no `Classical.choice`,
no warning, no error. Toolchain
`Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117)`.
See `KERNEL_CHECK.log`.

Parent: `CRTT-T29a-v0.1.1-verified.zip`. Its 70 listed SHA-256 entries
passed, all five omitted historical manifests match their original archives,
and all 15 inherited Lean sources are byte-identical. The new manifest covers
all payload files except itself. Both strict parent-log auditors were replayed
successfully over all 416 reports. RelativeEvidence.lean is byte-identical to
the original T29a candidate. The compiler evidence is archived as
T29a_KERNEL_CHECK.log. This is a parent-log audit, not a new kernel execution.

## Scope and repair

Only AdmissionAccounting.lean is new. T29b addresses the first two failed
clusters of the old T29, not the indexed trace cluster. It does not modify the
verified T29a, T28 or any earlier theorem. No `Step` or `Chain` is introduced.

1. `GateInput` has a fee, migration charge, old/new reserves, balance and
   paired rows. `gate` returns the ordinary T28 `Verdict`. It uses ordinary
   conditionals, without a dependent match on an equality proof. The four
   `gate_*_iff` theorems reflect every verdict independently of a Session.
2. `applyVerdict` takes a plain verdict and a proof that it equals the fixed
   gate on this exact session and offer. It cannot accept an arbitrary
   verdict from an unchecked caller. Unlike the failed T29, no inductive
   verdict family has a computed endpoint. The public `tryRelative` passes
   the same verdict to the application, and charges base+1 when not deferred.
3. `accepted_affordable` proves that the *installed* continuation's reserve
   is affordable, using the already verified `proposed_reserve` lemma of
   T29a. The `charge` helper takes an explicit debit and affordability proof.
   `addedEntries_cost` establishes the exact receipt/debit identity; then
   `apply_charge` uses this and unchanged prior receipts/history. The proof
   of `apply_funds` uses `gate_debit_le`, so Nat subtraction cannot silently
   saturate and fabricate a budget.
4. A distinct relative-admission journal preserves the exact indexed offer,
   predecessor continuation, balance before the attempt, check fee and
   verdict. Existing T28 history is unchanged, never mislabelled as passing
   T28's more restrictive absolute economic gate. The journal is an in-memory
   functional structure, not authenticated durable storage.

## Contract

With check fee H, migration K, old reserve Ro, new reserve Rn, balance B:

    if H + Ro > B: Deferred
    else if H + K + Rn > B: RejectLiquidity
    else if not relativeOK(H + K, rows): RejectGain
    else: Accepted

Deferred leaves the whole session unchanged. Rejection charges H and retains
the old continuation exactly. Acceptance charges H+K and installs the T29a
rebased continuation. The root task pair, old certificates, old search
receipts, base fees and historical records survive. `Live.liquid` is preserved
by construction, and completion is still the verified T28 root completion.
The raw numeric gate alone is insufficient: empty rows can pass vacuously;
the proof-indexed RelativeOffer excludes empty/uncovered evidence.

The source defines `objective = spent + remainingBill` only as a specification.
The gate does not evaluate prospective executions. `apply_accepted_gain`
states strict reduction of this objective for acceptance, including H and K.
`apply_nonaccepted_objective` states the exact increase by chargedFee for
nonacceptance (zero for deferred). `recordEvidence` records a positive externally
declared evidence charge if the fallback remains funded; it does NOT acquire
truth. Its current-continuation, journal, charge, conservation and objective
laws are included. Proof preparation, model construction and actual evidence
acquisition must be accounted for in a later operational integration; they
are not automatically free because they appear in propositions.

## Independent executable checks

`check_admission.py` checks all four verdicts on 45,000 numeric cases (37,500
with initially funded incumbent), and 17,621 concrete attempts on 320 task
pairs and 960 search prefixes. 1,342 accepted, 7,425 deferred, 4,434 rejected
for liquidity, 4,420 rejected for gain. All 17,621 completions match the
independent T23 morphism reference; 20,841 coverage comparisons are checked.
Accepted replacements include 6 with earlier emitted certificates and 800
with earlier search receipts. 17,617 externally charged evidence receipts
are carried into attempts. Three invalid applications (stale continuation,
forged verdict, empty evidence) are rejected by the reference assertions.
The model checks that the row scan is not evaluated on either unaffordable
branch. The closed T28/T29a witness costs 7 unchanged, 3 after successful
relative replacement, 8 after paid liquidity rejection, and 7 when deferred.
The 1,342 relative-only accepts use deliberately constructed correlated rows
with a shared nuisance shift, not measured new physical worlds. Prospective
bills are computed offline for the tests. Python asserts the verdict again
as a reference check; this is not an analysis of compiled Lean proof erasure.
See FINITE_ADMISSION.log. These tests are not Lean kernel execution or evidence
of wall-clock speedup.

## Kernel acceptance

Lean 4.36.0. **16 modules, 416 inherited + 35 new = 451 axiom reports.**
The strict auditors and existing fixtures are unchanged. Do not weaken any
statement merely to make the audit pass. Save the new log outside the package:

    set -o pipefail
    bash run_verify.sh 2>&1 | tee ../T29b-KERNEL_CHECK.log

**Recorded outcome.** `run_verify.sh` exits 0 on a fresh extraction of this
archive, with no repair needed to any module. Every module reports `Lean exit=0`
and passes both auditors, for 451 reports in total. `AdmissionAccounting.lean`
reports `35/35 axiom reports; Lean exit=0;
dependencies={'Quot.sound': 31, 'propext': 35}`. All ten auditor fixtures pass,
and the finite checks pass, including the new accounting model:
numeric reflection, exact charges, preserved reserves, receipts and root
completion.

The promotion condition stated above — all 451 reports, zero diagnostics,
allowed axioms, manifests and finite checks passing — is met.

The old failed T29 remains historical. The fixed closure plan is
T29c -> T30 -> T31 -> T32, not indefinite expansion. `KERNEL_CHECK.log` is
included in this archive and records the run; a recorded PASS is not a
substitute for kernel acceptance on the consumer's machine.
