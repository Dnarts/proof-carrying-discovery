# CRTT-T27-v0.1 — Decision-Relative Evidence Acquisition

Status: **VERIFIED on Lean 4.36.0, including DecisionEvidence.lean.** All
thirteen modules compile with exit 0 and zero diagnostics; 316 inherited + 36
DecisionEvidence = 352 axiom reports are audited by exact name and by
fully-qualified name, with only `propext` and `Quot.sound` permitted; no
`sorryAx`, no `Classical.choice`, no warning, no error. Toolchain
`Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117)`.
See `KERNEL_CHECK.log`.
This package takes Gate 3 before Gate 2 from the parent T26_NEXT_GATES.md,
then combines them. Gate 4 (controller replacement) is deliberately deferred.
The research-phase labels do not assert that all earlier open gates are closed.

## Provenance

The parent is `CRTT-T26-v0.1.1-verified(1).zip`, whose digest is pinned in
PARENT_ARCHIVE_SHA256.txt. Both uploaded v0.1.1 ZIP variants had the same SHA-256.
All twelve upstream Lean modules were copied byte-for-byte. The parent manifest,
README, NEXT_GATES and kernel log are retained under T26_* names. All 316 parent
axiom reports were independently re-audited by the existing short-name and
fully-qualified-name auditors; this is replay of the supplied log, not a new
Lean execution. The new manifest covers every package file except itself,
including the previously omitted historical T247/T25 manifests. Original
historical manifests refer to original package filenames and are archival,
not manifests for this new directory.

## Gate 3 — decision uncertainty versus value uncertainty

`Model H C` declares a nonempty finite controller catalogue, candidate aggregate
bills per cost hypothesis, and a reference with a certified lower-bound property
on admitted controllers. A hypothesis `h` is a whole possible cost model, not
an underlying execution world. The reference may be a lower bound in a general
Model. It is an exact optimum in `catalogueModel` (over the listed controllers)
or `exactFamilyModel` (over all legal T19 trees of a fixed underlying interface,
with supplied exact bill and reference identities). A candidate list that omits
all minimax-robust controllers need not attain the unrestricted robust optimum.

`regret D c h = bill c h - reference h` (Nat); `robustRegret` takes the maximum
over the declared belief. `residual` minimizes this over the declared nonempty
controller list. `robust_iff`, `residual_iff`, `catalogue_robust_iff` characterize
exact sufficient knowledge relative to the stated reference. The latter is
necessary and sufficient for pairwise epsilon dominance in every compatible
hypothesis when the reference is the catalogue optimum. `robust_subset` and
`residual_subset` prove refinement monotonicity under set inclusion.

`intervalOK` and `intervalCandidates` are executable sufficient checks using
only the certified bill interval endpoints. Self-comparison is skipped.
`intervalOK_sound` and `intervalCandidate_sound` certify these checks. A failure
is not proof of nonoptimality. `shared_endpoint_regret` bridges to T26: the
common upper optimizer has regret at most V_U-V_L for each compatible table.
If that optimizer is admitted in the catalogue, the optimum robust residual
cannot exceed this gap. Exact correlated hypotheses can eliminate unnecessary
value uncertainty. `assess` returns a proof-carrying decision when its residual
is within epsilon. Empty belief is vacuously sufficient and is NOT a license
to deploy: the true hypothesis must be a member.

## Gate 2 — two distinct acquisition objectives

The T19 adapter uses `World = H`, `Port = E`, `Action = C`, with deterministic
binary responses and fixed nonnegative prices. Terminal loss is regret against
the reference appropriate to the whole hypothesis. `acquisitionTree`,
`acquisition_optimal` and `acquisition_bellman` reduce the finite adaptive
problem to T19, with each query usable at most once per path. An empty response
branch has zero value. The Bellman identity is for nonempty belief. The actual
hidden hypothesis is not supplied as a distinguished argument of the solver.
`refine_truth` preserves truth membership when the response is correct.

The two objectives are intentionally NOT equated:

1. `acquisitionTree`: minimize max_h (paid query fees + terminal regret).
2. `hardAssess`: decide feasibility of terminal regret <= eps on every
   hypothesis, with a separate hard query budget. If feasible, the capped
   optimizer minimizes worst query expenditure among epsilon-valid legal
   strategies (`hard_minimal_observation`). This result reuses T19's penalty
   construction; it does not assume that a small weighted sum is a hard pass.

`walk` from T25 executes a selected tree through a supplied sense interface.
`walk_member`, `walk_terminal`, `walk_paid`, `hard_execution` connect selection,
query fees and regret to the certified tree. It is a pure execution model,
not an implementation of an external metered evidence service or a budgeted
cursor with receipts. `total_bill_identity` separates the benchmark, query
price, regret and an explicitly supplied setup charge. `optimizer_bill_bound`
provides a per-hypothesis actual bill bound. Minimizing regret+query cost is
not generally minimizing absolute worst expenditure, because the reference
may vary between hypotheses. The closed witnesses and Python tests show this.

## Costs, scope and remaining obligations

The hypothesis catalogue, exact cost/reference identities or certified
intervals, query semantics, and their prices are externally supplied. This
package is NOT a proof that constructing or certifying them is cheap or that
an arbitrary unknown true table belongs to the catalogue. Construction,
benchmark computation, querying, synthesis, verification, storage and loading
must be charged in a real deployment. A fixed setup charge is explicit; it
must represent those costs honestly and is not optimized by this solver.
No claim of autonomous online hypothesis-generation or a free cost oracle.
The hard evidence budget constrains query fees ONLY: it is not liquidity for
preparing the model or deploying the selected underlying controller. Those
reservations and continuation/root-contract preservation are Gate 4. The
exactFamilyModel fixes the underlying interface, action set, observation
ports, horizon and world list across hypotheses and changes only terminal loss.
There is no theorem over arbitrary algorithms or stochastic/nonstationary
observations. Correctness of actual sensor answers and truth membership are
external obligations; a rejected or inconsistent observation is not evidence
of a safe controller replacement.

## Independent finite check

See FINITE_DECISION.log. It enumerates 36,864 acquisition models and compares
2,727,936 legal trees, verifies 5,455,872 realized modeled bill identities,
184,320 hard-budget/epsilon feasibility checks and 168,768 successful hard
cases, 2,048 exact pairwise tests, 1,024 belief-subset tests, 29,760 sufficient
interval tests, and 10,000 compatible completions in 1,296 shared-endpoint
catalogues. The reference enumerates legal trees separately from the Bellman
implementation. It checks common-optimum correlated hypotheses, a paid bit,
XOR, disagreement of regret and bill objectives, excluded truth and empty
belief. This is a finite Python reference model, not execution of Lean or a
proof of physical runtime. No claim of measured wall-clock savings.

## Kernel verification

Lean 4.36.0 is required. Expected: 316 upstream + 36 new axiom reports = 352
reports across 13 modules. Both audit scripts and their fixtures are copied
unchanged. No `sorry` or `native_decide` is introduced. Compilation of the new
module has NOT been performed in the preparation environment: no `lean`
executable. `run_verify.sh` retains failure-closed checks and audits even on
compiler failure. Only `propext` and `Quot.sound` are allowed. Use a log outside
the package to preserve immutable manifests:

    set -o pipefail
    bash run_verify.sh 2>&1 | tee ../T27-KERNEL_CHECK.log

**Recorded outcome.** `run_verify.sh` exits 0 on a fresh extraction of this
archive. Every module reports `Lean exit=0` and passes both auditors, for 352
reports in total. `DecisionEvidence.lean` reports `36/36 axiom reports;
Lean exit=0; dependencies={'Quot.sound': 25, 'propext': 34}`. All ten auditor
fixtures pass, and the finite checks pass, including the new decision-relative
model in `FINITE_DECISION.log`.

One defect had to be repaired, and it was diagnostic-only: `DecisionEvidence.lean`
used the Lean 3-era names `if_neg` and `if_pos`, which Lean 4.36 reports as
deprecated (`ite_eq_right` and `ite_eq_left`). The proofs themselves were already
accepted; the strict runner rejects any warning. Renaming leaves the axiom
dependencies unchanged.

`KERNEL_CHECK.log` is included and records the run. A recorded PASS is not a
substitute for kernel acceptance on the consumer's machine: rerun the script and
read the `#print axioms` output yourself.
