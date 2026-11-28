# CRTT-T26-v0.1 — Paid Meta-Evidence Acquisition (T25.8–T25.12)

Status: **VERIFIED on Lean 4.36.0, including the new module.** All twelve
modules compile with exit 0 and zero diagnostics; 281 inherited + 35
MetaEvidenceAcquisition = 316 axiom reports are audited by exact name and by
fully-qualified name, with only `propext` and `Quot.sound` permitted; no
`sorryAx`, no `Classical.choice`, no warning, no error. Toolchain
`Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117)`.
See `KERNEL_CHECK.log`.
This package advances T25's finite meta-investigation; general controller replacement (T26 proper) is not yet established. The eleven imported Lean files are byte-identical to `CRTT-T25-v0.1.1-verified (1).zip`. Its original manifest, README and kernel log are stored under `T25_*` names. Both parent log auditors were replayed successfully for all 281 reports, and all twelve modules were then compiled here; see the recorded outcome below.

## Contract

For a finite T19 `Problem` with fixed actions, worlds, binary observations, prices and depth, each cell of a partial table is a `Bounds actual` with proofs `lower <= actual <= upper`. `Table C` is indexed by the exact mathematical cost function C. `refineCell` intersects evidence: it may only raise a lower bound or lower an upper bound. This excludes silently treating missing information as a zero exact bill. Initial lower bounds may be zero when certified by nonnegativity, but upper bounds must be justified.

Let VL and VU denote the optimized minimax values of the two endpoint models, and tU the upper model's optimizer. The candidate proofs establish:

* `lower_le_true`, `true_le_upper`: VL <= Vtrue <= VU.
* `upperTree_legal`, `upperTree_bill`, `certified_gap`: tU is legal, costs at most VU in the actual problem, and its worst bill is at most the bill of **any** legal competing tree plus VU - VL.
* `gap_monotone`: refinements cannot increase this sufficient gap.
* `pointTable_gap_zero`: a point table has zero gap.
* `assess`, `NearOptimal`, `nearOptimal_guarantee`, `assess_complete`: if VU <= VL + epsilon, return a proof-carrying strategy; otherwise return none. The gap is a sufficient certificate, not a necessary test of robust optimality. It is not pointwise regret relative to a world-aware oracle.

An optimum for a single declared action space does not imply optimum over arbitrary algorithms. The proof also does not establish that computing both endpoint optimizers is cheap.

## Operational contract

A `Request` has a key, a strictly positive declared tariff and a deferred evidence-producing thunk. `Operation` is either a request or a paid assessment. `Session` contains the partial table, remaining schedule, immutable-by-transition receipts, and optional near-optimal certificate. `quote` does not evaluate an optimizer or evidence thunk; only the paid successor can. The first successful assessment stops the schedule. If the result is absent, the session has no certified epsilon-optimal strategy, even if the schedule is exhausted. Preserve the full account to resume.

The theorem candidates `quote_meter`, `execute_trace`, `execute_info`, `execute_gap_le`, `execute_split` connect charges and state to the already verified budget runner. `quote_potential` and `execute_funded_quiescent` bound remaining scheduled tariffs. A fully funded finite schedule guarantees quiescence, not that the provided observations suffice. Top-up composition requires the same deterministic, balance-independent schedule. `paid_improvement` compares the bill including a supplied overhead H to a specified reference bill; all setup, acquisition, controller and other charges needed for that comparison must be included. A small gap by itself does not prove that acquisition was economically rational.

## T25 adapter

`actualProblem` preserves T25's observation interface and uses `actualBill` rather than its predicted table. `initialBounds` uses the plan setup fee and the proven reservation bound (setup + learning allowance + completion reserve). `exactRequest` computes the exact modeled bill of a known **offline catalogue** pair and plan, charging its reservation plus a positive surcharge. This is a conservative prepaid tariff, with no refund; it is not a claim of equality to the actual executed plan bill. `exactRequest_charge_covers` is the candidate upper-charge theorem; `exactRequest_point` proves a point interval. `actualModel_runCost`, `accepted_actual_bill`, `accepted_complete` connect a certified tree to actual T25 execution and semantic completeness. Existing T25 funding proofs remain required. The planner chooses using only paid observation bits at execution; offline catalogue indices are not a port to the hidden world.

The exact-request implementation retains the resulting point interval and the charged receipt, not a serialized full lower-level execution trace or durable evidence hash. Proof-carrying tables are indexed by a mathematical function, not by cryptographic identity. Authenticating persisted task IDs, executable code and historical traces is a separate open engineering/formalization gate. The `Request` supplier, tariff schedule and assessment tariff are explicitly provided, not independently measured runtime bounds. The code has not been inspected as a compiled binary for thunk evaluation or proof erasure.

## Independent executable checks

`check_evidence.py` is a finite Python model, not Lean execution. It enumerates 10,368 interval models (two worlds, two actions, one binary port with both prices), 80,000 compatible cost completions, 480,000 legal-tree comparisons, 320,000 refinements, 10,368 split-budget cases and 162 fully funded schedules ending in a certificate. Includes empty worlds, insufficient evidence after all funded jobs, a non-necessary gap witness, minimax-vs-oracle-regret witness and unpaid-thunk test.

The original T25 two-task witness is run using its real finite-model plans, not fabricated labels. A fixed ex-post chosen schedule queries six out of eight cells and certifies the same minimax value 22, omitting two cells. Under uniform reserve caps (350,390,390,390), a positive per-cell surcharge of 1 and assessment fee 3, the partial prepaid bill is 2,309 vs 3,051 for all eight cells and one assessment. The underlying actually modeled plan bills sum to 322 vs 465; these are different from prepaid charges. The schedule was chosen with prior knowledge of this witness. This is an existence example, not learned policy generalization or a general optimal acquisition theorem. Both approaches use the same declared price model; the old 465 figure in T25 did not include this new prepaid reservation and assessment model. At a controller fee of 3, the execution worst bill is 25, compared with 53 for the best known fixed plan; under the partial prepaid accounting, the 2,309 overhead takes 83 repetitions to amortize against that benchmark (assuming benchmark cost supplied, fixed family and no additional fees). No claim of practical speedup is made.

## Verify

Requires Lean 4.36.0. Eleven upstream modules = 281 reports, new module = 35, total = **316**. Both strict audit scripts and their ten tests are unchanged. The runner compiles in a temporary directory, audits both even on failure, and then runs all five finite model programs. Do not overwrite a manifest-covered historical log. Save new logs outside the package:

```bash
set -o pipefail
bash run_verify.sh 2>&1 | tee ../T26-KERNEL-RERUN.log
```

`SHA256SUMS.txt` covers all payload files except itself. `UPSTREAM_SHA256.txt` pins all eleven imported Lean files.

**Recorded outcome.** `run_verify.sh` exits 0 on a fresh extraction of this
archive. Every module reports `Lean exit=0` and passes both auditors, for 316
reports in total. `MetaEvidenceAcquisition.lean` reports
`35/35 axiom reports; Lean exit=0; dependencies={'Quot.sound': 22, 'propext': 30}`.
All ten auditor fixtures pass, and the finite checks pass, including the new
interval-minimax model: monotone refinement, paid schedule, quiescence, split,
insufficient evidence and oracle-regret controls.

Defects repaired to reach this status:

- `quote` built its `Session` update with `{ s with ... }`. For a structure whose
  parameters come from `variable` rather than from the declaration itself, Lean
  4.36 fails to elaborate that notation here (`unexpected identifier; expected '}'`),
  and the parse failure also broke three downstream `rw` steps and left two goals
  open. Writing the fields out as an explicit structure literal fixes all of it.
- In `quote_potential`, `rw [← hq]` substituted the quoted step but left
  `q.next ()` symbolic, so the structure literal never reduced. Using
  `simp only [.., Option.some.injEq] at hq` followed by `subst hq` lets it reduce.
- Eight `sorryAx` dependencies descended from the two defects above; none remain.
- Five theorems do not use the `DecidableEq` section variables. Lean 4.36 rejects a
  local `omit ... in` in this position, so `linter.unusedSectionVars` is disabled
  for the file, with the reason recorded at the `set_option`.

`KERNEL_CHECK.log` is included and records the run. A recorded PASS is not a
substitute for kernel acceptance on the consumer's machine: rerun the script and
read the `#print axioms` output yourself.

## Open gates

See `NEXT_GATES.md`. In particular, the optimal selection of evidence requests, tighter decision-specific certificates, amortized acquisition under unknown future tasks, durable evidence provenance, and the certified controller replacement itself remain open. Unlimited compulsory learning termination and active-core antichain obligations from T24.7 are not solved by this package.
