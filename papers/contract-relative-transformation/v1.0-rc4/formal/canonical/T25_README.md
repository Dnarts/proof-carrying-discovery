# CRTT-T25-v0.1 — Certified Meta-Investigation

**Status: VERIFIED on Lean 4.36.0, including the new module.** All eleven
modules compile with exit 0 and zero diagnostics; 251 inherited + 30
MetaInvestigation = 281 axiom reports are audited by exact name and by
fully-qualified name, with only `propext` and `Quot.sound` permitted; no
`sorryAx`, no `Classical.choice`, no warning, no error. Toolchain
`Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117)`.
See `KERNEL_CHECK.log`.
Parent: `CRTT-T24.7-v0.1.1-verified.zip`. All ten inherited Lean files are
byte-identical. Parent README, full manifest, upstream manifest and actual
supplied Lean log are preserved under `T247_*` names. The 251 parent axiom
reports were independently re-audited, including full qualified names.

## T25 scope and ADT

`RuleSchema`: a finite syntax for the already verified read/price/injective/depth
rule families. `instantiate` produces `CertifiedRule S T` at arbitrary carrier
sizes, not a learned task-specific no-good relabeled by analogy. This is
parametric portability; it does not synthesize new schemas or transport an
arbitrary learned core without a certificate.

`Plan`: ordered rule schemas, optional bounded learning allowance, static
completion reserve, declared setup/handoff/disposal charge.

`runPlan`: execute the unchanged T24.7 controller for the learning allowance,
then finish the **same frontier** using the unchanged funded T23 runner. Reuse
unspent allowance, previously emitted certificates and unfinished jobs. Stop
optional learning at the handoff (even a pending compilation may remain).
Return the full learning-prefix account as evidence, alongside the completed
frontier. The active library is not used by the static fallback; it and raw/
reduced evidence remain in the returned account. Persistence across processes
and future-task reuse are not implemented. `perform` is the final-account
projection, not a second execution.

`Funded`: supplied proof that the fallback has enough reserve. The new
`learning_quote_potential`, `learning_potential_bound`, `funded_of_initial`
show (as proof-source obligations) that the base frontier potential never
increases during learning, so the initial static reserve suffices regardless
of the learning prefix. No general termination theorem for unlimited learning
is needed. Potential is only used in proofs, not computed by the actual runner.
The reserve must be supplied and its funding justified before execution.

`MetaTask`: finite declared lists of possible task pairs, observation ports,
and plan IDs, including a default. Pairs share carrier sizes in this first
implementation. Each action has a complete funded plan for each possible pair.
The observer supplies a deterministic binary result and a declared port fee.
`problem` is the reduction to the verified T19 `Problem`, and `optimizer`
uses T19 `solve`. Only the chosen plan is run by `runMeta`, whose result
includes the decision, both phase accounts and total charged bill.

## Main mathematical obligations (all new declarations need kernel check)

| Gate | Main declarations |
|---|---|
| T25.1 Portable rule syntax | schema_sound |
| T25.2 Optional learning and completion | finishInput_correct, learning_quote_potential, learning_potential_bound, funded_of_initial, perform_exhausted, perform_complete, perform_static |
| T25.3 Accounting, continuity and evidence | runPlan_prefix, learning_accounting, perform_accounting, perform_trace, actualBill_le_reservation, runMeta_history |
| T25.4 Explicit meta semantics | walk_cost, selectedRun_complete, runMeta_bill, runMeta_complete |
| T25.5 Valid cost bounds | executionCost_le, actualWorst_le, optimizer_bound_optimal, meta_budget_iff |
| T25.6 Exact-cost minimax | executionCost_eq, actualWorst_eq, optimizer_legal, optimizer_actual_optimal |
| T25.7 Cost of metareasoning | default_upper, acquisition_gain_iff |

The cost table is an explicitly supplied function of plan ID and meta-world.
`tableBound` requires a proven upper bound on the actual abstract completed
plan bill. `ExactTable` is a strictly stronger condition. T19 optimizes the
upper-bound objective in the first case, actual modeled worst-case costs in
the second. Upper-bound optimality does not imply actual-cost optimality.
The finite table is known at synthesis, while its actual world is unknown at
selection; the tree branches only on declared observations. The mathematical
interface does not police IO or information flow in a user-supplied sensor or
table function. The Python stand materializes its tables offline and uses only
specified features as ports. Runtime sensing is modeled, not an external
adversarially verified IO protocol.

`controllerFee` is a **declared** aggregate charge, not an automatically
certified physical cost. Table acquisition/verification, planning, lookup,
retention, and disposal must be included explicitly either in this charge,
plan setup charges or separately amortized one-time acquisition costs (without
double counting). The code does not silently learn cost estimates, assume
unseen tasks follow a distribution, or build an uncharged exact table by
running every plan. The theorem is conditional on the supplied bound/exactness
proof. Compilation of arbitrary new schemas, adaptive learning schedules,
learned core reuse across task pairs, open-world calibration and recursive
controller transfer remain OPEN.

`meta_budget_iff` concerns worst-case **modeled expenditure**, not liquidity.
Each chosen plan needs upfront access to its learning allowance and sufficient
completion reserve, plus its setup charge and observations/controller fees.
A table using `setupFee + learningBudget + reserve` is a valid conservative
cost bound via `actualBill_le_reservation`; a table of exact spent amounts
alone need not certify availability of the reserve. There is no wall-clock,
RAM, or IO cost guarantee. Parent abstract coarse tariffs are unchanged.

## Independent finite reference check

`check_meta.py` reuses the parent independent transition models, compares
actual completed hybrid plans to literal h,p,a enumeration, checks trace
conservation and the initial static reserve, and exhaustively enumerates all
legal depth-two meta trees with two observation ports and six plan IDs.
It includes positive and empty-carrier controls, exact and slack cost tables,
selected plan re-execution, and an overhead counterexample.

- 2,330 completed plan checks (plus 768 selected reruns), 256 meta cases,
  904,704 tree comparisons, 452,352 exact-table optimality comparisons.
- 118 handoffs with pending compilation and 60 prefixes already containing
  certificates (counts across initial evaluations and selected reruns).
- 5,500 finite amortization arithmetic cases.
- Concrete two-meta-world example: plan bills `((80,21,87,63),
  (80,53,18,63))`, a single paid sensor reads the first source read bit.
  The plan order is no rules, read, price, injectivity. Best fixed worst bill
  is 53; depth-one meta tree worst bill is 22, or 25 with controller fee 3.
  Acquiring all eight table cells in this model costs 465; strict savings
  against the fixed plan's worst-case guarantee begin at 17 uses under the
  stated fixed charges (not an average-case or future-task guarantee).
  A fee of 40 negates the gain. A loose valid table can choose a worse actual
  plan. This is a constructed witness, not an independent statistical test.

Read `FINITE_META.log`. The reference stand does NOT execute Lean, and cannot
establish the new theorem proofs. The parent finite models were rerun as well.

## Verification

Expected: 251 inherited + 30 new audit reports = 281 reports across 11 modules.
The exact-name and full-qualified-name auditors from T24.7 are unchanged;
new module is appended to the strict runner. Both audits run before a module
failure stops the build. The immutable journal of the parent is never
presented as the new module's compiler output.

    set -o pipefail
    bash run_verify.sh 2>&1 | tee ../T25-KERNEL.log

**Recorded outcome.** `run_verify.sh` exits 0 on a fresh extraction of this
archive. Per-module audits: twenty-two, twenty-two, fifty-one, thirty-seven,
thirty-four, twenty-four, five, twenty-seven, thirteen, sixteen and thirty
reports, all `Lean exit=0`, all passing both the count/axiom auditor and the
fully-qualified-name auditor. `MetaInvestigation.lean` reports
`30/30 axiom reports; Lean exit=0; dependencies={'Quot.sound': 29, 'propext': 30}`.
All ten auditor fixtures pass. The finite checks pass, including the new meta
model: exact/bounded tables, selected reruns, frontier handoff, no-learning
control, paid trace, fixed uniform reserves, finite minimax, and the
costly-controller and loose-bound counterexamples.

One defect had to be repaired to reach this status:

- `acquisition_gain_iff` proved its biconditional with a bare `omega`. On `↔`
  over truncated `Nat` multiplication, `omega` falls back on a classical
  decision and imports `Classical.choice`; splitting with `constructor` and
  closing each direction separately is constructive.

`KERNEL_CHECK.log` is included in this archive and records the run. A recorded
PASS is not a substitute for kernel acceptance on the consumer's machine:
rerun the script and read the `#print axioms` output yourself.
