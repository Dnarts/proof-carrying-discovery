# CRTT-T24.7-v0.1 — Endogenous Learning Discovery

Status: **VERIFIED on Lean 4.36.0.** All ten modules compile with exit 0 and
zero diagnostics; 190 inherited + 5 ResumeLaws + 27 BudgetedPruning +
13 ImpasseCompilation + 16 LearningDiscovery = 251 axiom reports are audited by
exact name and by fully-qualified name, with only `propext` and `Quot.sound`
permitted; no `sorryAx`, no `Classical.choice`, no warning, no error.
Toolchain `Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117)`.
See `KERNEL_CHECK.log`.
Parent: `CRTT-T24-v0.1.zip`. Seven of the eight inherited modules are
byte-identical; `ImpasseCompilation.lean` is the repaired T24 version (see below),
not the parent's. `ResumeLaws.lean` and `LearningDiscovery.lean` are new here and
were also repaired. All ten modules were compiled and audited here; the historical README and finite
log are preserved under PARENT_* names. BudgetedPruning and ImpasseCompilation now
pass, and ImpasseCompilation carries the constructive membership checker described
below rather than the parent's `decide`-based version.

## ResumeLaws.lean (independent extension of verified T22.9)

A positive-cost deterministic quote depends on state, not on balance. The
budget is an affordability gate; execute uses the balance as fuel. The
new `execute_topUp_prefix` and `execute_topUp_add` statements remove the need
for a globally decreasing progress measure from the exact composition law.
They include arbitrary paid prefixes and possible cycles. The proof first
shows that execution from an affordable successor yields the same saturated
account, using T22.9's stopped-prefix equality. `loop_no_decreasing_measure`
is a constructive separation between budgeted resumability and termination.
If a policy observes the injected balance, the theorem is not applicable.

## LearningDiscovery.lean (depends on both unverified T24 modules)

The active library contains typed read obstruction cores. A port job's
fixed-rule suffix runs first. At the no-rules stage, the *current* active
library is checked (even on already queued regions). A hit discharges the
region by certified containment; a miss enables a paid read-row probe. A
failed probe discharges the region and records the full obstruction as a
pending compilation. A separately paid compilation shrinks it to an
inclusion-minimal core and updates the active library. A successful probe
enables one base advance. The quote stage does not compute row compatibility,
shrink cores, or perform final certification. The library and history are
inside the deterministic state; its policy does not read the budget.

`insertCore_rejects` states the exact union of rejected regions under insertion
and subsumption, within the SAME task pair. It is not a proof of economic
dominance. Retain an already subsuming core, otherwise insert the new core
and remove supersets. Starting empty, the active list is intended to remain
an antichain; this is independently tested but a general Lean antichain
invariant is still open. History retains the raw obstruction and the typed
Extraction, rather than deleting the reason when a rule is superseded.
`quote_correct` and `execute_correct` preserve T23 membership coverage;
`execute_exhausted_iff` connects answer exhaustion to exact T22 membership.
`execute_trace` connects spend to the sum of actual charges. `execute_split`
uses the new generic law, preserving the entire learned account. `classify`
returns the full account even when a last compilation remains pending.

## Limits, economics, and follow-up

- The new theorem sources have not been checked by Lean. The independent
  finite model does not execute Lean. A successful proof of generic
  composition does not supply a bound for full exhaustion of the learning
  automaton. The new Python model has a conservative sufficient-budget bound;
  a corresponding Lean measure/funding theorem remains OPEN.
- Whole-library containment is charged as lookup+length*perCore+1 (a
  conservative symbolic scan bill); actual short-circuit cost is not claimed.
  Quote computes the list length before payment. Compilation is one coarse
  paid operation (including minimization, subsumption and history append);
  no CPU, RAM, serialization, durable persistence or wall-clock bound.
  Base splits and action enumeration retain the parent coarse semantics.
- The new mode compulsorily probes and learns. There is no certified optimal
  learning policy, adaptive selection of whether to compile, or automated
  cross-task transfer. Baselines are separate reference and read-only runners.
  The learning mode may be more expensive than both. This is an economic
  negative control, not a failure of semantic correctness.
- This revision records in-memory raw/reduced evidence and aggregate fee
  lists; receipts are not cryptographically authenticated replay transcripts.
  Active-library semantic equivalence is scoped to current task pair.
- Next: prove a finite potential for the adaptive state, formalize optional
  compilation/retention, separate answer completion from optional learning,
  and include all setup, lookup and lifetime costs when comparing strategies.
  Only then introduce a T19 meta-task for choosing learning policies. T25
  recursive closure and scientific novelty remain open.

## Verification

Expected audit counts: 190 verified upstream + 40 parent T24 candidates +
5 ResumeLaws + 16 LearningDiscovery = 251. The exact-name and axiom auditors
are unchanged. ResumeLaws is compiled before the unverified T24 modules so
its independent theorem gate remains observable if the parent fails.

    set -o pipefail
    bash run_verify.sh 2>&1 | tee ../T24.7-KERNEL.log

Do not overwrite immutable logs or manifest. Lean is absent here; the runner
must fail closed with exit 127. Read FINITE_LEARNING.log for the observed
finite tests, including matched read-pruning controls. No kernel PASS is
inferred from Python results.
