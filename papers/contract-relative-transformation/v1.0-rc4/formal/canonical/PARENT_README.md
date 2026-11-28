# CRTT-T24-v0.1 — budgeted pruning and impasse compilation

**Status: SOURCE_CANDIDATE. New Lean modules are NOT kernel verified.**

Parent: `CRTT-T23-v0.1.2-verified.zip`. The six upstream Lean files are
byte-identical. `UPSTREAM_KERNEL.log` is the parent's original successful
Lean 4.36.0 journal. Its 190 reports were re-audited against the actual source
with both the original strict parser and the new fully-qualified-name check.
No claim of new Lean execution is made.

## BudgetedPruning.lean (T23.10–T23.11)

Uses T22.9 Account, QuotedStep, run, execute, topUp, and generic invariance and
saturation results. A frontier contains unfinished jobs, emitted canonical
certificates, and reverse-chronological receipts. Each individual rule is
charged separately; a failing rule discards its job before subsequent rules
are evaluated. A paid split produces the next layer of children. A paid
prepare decodes the full assignment, checks the original T22 port guards,
and generates the action-map list only on acceptance. Each action candidate
is certified separately. Retiring an empty action list is also charged.

`Correct` proves two directions separately: emitted certificates belong to
T22, and every canonical T22 certificate is emitted or covered by a job.
The source attempts the following proofs:

- `quote_correct`, `execute_correct`: preservation of the correctness invariant.
- `execute_trace`: exact difference of spend equals difference of summed receipts.
- `quote_potential`: remaining liability plus paid fee never exceeds prior liability.
- `execute_funded_exhausts`, `execute_full`, `start_full`: a sufficient budget
  yields exhaustion and exact canonical certificate membership.
- `execute_split`: exact account equality for divided top-ups with fixed policy
  and prices; preserves receipts and remaining balance, not just output sets.
- `execute_certificate_prefix`: previously emitted certificates survive.
- `verdict`, `classify`: found, globally impossible on certified exhaustion,
  or inconclusive, retaining the complete account on every return.

The potential is a proof-only upper bound. For a port job with d remaining
ports and an untested rule suffix R, its liability is cost(R)+P(d), where
P(0)=prepare_fee+(number_of_action_maps+1)*action_fee and
P(d+1)=split_fee+number_of_target_ports*(cost(policy)+P(d)). A quote must
satisfy potential(next)+fee <= potential(current). The paid runner uses the
remaining balance as fuel, not the potential or the exhaustive reference.

## ImpasseCompilation.lean (T24.1–T24.6)

`shrink` works over any monotone Boolean obstruction on a finite list of
constraints, with decidable equality for the irreducibility statement.
It tests each original occurrence once and keeps a constraint only if
removing it would lose the obstruction. `shrink_spec` supplies preservation,
subset inclusion, and irreducibility when the kept list starts empty.
Duplicate occurrences and empty source/target carriers are permitted.

`ObstructionCore` contains a target world, partial port constraints and an
empty-row proof. `extract` constructs an `Extraction` from a known bad row;
`toCore` retains the proof. `compileCore` uses subset containment alone to
exclude any later region containing the core, and `compiled_search_complete`
connects this rule to T23's exact membership theorem. `rowBad_cover_iff`
states the set-cover equivalence. This does NOT solve minimum-cardinality
set cover. `CoreTransport` permits reuse across distinct indexed task pairs
with a supplied reflection certificate, not matching labels or hashes.
`transportCore` preserves obstruction but not necessarily irreducibility.

## Explicit limits / decisions

- All fees are symbolic Nat charges, not CPU or memory measurements. Base
  prices use +1; each tested rule costs rule.cost+1. Paid split/prepare can
  allocate a whole one-level child list or all action maps for one valid
  port assignment. These are deliberately coarse metered operations; no
  claim of fully incremental action generation or physical resource bound.
- Receipts contain kind and fee, not full input/output content hashes or
  durable replay authentication. The trace theorem concerns this executable
  abstract transition system. No independent disk persistence implementation.
- Coverage proves no silent loss and exact membership at exhaustion, not a
  disjoint partition, ordering guarantee or uniqueness of emitted certificates
  for arbitrary externally constructed frontier states.
- The core extractor is constructive, but its work is not yet integrated into
  the paid frontier. Core libraries can be constructed outside and supplied
  as fixed policies. Online learning/retention, compilation costs and transfer
  discovery costs are not yet accounted for (T24.7 OPEN).
- The reflection certificate is supplied, not synthesized. Minimum-cardinality
  core optimization, action-constraint cores, Hall filters, computed lower
  bounds, and recursive metacontroller T25 remain open.
- Exact split-budget composition assumes a fixed rule list and fees. It does
  not promise unchanged results/state under a changed scheduling policy.

## Independent finite checks

`check_impasse.py` uses independent Python implementations, comparing every
completed search with literal h,p,a enumeration inherited from T23. It checks
finite progress, exact membership, symbolic liability, actual charged receipts,
core irreducibility, set-cover nonminimality, repeated constraints, fixed-policy
resume and positive transfer examples. It is not a Lean runtime test or proof.

## Verification

Expected 230 axiom reports: 190 upstream + 27 BudgetedPruning + 13
ImpasseCompilation. Both new modules require Lean 4.36.0 kernel checking.
The runner preserves the existing audit parser and fixtures, adds exact
qualified-name checking, audits reports even when compilation fails, and
stops before downstream compilation on any failed check. Run:

    set -o pipefail
    bash run_verify.sh 2>&1 | tee ../T24-KERNEL_CHECK.log

Keep the journal outside the immutable package. The author environment has no
Lean executable. `run_verify.sh` must fail closed with exit 127 here.
