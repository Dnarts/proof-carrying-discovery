# CRTT-T30-v0.1 — Paid, Replaceable Finite Proposal Policy

**Status: VERIFIED on Lean 4.36.0.** All eighteen modules compile with exit 0
and zero diagnostics; 484 inherited + 19 MetaPolicy = 503 axiom reports are
audited by exact name and by fully-qualified name, with only `propext` and
`Quot.sound` permitted; no `sorryAx`, no `Classical.choice`, no warning, no
error. Toolchain `Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117)`.
See `KERNEL_CHECK.log`.
The parent is `CRTT-T29c-v0.1.1-verified (1).zip`, pinned in
PARENT_ARCHIVE_SHA256.txt. Its 91 declared payload hashes passed; its seven
unlisted historical manifests matched the original archives. All 17 Lean
sources are unchanged, including RecursiveTrace.lean (identical to its
submitted candidate). The supplied parent journal was replayed with both
strict text auditors: 484/484 reports. The independent check_trace.py model
was rerun, with byte-identical output. No local Lean compilation was performed.
The new manifest includes every payload except itself, including historical
manifests. Historical files are archival, not assertions about current paths.

## Scope — one finite acquisition episode, one fixed verifier

T30 implements a finite, executable proposal policy as an actual
T19 `Investigation Unit Bool`. A leaf `false` keeps the existing controller;
`true` invokes paid offer preparation and then the existing T29b admission
checker. An observation node purchases one binary response, then executes
only the selected branch. The root tasks and continuation are fixed during
acquisition and policy synthesis. Rule and base prices retain the previously
established abstract tariff contract. The provider is fixed for the comparison;
a meta-policy cannot change the verifier, observation semantics or tariff
by installing a different tree.

`Frame old` carries a live Session and a proof of its precise old-continuation
identity. `Provider old` declares the observation thunk and the offer factory
thunk, as well as positive query, preparation and root-check fees (base+1).
`pay` uses the actual T29b charge transition, retaining the incumbent reserve.
`offerAt` transports a prepared RelativeOffer through the exact equality in
Frame; it does not guess identity by matching labels or hashes.

`interpret` is structurally recursive on the finite T19 tree. It does not
execute a prospective completion or optimize a tree when quoting an operation.
In the funded branch it records the query or preparation fee and invokes the
corresponding thunk. Preparation returns actual proof-bearing offer data;
this is more than a bare acquisition receipt. T29b alone checks and installs
the proposed root controller. `Outcome` returns the real observed Boolean,
prepared offer (also when its later admission is deferred), attempt verdict,
final Session and proofs of preservation and conservation. An unfunded query
or preparation returns blocked. A deferred root attempt ends the episode.
No nonterminal step can cause an unbounded walk, since the tree is finite.
An arbitrary finite tree is executable, even if it repeats its one port;
only the synthesized witness is claimed T19-legal with a one-query horizon.
These are pure operational definitions, not an audit of compiled thunk
forcing, external IO timing or physical execution charges.

## Mutable meta-policy and admission

`Machine old` holds the current Frame, an active proposal tree and append-only
upgrade history (newest first). A `Proposal` is indexed by the exact Machine,
fixed Provider, setup tariff and paid frame. It has a candidate tree, an old
lower bound on the incumbent's all-in completion bill at the actual before
frame, and a new upper bound on the candidate's all-in completion bill at the
actual POST-payment frame. Both bounds carry proofs. `policyBill` is the
specification of the final completion total and is never invoked by upgrade.
It includes sunk charges, the installed root controller's remaining bill,
and all charges actually recorded by this policy. In particular the new
bound already includes the policy synthesis/admission tariff, not just the
policy's conditional downstream cost.

`upgrade` checks that prepayment leaves the incumbent root reserve intact.
If not, it leaves Machine unchanged and does not invoke the synthesis thunk.
If affordable, it pays the positive declared synthesis/admission tariff,
invokes the proof-bearing proposal thunk, and compares the two certified
numbers. Strict separation `newUpper < oldLower` admits the new tree.
Otherwise it retains the incumbent tree, with the attempted fee still paid.
Upgrade history stores fee, status, old/candidate trees, before balance and
numeric comparison bounds; the dependent result retains the accepted-gain
proof. Numeric comparison does not run either prospective policy. A rejected
upgrade need not leave the economic objective unchanged; the old root can
still finish. `upgrade_gain` proves a strict improvement in the declared
all-in bill, for the precise before and after frames, conditional on the
supplied bound witnesses. It is not an optimal policy search theorem.

Important boundary: the upgrade function receives a fixed Provider as an
argument. T31 must freeze that Provider for an entire admitted meta-history.
This is an episode-local mutable policy, not a rewrite of arbitrary code or
of the independent verifier. The proof source is not an untrusted-proof
parser. The finite provider and evidence catalogue are pre-certified, and
preparing such a catalogue for another problem is an external obligation.
The declared synthesis/admission fee models its bundled runtime operation;
it does not measure or bound Lean proof generation, offline catalogue
construction, CPU cycles, storage or memory. No claim of a cheap universal
proof generator or independent proof-checking service is made.

## Nontrivial closed witness

Reuse T28's finite depth-obstruction source/target and its already exhausted
counterpart as a two-scenario catalogue. The actual observation is whether
the current (exactly fixed) frontier has pending jobs. The direct action
incremental bills, separately matched to actual execution by terminal_bills:

| Scenario | Keep | Prepare and attempt |
| --- | ---: | ---: |
| Exhausted | 0 | 2 |
| Pending | 7 | 4 |

The exhausted scenario has already paid 7; the table is incremental, not
an assertion that its lifetime bill is zero. Unit observation price = 1.
The T27 `catalogueModel` and `acquisitionTree` compute a legal policy from
the finite declared belief, not from a distinguished true scenario. Its
minimax query-fee-plus-regret value is 1; the pure runtime observation then
selects keep or prepare-and-attempt. The selected tree's pending all-in bill
is 5 (before upgrade setup); its exhausted incremental bill is 1. It beats
both constant actions on the stated regret objective (their worst regret is
3 and 2 respectively). It does NOT beat direct attempt on every objective
or every scenario. Pending direct attempt alone costs 4, and the best
absolute worst incremental bill is not the regret optimum. The meta-upgrade
compares against the actually installed KEEP policy at the pending frame.
`makeUpgrade` runs the T27 solver inside the paid proposal thunk, with exact
closed proof-side bounds 7 and 6. The accepted result installs that tree.
Final all-in bill is 6: synthesis/admission 1, actual query 1, preparation 1,
root validation 1, migration 1, completion 1. Original completion is 7.
The setup and other amounts are explicit model tariffs, not wall-clock
measurements. `blocked_is_free` protects the fallback at exact reserve.
The independent negative control rejects a nonimproving paid meta-upgrade,
increasing the unchanged completion bill from 7 to 8.

The positive witness is an existence demonstration on a tiny, explicitly
specified family. Its proof-bearing offers and exact action-bill table are
pre-certified closed fixtures, not autonomously learned economic evidence.
A prepared offer is actually constructed or returned by its paid factory;
obtaining proofs for arbitrary new frontiers is outside this witness.

## Independent finite checks

`check_policy.py` uses the existing T23/T29b/T29c Python reference runner,
with an independent Bellman implementation from check_decision.py. It
checks all six one-port depth-one policy trees over 48 task pairs, three
prefixes, five surplus levels and two values for each of two acquisition
fees: 17,280 executed policies, 474 accepted root replacements, 5,760
blocked, 864 deferred, 6,912 kept, 2,796 rejectGain and 474 rejectLiquidity.
Every completion matches the independent literal morphism reference;
all observed/prepared events match invocation counts and all fees are
reconciled. It checks the four exact terminal bills, closed synthesis and
installation, positive and negative upgrades, and three poison thunks which
must not be invoked on unfunded branches. This is not execution of Lean.

## Verification and fixed closure path

Expected: 18 modules, 484 inherited + 19 new = 503 axiom reports. The
strict auditors and their fixtures are unchanged. Lean is unavailable in the
preparation environment. New proofs are candidates until actual compiler
exit 0, zero diagnostics, and all reports pass both auditors. Use Lean
4.36.0 and save the log outside the immutable input directory:

    set -o pipefail
    bash run_verify.sh 2>&1 | tee ../T30-KERNEL_CHECK.log

**Recorded outcome.** `run_verify.sh` exits 0 on a fresh extraction of this
archive. Every module reports `Lean exit=0` and passes both auditors, for 503
reports in total. `MetaPolicy.lean` reports `19/19 axiom reports; Lean exit=0;
dependencies={'Quot.sound': 19, 'propext': 19}`. All ten auditor fixtures pass,
and the finite checks pass, including the new policy model: the actual finite
T23 runner, paid policy thunks, protected fallback, synthesis/installation and
complete reference membership.

One defect had to be repaired, and it carried all three `sorryAx` dependencies
in `Witnesses`:

- `makeUpgrade` proved `newSound` by a chain of local `have`s. Because the
  affordability proof `hf` is an *argument* of `pay`, it occurs inside the goal
  type rather than in the local context, and `decide` rejects such a goal
  ("Expected type must not contain free variables"). Restating the goal with
  `show` does not help for the same reason. `decide +revert`, which generalises
  the offending variable first, closes it; `changed_policy`, `changed_bill` and
  `actual_saving` then report `propext, Quot.sound` only.

T31 must establish compositional closure under repeated actual transitions,
including policy upgrades, retaining the provider and exact observations and
prepared evidence. T32 is the finite reference integration/freeze. Neither
stage licenses an expansion to arbitrary code rewrite or a new research
program. The complete fixed scope is in NEXT_GATES.md and the parent plan.
`KERNEL_CHECK.log` is included in this archive and records the run; a recorded
PASS is not a substitute for kernel acceptance on the consumer's machine.
