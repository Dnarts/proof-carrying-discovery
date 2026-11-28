# CRTT-T31-v0.1 — Fixed-Provider Compositional Closure

Status: **VERIFIED on Lean 4.36.0.** All nineteen modules compile with exit 0
and zero diagnostics; 503 inherited + 21 MetaClosure = 524 axiom reports are
audited by exact name and by fully-qualified name, with only `propext` and
`Quot.sound` permitted; no `sorryAx`, no `Classical.choice`, no warning, no
error. Toolchain `Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117)`.
See `KERNEL_CHECK.log`.
Parent `CRTT-T30-v0.1.1-verified.zip`, pinned by PARENT_ARCHIVE_SHA256.txt.
All 102 parent manifest entries passed; all eight unlisted historical manifests
were compared directly with their original verified archives and are identical.
All eighteen inherited Lean sources are byte-identical. The T30 source repair
was limited to `decide +revert` in the closed `makeUpgrade.newSound` proof.
Both inherited audit scripts were replayed over all 503 supplied reports, and
the independent `check_policy.py` output was reproduced byte-for-byte.
No new kernel execution is claimed. Expected: 503+21 = 524 reports, 19 modules.

## Exact scope

T31 is the agreed compositional closure gate, not a new level of authority.
A fixed `Provider S T old` is a parameter of every plan, transition, trace and
closed execution. The root S,T, actual old continuation, observations, base
tariffs and checkers are fixed during this finite episode. The active tree
may be replaced multiple times; there is no operation for replacing the
verifier or for redefining its admissibility criteria. The proposal language
is T30's finite executable tree (arbitrary finite depth, including repeated
reads); this is broader than the specific one-query legal class of T19 used
in the T30 synthesis witness. No universal optimality is claimed for it.

`Plan` takes the current machine and a funding proof and supplies a deferred
proof-bearing proposal. The plan list itself is supplied from outside.
`recordUpgrade` calls the actual T30 upgrade once and stores the result with
its equality witness. `Transition` does not contain a separately invented
endpoint; `after` reads that result. `ValidTrace` requires literal state
continuity and uses the same provider throughout. `runPlans` consumes a
finite list of plans, one cell per attempted upgrade even if deferred. Thus
it cannot make an unbounded sequence of free retries. It is an executable
finite schedule, not a claim of a general autonomous scheduler or infinite
self-improvement. Preparation of the plan list, proof construction and
external IO are not independently metered by this pure formal model.

## Candidate theorem map

- `upgrade_facts`, `transition_facts`: an affordable upgrade pays exactly
  base+1 and appends one paid attempt; a deferred upgrade is the identity.
- `trace_laws`: all finite connected histories preserve prior certificates,
  search receipts, evidence journal, base tariffs and old history; retain
  upgrade history; conserve funds; exactly meter fees; count paid and accepted
  attempts. This is one induction independent of history length or policy
  tree depth.
- `trace_paid_balance`, `trace_liquid`: paid attempts are bounded by balance
  expenditure; the existing root completion reserve stays funded.
- `transition_gain`, `trace_no_rejection_gain`: every accepted upgrade reduces
  the actual all-in completion bill by at least one; deferred leaves it
  unchanged. Without paid rejections, final policy bill + number of accepted
  upgrades <= initial policy bill. This is NOT a general global saving claim
  for mixed histories.
- `run_laws`, `run_steps`: the executable list runner generates a connected
  certified history and exactly consumes the supplied number of plan cells.
- `closeRun`, `close`: execute the last installed policy, retain its actual
  observed answers, prepared offers and attempt outcomes, then finish the
  funded root search. `Closed` records exact interpretation and completion
  equalities. `history` concatenates the paid upgrade history (chronological)
  with the actual episode event list; the full upgrade trace separately
  retains deferred steps, and the final Session retains the search journal.
- `closed_preserves`, `closed_funds`, `closed_complete`, `closed_bill`,
  `closed_gain`, `closed_history`: compose the T29/T30 laws through completion,
  including exact reference certificate membership and all-in bill identity.
- `policyBill_le_funds`: a conservative bound from conservation, used for the
  non-improving control plan, not an uncharged prospective execution.

## A necessary distinction at the meta level

T29c's root continuation objective has an exact accepted-gain/rejected-fee
ledger. At T31 the active policy is itself budget-sensitive: a paid rejected
meta-upgrade can change which observations or root migration remain affordable.
It is incorrect to silently assume that policyBill rises by precisely its
rejected validation fee. Only actual charged expenses obey that accounting.
A mixed sequence therefore has no unconditional global improvement claim.
The no-rejection theorem is deliberate, not a weakening of the verified T29c
law. Exact prospective bills are still specification functions, not free
observations at the numeric gate.

## Concrete candidate witnesses and independent tests

Closed Lean candidates check the original T30 7 -> 6 example, an additional
paid rejection erasing that saving (7), two accepted upgrades 8 -> 7 -> 6,
two intentionally rejected control plans (9), and two free deferred plans at
the protected reserve (7). The redundant four-probe incumbent in the
2-acceptance example is deliberately non-optimal; repeated probes are allowed
by the finite interpreter, not the one-query T19 legality relation. All bounds
in these witnesses are on the exact closed fixtures. The non-improving plan
uses the general funds cap; it is not a claim of a useful policy generator.

`check_closure.py` independently runs the inherited finite reference evaluator.
`FINITE_CLOSURE.log` records 965 completed executions, 2418 transition laws,
128 accepted, 1047 rejected, 1243 deferred meta-attempts, 463 no-rejection
inequalities, 725 provider-mismatch and 1066 forged-trace rejections. Each
completed execution reproduces the independently enumerated canonical
certificate set. The test constructs exact prospective bound fixtures offline;
that cost is not measured. The Python provider-identity guard is a reference
model control, not a cryptographic or external proof-decoder implementation.

Counterexample to a naive fee law: with balance 103 and reserve 100, the old
ATTEMPT policy costs 4 all-in. Paying 1 for an unsuccessful upgrade leaves
insufficient funds for the old policy's eventual migration; it now costs 10
including fallback completion. A rejection of price 1 has increased the
all-in bill by 6, without violating any semantic or funding invariant.

## Verification and release boundary

Use Lean 4.36.0. Keep the package bytes immutable and write the new log outside:

    set -o pipefail
    bash run_verify.sh 2>&1 | tee ../T31-KERNEL_CHECK.log

The two inherited strict auditors must pass on all 524 requested reports;
no error, warning, missing name, forbidden axiom or nonzero compiler exit is
accepted. The new manifest includes every payload except itself, including
all historical manifests. Historical logs and manifests refer to their old
revisions, not to current paths. `MetaClosure.lean` is uncompiled in this
preparation environment; Python is not the Lean kernel.

Only T32 (integrated release, final audit and freeze) follows a successful
T31. No new mandatory architecture stage is proposed. This is a bounded
**Recorded outcome.** `run_verify.sh` exits 0 on a fresh extraction of this
archive. Every module reports `Lean exit=0` and passes both auditors, for 524
reports in total. `MetaClosure.lean` reports `21/21 axiom reports; Lean exit=0;
dependencies={'Quot.sound': 21, 'propext': 21}`. All ten auditor fixtures pass,
and the finite checks pass, including the new closure model: fixed-provider
closure, bounded schedules, exact charges, preserved history, terminal
completion and economic controls.

Two defects were repaired:

- Four deprecated names (`dif_pos`, `dif_neg`) were replaced by `dite_eq_left` and
  `dite_eq_right`, which Lean 4.36 requires.
- The history branch of `trace_laws` rewrote with `hb` and `ha` in one step. The
  definition `after` is a bare projection, so `rw [after]` cannot unfold it and
  `show` alone does not reach the goal shape; rewriting with `hb` first and then
  `show after S T x = x.result.next from rfl` before `ha` closes it. Six `sorryAx`
  dependencies descended from this single failure and none remain.

formal reference implementation of deterministic finite discovery under
explicit certificates and tariffs. Durable external storage, physical cost
bounds, new hypothesis synthesis, broader task transfer, stochastic ports,
arbitrary code rewrite, and full-lifetime economic improvement remain outside
this release's claims. The trusted Lean kernel and its declared axioms remain
outside the replaceable state. `KERNEL_CHECK.log` is included in this archive and
records the run; a recorded PASS is not a substitute for kernel acceptance on the
consumer's machine.
