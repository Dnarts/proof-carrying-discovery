# Finite closure plan — T29a/b/c, then T30–T32

This is a proposed scoped completion plan, not a prediction of successful
proofs. Do not add gates merely because another abstraction can be invented.
The target is a closed finite proof-carrying reference architecture, not
universal research automation, general optimality, or self-verification of
its own trusted kernel.

## T29a (current) — relative evidence

Acceptance: 21 new axiom reports pass on Lean 4.36.0; inherited 395 reports
pass, exact source names and axioms are audited. The relative test must retain
joint actual coverage and strict gain including validation and migration.
The T27 adapter must retain the incumbent-margin hypothesis. T28 singleton
embedding must preserve the same proposed continuation. No new runtime.

## T29b — AdmissionAccounting (blocked on T29a)

Use a plain numeric GateInput and a non-dependent Verdict, not an inductive
verdict whose constructor contains a dependent match proof. Let H=check fee
(positive in the public attempt), K=migration, Ro=old reserve, Rn=new reserve,
B=balance, and G=relativeOK(H+K, rows).

    gate(input) =
      if not (H + Ro <= B) then Deferred
      else if not (H + K + Rn <= B) then RejectLiquidity
      else if not G then RejectGain
      else Accepted

    debit(Deferred) = 0
    debit(RejectLiquidity | RejectGain) = H
    debit(Accepted) = H + K

First prove reflection of the independent numeric gate: accepted iff all
three guards hold, plus a separate guard proof for each rejecting verdict.
No Session or Offer argument is needed in that theorem. The typed application
phase uses these lemmas to obtain funding; never derive funding by rewriting
inside a proof-dependent match. Use proposed_reserve from T29a to relate the
candidate reserve to the installed continuation. Make the receipt debit law
explicit; prove it before attempting a charge theorem. Use one charge helper
with a stated debit, a debit+reserve affordability proof, and a receipt-cost
identity. Proofs may be supplied to the typed application; they are not new
unchecked runtime authority. The implementation must preserve:
- deferred = exact old state, zero charge;
- rejection = exact old continuation, debit H, reason receipt;
- acceptance = T29a proposed continuation, debit H+K, relative gain;
- old certificates/search receipts and all histories preserved;
- funded fallback at all outcomes and conservation of total funds.
Keep the distinct relative-admission journal; no fabricated T28 absolute-pass
receipt. Optional external evidence acquisition is recorded with positive fee
and fallback liquidity. A receipt alone is not evidence of obtaining truth.
Do not expose a T29b archive before T29a passes. Do not weaken proofs of T28.

## T29c — RecursiveTrace (blocked on T29b)

Avoid the two-endpoint indexed inductive family from failed T29. Prefer:

    Action(s : Session) : Type
    execute(s, a : Action(s)) : Session
    Transition = (before : Session, action : Action(before))
    after(t) = execute(t.before, t.action)
    Trace = List Transition
    ValidTrace(s, trace) : Prop -- successive before = previous after

Alternative if simpler: structural recursion on fuel with a state-indexed
policy that supplies the next Action. A finite trace proof must quantify over
all legal traces and preserve adjacency; neither approach may replace an
actual transition by an arbitrary endpoint satisfying a postcondition. Valid
Trace is a proposition, not necessarily an executable equality test on
function-bearing Session. Verify the one-step effect theorems before induction.

Required properties: exact prefix-accounting law for ordinary execution using
T22.9/ResumeLaws; accepted decrease, rejection increase by H, external paid
evidence increase by fee, deferred equality; exact telescoping identity
Phi_final + sum accepted gains = Phi_initial + sum paid nonproductive overhead;
funds conservation, paid attempt bound, cumulative provenance and fixed base
fees, final completion of the unchanged root. Demonstrate a positive mixed
trace and a negative trace whose rejection overhead erases local gains.
No global improvement from the mere existence of accepted transitions.

## T30 — one executable meta-policy

After T29c passes, integrate ONE finite query/offer policy (T19/T27) with the
T29 runtime, including actual paid observation, evidence preparation and
validation accounting. Show a nontrivial policy change under a fixed verifier
and fixed tariff contract, with honest baseline and fallback. A claim of
cheap evidence acquisition needs a witness, not a supplied exact cost oracle
whose preparation cost is omitted. Preserve full LearningDiscovery state if
claiming a change of that full state; otherwise scope the reference to static
T23 controllers and explicit learning-to-static handoff. Do not imply arbitrary
code rewrite. Runtime termination requires a fuel/resource decrease for every
nonterminal iteration, including deferred attempts. If an optional extension
fails, keep an explicit negative/unsupported scope instead of opening an
unbounded new line of proof gates.

## T31 — closure theorem

State one invariant over the chosen finite architecture and prove inductive
closure under ALL admitted transitions, including changing the proposal policy.
The kernel and root contract stay fixed. Arbitrary finite depth/number of
admitted applications is a quantified property of the one transition
interface, not a requirement to create a new controller type at every level.
Prove preservation of unresolved obligations, accumulated certificates,
resource bounds and provenance with a meaningful non-vacuity witness.

## T32 — freeze / reference release

One executable entry point, explicit bounded termination (certified result or
honest unresolved state), independent checker, complete provenance and ledger,
clean Lean audit and reproducible end-to-end comparison against frozen
baselines, including negative controls. Distinguish model fees from measured
runtime and full-lifetime amortization. If a capability is not proved in the
chosen scope, it remains an explicit limitation. A failure in an obligatory
closure condition blocks that claim; extra features do not extend the release
scope. Production persistence/crash recovery, stochastic ports, generalization
across unrelated tasks and unrestricted policy synthesis are subsequent work,
not reasons to recursively expand the finite reference architecture.
