# Fixed closure plan: T29c -> T30 -> T31 -> T32

## T29c acceptance (current candidate)

Compile RecursiveTrace.lean and audit all 484 declarations. In particular,
verify the generic prefix law independently of trace induction, then local
laws and the connected-list induction. Require all source statements to stay
unchanged unless an explicit repair note proves semantic equivalence. Do not
weaken adjacency, reserve preservation or actual transition semantics to
obtain a compiling package. The closed positive and negative witnesses are
mandatory. A Python pass is not a Lean pass. T29b remains verified regardless
of a T29c compile failure.

After T29c passes, the following three stages are the ONLY mandatory
architecture stages. Their criteria are inherited from the frozen T29a plan,
reproduced below. Any other discovery is a separate research branch, not a
new prerequisite for the finite reference architecture.

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
