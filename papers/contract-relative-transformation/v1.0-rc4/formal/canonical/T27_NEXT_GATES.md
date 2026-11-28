# T27 next gates — from a decision certificate to a replacement certificate

## Gate 3/2 completion (current candidate)

Compile DecisionEvidence.lean against the pinned T26.1 parent. Verify all new
axiom reports with no weakening. Establish the stated exact and sufficient
criteria on the declared model. The output of hardAssess is a decision tree
certificate for the finite evidence model, not permission to replace a live
controller. Do not confuse catalogue optimum with full-interface optimum.

## Gate 4 — independently admitted controller replacement

Define a versioned contract C and a state with remaining obligations O, paid
trace, root task, frontier, active controller and historical provenance. A
replacement is not merely a new controller with small predicted regret.

Proposed dependent types:

    Continuation(C) = State x Frontier x OutstandingObligations x Witness
    Replacement(old : Continuation C) =
        candidate : Controller C
        transport : ContinuationMap old candidate
        root_preservation : ...
        outstanding_coverage : ...
        history_preservation : ...
        affordability : ...
        economic_witness : ...

The semantic contract must be fixed before evaluation. The transport must
preserve unresolved obligations, not just already found certificates; new
certificates must be sound. Separate semantic equivalence from order or
multiplicity of list outputs. Prove identity and composition for the actual
continuation relation, and make rejection leave the authoritative continuation
unchanged except for the correctly charged check/attempt receipt. No unchecked
candidate may alter the trusted state. Never use a later successful outcome
to retroactively mark an invalid admission as valid.

### Liquidity is not amortization

For nonnegative Nat costs, let H be paid acquisition and validation overhead,
K the additional migration/setup charge, R a sound upper bound on funds
needed to finish the remaining work, and B the current uncommitted balance.
Past charges H may be sunk for the incremental decision, but remain in the
full ledger. One safe admission rule is K+R <= B (accounting for any required
simultaneous reserves). A separate end-to-end economic test compares actual
or certified upper costs against a justified lower bound on the specified
reference continuation; state the horizon and which costs are sunk. A plan
may be cheaper and still unaffordable. A fixed reserve may be larger than the
realized bill. Gate 4 must not confuse these objects or charge unused reserves
as spending.

### Decision safety versus safe exploration

A robust regret result is conditional on actual truth membership. A controller
may be semantically valid but economically suboptimal. If the observed response
contradicts every declared hypothesis, emit ModelViolation, not a vacuous
certificate from an empty belief. If information is insufficient, return the
intact continuation or invoke a separately certified fallback. Totalize the
runtime interface only through explicit proof obligations.

## Gate 5 — acquire/transport evidence without a second-order free oracle

The current optimal solver uses a supplied finite catalogue and supplied
exact regret table; only the online query selection is optimized. Consider
symbolic families of hypotheses with an explicit denotation, certified pruning
of incompatible tables, and bounds on regret that do not enumerate every
completion. Charge construction, benchmark computation, checking, storage,
lookup and planning. A reusable certificate can be transferred only through a
witness relating actual query semantics, root objectives and reference costs.

Candidate research question: can a sufficient decision certificate be
constructed and transferred at smaller total cost than reconstructing the full
meta-cost table, under an explicit class of task streams? A universal claim of
strict improvement is false without assumptions. Compare against no acquisition,
fixed acquisition, full acquisition, the current interval test and clairvoyant
lower bounds. Preserve the independent economic and semantic gates.
