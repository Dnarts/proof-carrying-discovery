# From acquiring cost knowledge to certified controller replacement

## Gate 1 — Verify current candidate

Compile MetaEvidenceAcquisition and audit 316 declarations without weakening statements. The package label T26 is a research-phase label; the implemented module targets T25.8–12. No Lean proof is assumed just because the finite reference model passes.

## Gate 2 — Avoid a second-order free oracle

The current fixed sequence of requests is explicit and paid; it is not chosen by an optimal acquisition strategy. The next abstraction is an information state `E` comprising possible cost tables and an available finite query set. Each query has a deterministic observable response and charged cost. A decision at an E-node may either return a legal controller or purchase evidence. For a finite catalogue H of possible tables with actual truth guaranteed in H, terminal controller loss can be the worst-case regret relative to each table's optimal minimax controller, or its actual objective bill. Do not mix those objectives. Account for costs of preparing H, validating actual membership, solving the acquisition tree, and executing the selected plan. A finite binary query interface can be expressed using T19; multi-valued queries require a declared binary encoding with cost semantics, not free extra observations.

A candidate Bellman recurrence for a *regret* objective is

    F(E, Q, d) = min(terminalRegret(E),
                     min_{q in Q} [fee(q)+max_{b in nonempty responses} F(E_b,Q\{q},d-1)])

where `terminalRegret(E)` minimizes over a finite list of admitted controllers the maximum, over all compatible cost tables, of that controller's worst bill minus that table's optimal value. This is an optimal acquisition strategy only under the declared hypothesis and cost model; generating the full hypothesis set or precomputing all optimum values may itself be expensive. Reuse T19 to prove the recurrence with explicit legal-action and observation membership rather than assuming optimality.

## Gate 3 — Separate certainty of decision from exact knowledge of value

The gap VU-VL can be positive even when one controller is optimal in every compatible table (e.g. one available action). It is a sufficient, not necessary, certificate. For a finite set of controllers, pairwise interval dominance gives a tighter sufficient certificate when common costs cancel. A necessary-and-sufficient robust-regret theorem over a declared finite set of compatible tables is possible by explicit enumeration, but does not by itself supply a cheap algorithm. Compare certificate acquisition costs and scope against the existing gap test.

## Gate 4 — Admission of replacement

Define a root contract, the current remaining obligations, the resource account and a typed continuation. Candidate replacement must preserve root semantics and reference coverage, carry forward the unresolved frontier and provenance, and certify liquidity as distinct from amortized cost. A controller replacement is not licensed merely because its predicted bill is lower.

A proposal can be admitted by an independent checker if (1) semantic and continuation certificates pass, (2) all deployment and acquisition charges are reserved, (3) a declared improvement predicate holds with the correct reference and comparison horizon. A static valid controller remains admissible even if no replacement can be justified. Do not let the proposal redefine the root contract or declare itself verified.

## Gate 5 — Transfer and cumulative learning

Distinguish a schema sound in every task pair from actual economic dominance in a new pair. To transport economic evidence, require a proved cost bound/reflection in the new problem; to transport a controller, require a T20 morphism at the actual meta-problem level. Store evidence with task IDs, source artifact IDs, contract, validity scope and cost model. Retain predecessor history; a later active rule may supersede a previous rule but does not erase the reason.

## Gate 6 — Recursive controller synthesis

Use a fixed kernel over typed proposed replacements. At each level permit search, evidence acquisition, admission, execution and retention only through an explicit transition; bound total positive paid steps independently of termination of the full search. A theorem for finite admitted portfolios is not an unrestricted self-improvement theorem. Demonstrate nontrivial safe replacement on an independently specified new family, with static, ordinary pruning, compulsory-learning, no-acquisition and full-offline-table controls. Report pointwise loss, worst-case cost, acquisition bill, reserve and regret separately.
