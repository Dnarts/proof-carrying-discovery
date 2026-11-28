# T28 → T29 — authority, improvement and recursive control

## Gate 1 — kernel validation

Compile and audit all 395 requested declarations, including the closed concrete
witnesses. Preserve exact definitions and statements on repair. The existing
finite cross-check is not a kernel check.

## Gate 2 — evidence-to-admission bridge

T27 certifies a decision relative to the reference on a finite admitted belief.
T28 accepts a continuation replacement only when independent bound witnesses
prove a strict improvement over the actual incumbent and sufficient liquidity.
Do not conflate these. For each compatible hypothesis h, require a certified
upper bound U_new(h) for the exact migrated continuation and a lower bound
L_old(h) for the exact incumbent. Require H+K+U_new(h)<L_old(h) for every h in
the belief, or prove a different explicit comparison objective. Additionally
require truth membership, nonempty belief, identical root and tariff contracts,
no stale evidence, and a separate reserve proof. If the true table is outside
the belief, return ModelViolation. Acquisition and all failed checks cost
resources, even when the final candidate is admitted.

## Gate 3 — improvement potential over a sequence

Define P(s)=spent(s)+remainingBill(current(s)). T28's accepted_finish_gain is
strict decrease for one accepted attempt. Prove separately that paying a search
prefix while leaving the policy fixed conserves P (composition of deterministic
execution; use actual residual reserve, not a newly quoted full-search bill).
A paid rejection raises P by the validation fee. An unexecuted/deferred
attempt changes neither. Therefore a chain of accepted replacements alone has
length bounded by initial natural P, and a mixed trace must explicitly account
for rejected-check and acquisition costs before claiming global improvement.
Repeated accepted local improvement does not imply globally optimal policy or
better real-time performance. Do not infer termination if the scheduler can
repeat free administrative actions.

## Gate 4 — transactional extension to LearningDiscovery

A live learned state has a frontier, active core library, pending compilation,
learning history and feesPaid trace. Merely swapping its Frontier is not a
replacement of the entire state. Specify which obligations survive handoff,
which optional learning steps are cancelled, and how all receipts survive
exactly once. Prove a commuting projection to the T22 reference; retain the
reasons even when old active rules are superseded. Model the failure of a
partially committed migration; the pure functional T28 interface has no storage
or crash model. Preserve atomic readback and immutable provenance if persisted.

## Gate 5 — recursive admission without self-certification

The object being replaced becomes the controller that proposes and evaluates
other replacements. Keep the root contract, tariff authority, admitted proof
language and independent verifier fixed. A proposal can change the policy but
not relax its own obligations. Separate proposal computation, evidence
acquisition, verification and deployment from the actual commitment. Construct
one finite typed recursive instance and prove preservation by induction on paid
transitions. Do not claim unrestricted self-improvement or universal optimality.
