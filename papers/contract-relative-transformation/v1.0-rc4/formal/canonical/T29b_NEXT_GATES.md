# T29b -> T29c -> T30–T32 (fixed closure plan)

## T29b acceptance (current candidate)

Compile AdmissionAccounting.lean on the pinned 15-module verified parent.
Require all 451 reports, no warnings/errors and only propext/Quot.sound.
Preserve the plain GateInput and the exact verdict reflection theorems. In
particular, do not bypass typed economic evidence or weaken reserve checks.
The original T29a_NEXT_GATES.md remains the reference for the scope.

## T29c (blocked on T29b)

Use the verified AdmissionAccounting Session and actual tryRelative function.
Avoid the failed two-endpoint indexed Step family. First prove the generic
prefix spending identity with ResumeLaws, independently of histories. Use a
state-indexed Action with only one index, and an explicit Transition record
containing its input and its typed action. Compute the output by execution;
validate successive adjacency separately. Alternatively use bounded structural
recursion with an action producer that is typed at the current state. A
function-bearing Session need not admit an executable equality test; don't
invent one. Require a theorem for all legal finite sequences, not just a
single policy or a hand-selected sequence of endpoints. No arbitrary endpoints
in lieu of execution witnesses.

Lift the verified accepted/nonaccepted/evidence objective laws; prove exact
ordinary-prefix conservation. Then telescope:

    Phi(final) + sum(accepted net gains)
      = Phi(start) + sum(rejected check fees + external evidence charges).

Prove funds conservation, a bound on paid attempts, certificate and receipt
preservation, fixed base fees and full completion after the history. Test a
strictly beneficial sequence and a sequence whose failed checks erase all
local gains. Deferred steps are free, so paid-step bounds alone do not establish
scheduler termination. Do not claim that an external evidence receipt proves
actual acquisition; that integration is T30.

## T30–T32

Retain the scope of T29a_NEXT_GATES.md verbatim as the closure target:
T30 one executable finite meta-policy with charged actual queries/evidence,
T31 invariant closure of the admitted transition interface including policy
replacement, T32 bounded total runtime, a nontrivial reproducible witness,
frozen controls, clean kernel audit, unified entry point and release freeze.
Additional generalizations (unrestricted controller code, stochastic evidence,
external persistence, broader learning state, universal speedup) are explicitly
outside the mandatory finite reference release unless separately agreed.
