# CRTT v1.0 — FROZEN (T32)

Mandatory architecture gates are closed. The accepted inner RC1 package is retained byte-for-byte, including its historical labels and manifest. The supplied final successful compiler/runtime journal is external to the inner immutable package, as required by RELEASE_ACCEPTANCE.md. No Lean source was edited in this freeze.

## Acceptance

- 143/143 manifest entries; 19/19 upstream source pins; 18 historical standalone checks.
- 21/21 Lean files compiled according to the supplied Lean 4.36.0 log, 542/542 exact-name audited reports, only propext and Quot.sound where required; no forbidden axioms or compiler diagnostics. ReleaseMain compiled and executed.
- Both strict audit scripts replayed against the supplied log, not a new kernel run.
- All 9 independent release fixtures recomputed; actual supplied Lean CLI projection compared successfully.
- Ten audit-parser and twelve projection-parser controls passed.
- Parent and all inherited source bytes preserved. The original earlier failed log is a historical artifact, not the final witness.

## Reproduction

Verify the outer SHA256SUMS.txt, extract the inner ZIP in a fresh directory, and run its run_verify.sh with Lean 4.36.0, saving the new log outside the immutable package. The log stored here is a supplied compiler witness; hash binding and replay do not cryptographically attest execution.

## Scope

Finite deterministic, funded proof-carrying reference architecture, fixed root task pair, provider, tariffs and checker within an episode, externally supplied typed evidence and finite plans. Proof-bearing result and report projection are distinct. Model fees are not measured CPU, wall time or proof-preparation cost. No unrestricted self-rewrite, general automatic evidence generation, autonomous unbounded scheduler, or general physical performance guarantee. Architecture frozen; future research is outside the mandatory release. No T33.
