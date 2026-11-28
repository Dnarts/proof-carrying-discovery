# Fixed final gate — T31 -> T32

## Gate T31: verify the closure candidate

Compile MetaClosure.lean. All 524 reports must pass both unchanged auditors.
Repair failures without silently weakening statements or changing inherited
modules. In particular keep the actual upgrade-result equality, fixed provider,
finite list consumption, exact charges, preservation of history and the
qualified no-rejection improvement inequality. The mixed-history liquidity
counterexample forbids a blanket +fee law for policyBill.

## Gate T32: integrate and freeze CRTT v1.0

Only after T31 passes, build a single small executable entry point over the
already verified bounded episode interface (`runPlans` / `close`). Do not
invent a new independent proof calculus, policy layer or new solver.

Required release acceptance criteria:

1. Exact declared finite task, provider, tariffs and initial funded reserve.
   The immutable checker remains distinct from the supplied plan factories.
2. A bounded trace of actual upgrade requests, including free deferred ones,
   one execution of the final installed policy, then funded root completion.
   An explicit terminal report distinguishes full certified completion from
   blocked/deferred intermediate attempts. Do not promote a failed attempt
   to a successful replacement. If extending beyond the funded reference
   scope, return honest unresolved status rather than claiming completeness.
3. Expose final canonical certificate membership, preserved predecessor
   certificates, ordered paid history, actual observation answers, prepared
   offers and their admission status, balance, spent and the completion bill.
   Printed/serialized metadata is a projection, not an external proof decoder.
4. Reproduce the closed 7 -> 6 witness, the two-acceptance 8 -> 7 -> 6 witness,
   paid rejection erasing savings, protected fallback and the liquidity
   counterexample. Include the whole declared bill, and distinguish abstract
   costs from wall-clock and offline proof preparation.
5. Provide a single pinned Lean 4.36.0 toolchain and runner, both strict audit
   parsers, exact manifest coverage, all required reports, independent finite
   test output, and a consolidated architecture/specification document with
   a precise scope and limitations. Historical files remain immutable.

Freeze the architecture once these criteria pass. If a necessary criterion
fails, repair inside T32 or report it as a blocker. Do not create T33 merely
because further generalizations are interesting. Post-release research is
optional and explicitly separate (crash recovery, actual resource profiling,
automated proof acquisition, learned state migration, stochastic and broader
problem classes). T31 establishes closure under finite histories in the
specified language; it does not establish unrestricted recursive self-rewrite.
