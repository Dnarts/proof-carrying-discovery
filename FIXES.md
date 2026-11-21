# Audit findings → v1.1 corrective actions

## Publication patch v1.1.1 — 22 November 2026

- The certificate checker now independently checks the four transition destinations and matching `q0` increments required by the phase-linear argument. A previously valid invariant must not certify a table whose control flow has since changed. Regression checks cover ten such mutations across the two target families. The inference pipeline's measured results are unchanged.
- The failure-cost convention is explicit: 200,000 is a penalty for an unsuccessful task's base search/proof component, while normalization and acquisition are charged separately. The final aggregate ceiling is `number_of_tasks * 200000 + 1000000`.
- The wrong-transfer control reports **205 + 57 = 262** attempted branches, including the failed restricted attempt.
- Added a complete English preprint and an accessible English-first, Russian-second README. Both papers describe the same results and limits.
- The exact v1.1.0 source archive is retained in `history/`; v1.0 sources remain unchanged in `legacy/`. The MIT license already present in the publication repository is preserved.
- The publication CI exposed a Python-version difference in floating-point `sum`: five `sum_W` values differed by at most `8.89e-16` on the older summation behavior, although programs, costs, individual Shapley values, and history hashes matched. The two aggregations now use `math.fsum`. A regression replay emulates sequential summation and still requires exact equality of the complete deterministic report; no comparison tolerance was added. The saved numerical results are unchanged. See [Python's 3.12 summation change](https://docs.python.org/3.12/whatsnew/3.12.html#other-language-changes) and `evidence/numerical_portability.json`.

## Earlier audit: v1.0 → v1.1

**Audit source:** `legacy/V1_AUDIT.ru.md`, 22 Nov 2026. Original v1.0 files are unmodified. This is a revised artifact produced *after* inspecting v1.0 results; neither source timestamps nor this changelog claim independent preregistration.

| Audit finding | Correction in v1.1 | Evidence / residual limitation |
|---|---|---|
| Static Shapley misnamed as historical | All 8 coalitions start with NAND only and **replay e1, e2, e3 in fixed order**, enforcing the e3→e2 dependency | `abc_historical_v1_1_results.json → replays[*].history`. Fixed curriculum; no endogenous task generation |
| Acquisition costs absent | Each coalition records XOR synthesis, law discovery, law-certificate comparisons, gate replay and normalizer calls; for a task suite acquisition is charged once | Cost ledger and sensitivity λ=0…5; modeled work, not physical cost or full administrative overhead |
| Normalization ignored in original W | Default W adds **one work unit per call** to normalize_nf; λ varies separately | `sensitivity_suite`; unit weights are a declared convention, not hardware calibration |
| No solution within gate limit misread as time | Record `found=false`; assign an explicit failure penalty to the base component, then add normalization and acquisition | Existing base cases at 3/4-gate depth are unresolved within the declared grammar; this is not observed unbounded time-to-success |
| Rounded Shapley called exact | Calculate with unrounded floating-point values; report efficiency residual and separate exact finite coalition enumeration | `sum(W)=v(full)` to tolerance; logarithms are floating-point |
| MN `N_K > 5` over-interpreted | Emit all 15 distinguishing suffix witnesses for N=6; label bound **DFA≤5** only | `dfa_to_1dca_v1_1_results.json → pair_witnesses`; no proof of nonregularity for unknown teacher |
| Finite observation table treated as global equivalence | Enforce table closure/consistency; only explicit 5-state regex reference has an exact product-DFA certificate | Arbitrary membership oracle remains `UNKNOWN`; adversarial finite-teacher test included |
| Unknown teacher identity can be faked by a metadata label | Only built-in known target-family oracle receives the conditional target-family certificate; external wrappers return `UNKNOWN` | `tests/test_release.py` checks disguised-oracle negative cases. Not a security sandbox |
| Phase-linear discovery overstated | State that grammar **q0 c=a*m; q1 c=a*m+b*k+d** is fixed; infer coefficients from transitions without an offset hint | Coefficients plus 8 obligations and separately recomputed fields; no arbitrary-formula synthesis or Lean proof |
| Certificate can silently trust its own flags or labels | Check exact obligation keys and values, labels, initial and bridge conditions directly against exported table | Tampered coefficients/transition/labels rejected by tests |
| Incorrect transfer law destroys solution | Use restriction **provisionally**; if no acceptable certified candidate, rerun **unrestricted** from the same history | Wrong slope `(1,1)` now fails restricted mode then solves at 57 nodes; correct transfer remains 28 nodes |
| End marker/tail accepted incorrectly | Whole-word framing and reject on trailing symbols after ACC/REJ; DFA runner rejects malformed alphabet too | `01$$`, `01$0`, `01$1`, `01x$` negative tests, independently checked on 9,841 short strings per DCA |
| Unsupported claim of original theorem novelty | Bound all statements to declared programs, candidate languages and cost game | `PREPRINT_v1.1.ru.md`; related work on Angluin, DreamCoder, babble, causal Shapley and DOCA |
| Unstable machine hashes | Preserve all original SHA-256; publish a content-manifest and compare deterministic projections excluding timing and platform | `MANIFEST.json`, `SHA256SUMS.txt`, `tests/audit_release.py` |
| Nontransparent provenance of patches | New version and explicit generator; predecessor history retained, no SHA-based similarity reattachment | `v1_1/build_dfa_v1_1.py` and `legacy/` |

## What cannot honestly be "fixed" by a local patch

1. No finite list of membership queries certifies exact equivalence to **an arbitrary unknown target language**. A teacher contract or a genuine equivalence oracle is required. v1.1 *narrows the claim* rather than claiming to solve an impossibility.
2. Neither Shapley attribution nor program-bit cost is invariant under arbitrary **splitting/merging players, encodings, budgets or search languages**. Those elements are now explicit arguments of the game.
3. A fixed phase-linear inference template does not discover a new architecture of representation, nor a novel mathematical theorem. The available two-tier hierarchy and regex/offset families remain given.
4. The **complete physical cost** of discovery (wall-clock under all machines, energy, memory traffic and compiled implementation complexity) has not been measured. v1.1 uses a declared multidimensional ledger plus sensitivity, not a false zero.
5. No Lean kernel verification or general DOCA equivalence algorithm has been added. The exact product check is **only** for two explicit five-state DFAs; the offset-family argument is a template-scoped induction.
6. The new history replay is deterministic and on a *fixed curriculum*. It measures a well-defined event-sequence causal game, not the full open-ended evolving research process.

## Release hierarchy

- `legacy/`: original version, original observations; no changes.
- `v1_1/`: corrected version and new values. Never reuse v1.0 Shapley numerical values as v1.1 measurements.
- `tests/`: independent replication of observable behavior within this Python project; no outside-laboratory attestation.
