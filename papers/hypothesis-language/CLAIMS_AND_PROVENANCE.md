# Claims, provenance and publication caveats

This is an **append-only editorial statement** distinguishing original claims from corrected scope. It does not delete or rewrite the supplied historical PDF. The proofs and metrics cited below have different evidence strengths.

| Claim | Correct status / scope | Supporting artifact | Excluded interpretation |
|---|---|---|---|
| Semantic version spaces shrink under added consistent observations | Mathematical set inclusion for fixed language and semantics | Manuscript §1 | No guarantee that the world belongs to the language |
| Version spaces may expand under nested language enlargement | Mathematical set inclusion under semantics-preserving embeddings | Manuscript §1 | A certificate for a small language is not a universal certificate |
| Two-sided window of identification | Finite-dimensional nested $\mathbb F_2$-linear spaces, consistent labels | Manuscript §2 / linear algebra proof | Not for arbitrary nonlinear syntax or noisy data |
| Distinguish vs. agreement query | Exact logical distinction for **nonempty** semantic version space | Manuscript §3 | Agreement is not confirmation of origin; singleton-model compatibility does not prove truth |
| Rule 110 post-merger historical recovery | Reported finite fixture in **augmented** CA | Original 7-page PDF §4 | Not a complete-state reversal, not pure two-symbol Rule 110 |
| Gate 5 v3.2 64-site dynamics and 505 nominal local states | **Reported finite observations** from original PDF, not replayed from v3.2 Python here | Historical PDF §§4–5 | Not Lean-proved dynamics and not a minimal alphabet |
| Wolfram Rule 110 table equals its algebraic normal form | Lean declaration and supplied successful verification log | formal/gate5_invariants.lean | Not a proof of all Gate 5 source transitions |
| $C_4$ minimum distance exactly 2 | Lean declarations: lower bound and attained pair | Source and verification receipt | Not a new coding-theory theorem |
| 16/16 single-bit flips detected | Lean theorem for the **defined four codewords** | Lean source | Not proof against physical common-mode or correlated faults |
| 10/24 double flips map back into the code | Lean finite enumeration | Lean source | Not an error-correction guarantee |
| Static liveCert accepts nominal inputs and rejects specified single changes | Lean finite theorem about **an explicit Boolean function** | Lean source | Not a temporal invariant of the whole CA |
| Automatic re-evaluation of liveCert on every relevant CA step | **Not yet formally verified** | Python v3.2 source needed | A static Lean theorem alone does not prove an execution property |
| Full 64-bit origin membership | **UNKNOWN** | Observation map is not injective on unrestricted origins | Observation-class ID ≠ exact initial configuration |
| Five-memory-state lower bound for presented device | **Unestablished as stated**: requires five distinguishable outcomes under identical externally available state | See revised manuscripts §8 | Pairwise coalescence at fixed context does not by itself prove it |
| New representation invented autonomously after falsification | **OPEN** | Proposed next experiment | Query selection within hard-coded four cases is not language invention |

## Supplied receipt, not new verification

The locally supplied log states **Lean 4.36.0**, no sorry/admit/user axioms, exit code 0 and reports these ten theorem declarations:

1. Gate5V32.rule110_eq_anf
2. Gate5V32.c4_dmin_ge_2
3. Gate5V32.c4_dmin_attained
4. Gate5V32.c4_detects_all_16_single_bit_flips
5. Gate5V32.c4_two_bit_boundary_eq_10
6. Gate5V32.liveCert_nominal_all_4
7. Gate5V32.liveCert_blocks_all_vs_mask_mismatches
8. Gate5V32.liveCert_blocks_ans_corruption
9. Gate5V32.liveCert_blocks_single_receipt_bit_flip
10. Gate5V32.no_len2_code_size4_dmin2

Standard axioms shown in the supplied report include propext and, for several finite declarations, Classical.choice / Quot.sound. Exact Lean source SHA-256: **2baaffcb0b30bea445917b3dfbf7c75823cff4213d0ab53b955eb0fbe6b49d78**.

## Original-source boundary

- Historical PDF SHA-256: aa3b995113bfec3313a30f9824f8da27a1d670558ec8a7dc06d92adf70f235fb
- Historical Lean SHA-256: 2baaffcb0b30bea445917b3dfbf7c75823cff4213d0ab53b955eb0fbe6b49d78
- Original verification log SHA-256: d2938e1d26a9e891db8d8bd80cfce3c48084c2176b35922a73ea1091d1d4648c

Changes to the scientific claims in the new editions are expressly disclosed: no claim of pure binary Rule 110, no whole-CA Lean proof, no unconditional five-state bound, no demonstrated optimal alphabet, no public DOI for this new paper and no universal subjective/epistemological conclusions.

## Future release checklist

* Attach the exact v3.2 Python source, frozen input fixtures and full run logs, then replay the full transition system independently.
* State which fault stage is protected (sensor, wire, register before use) and test correlated faults separately.
* Formally connect Lean liveCert to actual reachable local transitions and publish a testable artifact with a pinned toolchain.
* Apply the same evidence contract to a second domain, preferably without a hard-coded four-hypothesis observation table.
* Publish with an openly accessible repository or DOI only after provenance, permission and independent-review checks.