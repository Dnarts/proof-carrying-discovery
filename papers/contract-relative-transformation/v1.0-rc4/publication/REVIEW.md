# Response to the cold peer review — RC4

Manuscript: *Contract-Relative Transformation Theory: From Certified Discovery to Meta-Policy Closure*.

Revision status: editorial revisions implemented; independent kernel reproduction and persistent artifact identifier remain outstanding. This document records the response to the supplied review, not acceptance by a journal or an independent reviewer.

| Review item | Response | Location / status |
|---|---|---|
| 2.1 Supply-side assumption | Distinguish computable structural potential, conservative funded-plan bounds, paid exact-cell acquisition, conversion of absolute certificates to joint rows, and closed finite proposal synthesis from externally supplied tight comparisons, hypothesis membership, and general proposal factories. Exact evaluation can require completing a search; no generic cheap certificate producer is claimed. | Section 9, “What the certificate producer must supply”; source locators in SOURCE_MAP_D.md. Addressed as a scope clarification, not a new solver theorem. |
| 2.2 Internal stage numbering | Replace Txx headings and narrative references with mathematical concepts and section numbers. Retain the stage crosswalk and missing historical links only in the artifact/evidence section. Keep the earlier sources, original identifiers, and proof lineage in the supplement. | Sections 1–7; artifact crosswalk in Section 8.1. Addressed. |
| 2.3 Lean and DOI | Preserve the successful supplied transcript and repeat the independent Python replay. Add a clean-extraction wrapper using the exact formal archive hash and unchanged canonical runner, recording environment, raw process log, exit code, and log hashes. The current local attempt passes preflight but stops before Lean compilation (exit 127). No DOI has been minted or claimed. | Section 8.3; supplement/FRESH_VERIFICATION.md, verify_fresh.sh, local_attempt/, replay_rc4/. Independent fresh compilation and public artifact deposit remain OPEN. |
| 2.4 Companion citations | Keep three closely relevant companion preprints in the main references: 110 OBSERVER, Essential Inputs and Memory after Coalescence, and Representation, Incremental Memory Value, and Budgeted Control in Finite Channels. Keep the formal artifact citation separately. All eight previously supplied Zenodo records remain in a standalone companion bibliography and the original audit files. | Section 9; References; supplement/COMPANION_REFERENCES.{tex,pdf}. Addressed. The main bibliography has 19 entries, of which three are companion papers and one is the author's formal artifact. |
| Notation Q | Use Q for observation ports, Lambda for the search-receipt list, including continuation equivalence. | Sections 3, 4, 6. Addressed. |
| Worked example | Follow the existing depth-obstruction fixture across morphism nonexistence, exhaustive versus certified pruning, direct root replacement, and the synthesized single-upgrade policy. Separate alternative executions with costs 7, 3, and 6; do not treat them as consecutive bills. Keep the separate nonempty and predecessor fixtures. | Section 8.2; exact source locators in SOURCE_MAP_D.md. Addressed. |
| Reference [8] | Match the official arXiv abstract page, arXiv:1612.02353, and render the identifier as plain linked text. | References. Addressed. |

## Verification boundaries

No Lean source or accepted theorem was modified. The paper still has 20 pages. The fresh wrapper is a reproducibility aid, not a proof of successful fresh compilation. The repeat Python replay returned PASS for 21 module logs, 542 exact audit reports, nine CLI cases, and 45 commands. The separate fresh-run attempt returned 127 because Lean is absent in this environment. The prior successful Lean transcript remains the evidence of compilation; the replay is not an independent compiler run.

The main text's mathematical theorem environments retain their statements and proofs apart from consistent notation and replacement of internal stage labels with section references. The added worked example and discussion interpret existing formal objects and fixtures rather than introduce new unverified mathematical claims. The existing external Zenodo resolution caveat is retained. The [8] metadata was checked directly at https://arxiv.org/abs/1612.02353.

## Outstanding publication gates

- Obtain an independent fresh run with the pinned Lean compiler and publish its raw evidence (the supplied wrapper describes the procedure).
- Publish the immutable formal artifact with its SHA-256 and actual version-specific DOI, then update the artifact citation.
- Submit RC4 for external reassessment. Editorial response does not imply peer-review acceptance or satisfy every venue's artifact policy.
