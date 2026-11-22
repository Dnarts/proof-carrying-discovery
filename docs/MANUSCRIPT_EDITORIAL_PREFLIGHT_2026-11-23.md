# Editorial and TeX manuscript preflight — 23 November 2026

This is a **repository-side audit report**, not part of any manuscript or proof. It reviews current and historical research manuscripts in Proof-Carrying Discovery, Rule 110 Dependency Fronts (including its 110 OBSERVER v2.2.1 multilingual tag), and Channel Topology and Memory.

## Edits completed in Proof-Carrying Discovery

- Hypothesis Languages: [English](../papers/hypothesis-language/HYPOTHESIS_LANGUAGE.en.md) and [Russian](../papers/hypothesis-language/HYPOTHESIS_LANGUAGE.ru.md) working papers no longer have an editorial-history header, standalone research-plan section or SHA/provenance appendix. Mathematical claims, limits and references are preserved. Provenance stays in the [separate ledger](../papers/hypothesis-language/CLAIMS_AND_PROVENANCE.md).
- Cumulative Search v1.1: [English](../papers/cumulative-search/CUMULATIVE_SEARCH.en.md) and [Russian](../papers/cumulative-search/CUMULATIVE_SEARCH.ru.md) **clean reading editions** remove process-status labels and next-experiment paragraphs. Historical v1.1.1 Markdown, PDFs and hashes remain unchanged.
- The four cleaned Markdown editions passed source-level dollar-math pairing, math-brace matching and editorial-plan heading scans. [GitHub release verification after changes](https://github.com/Dnarts/proof-carrying-discovery/actions/runs/45079862515) succeeded. These checks are not a full PDF build.

## Open publication-hygiene findings in historical publications

| Source | Finding | Publication-safe treatment |
|---|---|---|
| Supplied seven-page Hypothesis Language PDF (22 Nov) | Page 6 Lean theorem table has crowded/colliding rows; page 3 has a congested flow diagram. Abstract mixes in source SHA and developer-verification status. | Preserve the historical PDF; issue a newly typeset PDF with a new edition identifier, not a silently relabeled original. |
| 110 OBSERVER v2.2.1 Russian/English/Chinese tagged monograph | A leading snapshot block contains developer labels PASS_DEV, NOT_RUN, DECLARED_NOT_DERIVED. Discussion §7 contains the unexecuted T3 experiment protocol and future-panel checklist. | Keep the tag immutable. In a revised edition, place protocols and planned panels in a separate research-protocol document, while retaining empirical negative boundaries. |
| 110 OBSERVER Hebrew manuscript, main branch | Shares the monograph's unexecuted-experiment content. | Change the TeX and published PDF together in a new edition. |
| Rule 110 Continuation English | The included verification-status.tex contains a verbose publication reconstruction narrative and historical failed-log discussion. | Keep concise reproducibility / AI-assistance acknowledgement, move engineering chronology to verification docs when revising PDF. |
| Rule 110 Continuation Russian | PDF exists but its Russian TeX manuscript was not located in continuation/paper on main. | No claim of Russian source-level compile validation. |
| Channel Topology and Memory unified monograph | Part III is titled “Interpretation and a Scoped Research Program”; synthesis conclusion contains explicit future-work questions. | Move future research agenda to project documentation in a new PDF edition; keep limitations and measured negative controls. |

## TeX source and PDF preflight

- The active Rule 110 Paper I v2 EN/RU/ZH/HE, Paper III English and Observer Hebrew TeX files have balanced begin/end environments and no missing local labels or bibliography keys in the source-level check. The tagged Russian Observer main + all included sections also has no missing labels or cites. Three channel-topology/manuscript source dependency sets likewise had no missing bibliography keys / local references.
- The previously reported Chinese literal earpage error is **absent from the current Paper I v2 Chinese TeX**: line 290 contains the valid LaTeX command clearpage. Substring matching earpage inside clearpage is a false positive.
- Existing PDFs were found as GitHub binary blobs, but this audit **did not independently compile all TeX targets or visually review every PDF**. A PDF header and balanced LaTeX environments do not demonstrate absence of font, hyphenation, overfull-box, bidi or figure-layout defects.

## Scientific boundary that must remain explicit

Language-relative uniqueness is not origin membership; the Gate 5 augmented local automaton is not pure binary Rule 110; the ten Lean checks prove listed finite coding and certificate-predicate statements, not the full 64-site dynamics; parity checks do not authenticate arbitrary correlated faults; and an AI-assistance acknowledgement is an ethical publication disclosure, not gratuitous metadata.

The original scientific history, its checksums and explicitly unsuccessful tests have not been deleted or rewritten by this audit.
