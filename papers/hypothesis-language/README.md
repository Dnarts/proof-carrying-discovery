# Hypothesis Languages — reading guide

**Current main publication: Gate 11–12 v12.3.** [English PDF](translations/gate11-gate12-v12.3/hypothesis_language_gate12_en.pdf) · [简体中文 PDF](translations/gate11-gate12-v12.3/hypothesis_language_gate12_zh.pdf) · [Russian PDF](gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf) · [עברית PDF](translations/gate11-gate12-v12.3/hypothesis_language_gate12_he.pdf) · [LaTeX source](gate11-gate12-v12.3/src/hypothesis_language_gate12_ru.tex) · [reproducible ZIP](gate11-gate12-v12.3/gate12_reproducible_bundle.zip) · [Lean proofs](gate11-gate12-v12.3/gate12/) · [verification scope](gate11-gate12-v12.3/README.md).

This edition combines bounded model-class refutation with a universal program-specification proof for canonical two-phase stack machines, and formalized separation from DFA and one-counter machines under their stated assumptions. The historical escalation checker validates *selected witness-list prefixes*, not all oracle-call ordering. [Successful Lean 4.36.0/XeLaTeX GitHub Actions run](https://github.com/Dnarts/proof-carrying-discovery/actions/runs/45134680055).

## Previous methodological edition

[English manuscript](HYPOTHESIS_LANGUAGE.en.md) · [Русский](HYPOTHESIS_LANGUAGE.ru.md) · [简体中文 PDF](HYPOTHESIS_LANGUAGE.zh.pdf) · [中文 Markdown](HYPOTHESIS_LANGUAGE.zh.md) · [עברית PDF](HYPOTHESIS_LANGUAGE.he.pdf) · [finite Gate 5 Lean declarations](formal/gate5_invariants.lean) · [claim/provenance ledger](CLAIMS_AND_PROVENANCE.md).

This earlier paper studies semantic version spaces, exact identification windows for finite-dimensional Boolean-linear languages, distinguishing and agreement queries, and the limited Gate 5 observer case study. Its extended cellular automaton is not the original two-symbol Rule 110 transition as a complete system. Original source checks and publication dates remain attached to their own historical artifacts; Gate 12 does not silently replace them.

[Complete preprint language table](../../docs/PREPRINT_LANGUAGES.md)

## Scientific line and navigation

1. **Latest universal program certificate:** [Gate 11–12](gate11-gate12-v12.3/).
2. **What identification means:** [Earlier hypothesis-language paper EN](HYPOTHESIS_LANGUAGE.en.md) / [RU](HYPOTHESIS_LANGUAGE.ru.md).
3. **When a model-class change is justified:** [Controlled Representation Change](../../docs/FORMAL_RESULTS.en.md).
4. **Why accumulated rules may help or hurt:** [Cumulative Search v1.1](../cumulative-search/).

[Main repository README](../../README.md) · [Research lineage EN](../../docs/RESEARCH_LINEAGE.en.md) · [Русский](../../docs/RESEARCH_LINEAGE.ru.md).

**Do not merge evidence:** finite code-distance results, full CA dynamics, a formal theorem on a fixed stack-language class, and the entire adaptive-controller history are different proof obligations.
