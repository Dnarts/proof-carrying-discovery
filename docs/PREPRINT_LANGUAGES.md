# Preprints by language · Препринты по языкам · 论文语言版本

**Canonical scientific versions are tracked separately from translations.** Translating a preprint neither modifies its mathematical claims nor makes a historical finite check into a universal theorem. Read the evidence scope accompanying the relevant research edition.

| Study (newest first) | English | Русский | 简体中文 |
|---|---|---|---|
| **Recursive Switching and Modular Oracle Separations under NP = UP** · [Bundle and companion](../papers/recursive-switching-np-up/) | [PDF](../papers/recursive-switching-np-up/recursive_switching_np_up_en.pdf) · [TeX](../papers/recursive-switching-np-up/recursive_switching_np_up_en.tex) | [PDF](../papers/recursive-switching-np-up/recursive_switching_np_up_ru.pdf) · [TeX](../papers/recursive-switching-np-up/recursive_switching_np_up_ru.tex) · [Научпоп](../papers/recursive-switching-np-up/interface_barrier_popular_ru.pdf) | Not included |
| **Observe, Change Representation, or Act v2.6.1 (corrected edition)** · [Sources and evidence](../papers/certified-strategy-selection/v2.6.1/) | [PDF](../papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_en.pdf) · [TeX](../papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_en.tex) | [PDF](../papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1.pdf) · [TeX](../papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1.tex) | [PDF](../papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_zh.pdf) · [TeX](../papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_zh.tex) |
| **Goal-Relative Information Sufficiency and the Research Repair Atom v1.3** · [Sources and evidence](../papers/repair-budget-atom/v1.3/) | [PDF](../papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_en.pdf) · [TeX](../papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_en.tex) | [Original PDF](../papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3.pdf) · [TeX](../papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3.tex) | [PDF](../papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_zh.pdf) · [TeX](../papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_zh.tex) |
| **Meta-Synset and Invariant v2.5** · [Lean and evidence](../papers/hypothesis-language/meta-synset-v2.5/) | [PDF](../papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5_en.pdf) · [Source ZIP](../papers/hypothesis-language/meta-synset-v2.5/meta_synset_v2_5_english_source.zip) | [Original PDF](../papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5.pdf) | [PDF](../papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5_zh.pdf) · [Source ZIP](../papers/hypothesis-language/meta-synset-v2.5/meta_synset_v2_5_chinese_source.zip) |
| **Gate 11–12 v12.3 — Hypothesis Languages and Proof-Carrying Representation Escalation** | [PDF](../papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_en.pdf) · [TeX](../papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_en.tex) | [PDF](../papers/hypothesis-language/gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf) · [TeX](../papers/hypothesis-language/gate11-gate12-v12.3/src/hypothesis_language_gate12_ru.tex) | [PDF](../papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_zh.pdf) · [TeX](../papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_zh.tex) |
| **Hypothesis Languages — earlier evidence-scoped identification edition** | [Markdown](../papers/hypothesis-language/HYPOTHESIS_LANGUAGE.en.md) | [Markdown](../papers/hypothesis-language/HYPOTHESIS_LANGUAGE.ru.md) | [PDF](../papers/hypothesis-language/HYPOTHESIS_LANGUAGE.zh.pdf) · [Markdown](../papers/hypothesis-language/HYPOTHESIS_LANGUAGE.zh.md) |
| **Cumulative Search v1.1 — original experimental paper** | [Historical PDF](../PREPRINT_v1.1.en.pdf) · [clean Markdown](../papers/cumulative-search/CUMULATIVE_SEARCH.en.md) | [Historical PDF](../PREPRINT_v1.1.ru.pdf) · [clean Markdown](../papers/cumulative-search/CUMULATIVE_SEARCH.ru.md) | [PDF](../papers/cumulative-search/CUMULATIVE_SEARCH.zh.pdf) · [Markdown](../papers/cumulative-search/CUMULATIVE_SEARCH.zh.md) |

**Status of the editions:** Certified Strategy Selection v2.6.1 is available as a corrected edition in Russian, English, and Simplified Chinese. Meta-Synset v2.5’s English and Simplified Chinese translations accompany the original Russian PDF. Gate 11–12 has [parametric Lean statements and a full release bundle](../papers/hypothesis-language/gate11-gate12-v12.3/). The earlier methods article reflects its own earlier evidence snapshot, including a finite Gate 5 checker; it has not been silently rewritten in light of later results. Cumulative Search is a separate historical research contribution whose original v1.1 paper and results remain unchanged. The Chinese version of that paper translates its clean-reading edition rather than claiming to reproduce the byte-identical v1.1 historical PDF layout.

**Original evidence is language-neutral:** the proof objects and SHA-256 records remain at their original paths. Chinese and English PDF renderings are reading copies; an independently checked translation of the natural-language text is not claimed. For verification, consult the [Gate 11–12 evidence guide](../papers/hypothesis-language/gate11-gate12-v12.3/README.md) and [research lineage](RESEARCH_LINEAGE.en.md).

## Rebuilding PDFs

From the repository root on a system with XeLaTeX, the Noto fonts, `ctex`, and Pandoc:

```bash
cd papers/hypothesis-language/translations/gate11-gate12-v12.3
xelatex -halt-on-error -interaction=nonstopmode hypothesis_language_gate12_en.tex
xelatex -halt-on-error -interaction=nonstopmode hypothesis_language_gate12_en.tex
xelatex -halt-on-error -interaction=nonstopmode hypothesis_language_gate12_zh.tex
xelatex -halt-on-error -interaction=nonstopmode hypothesis_language_gate12_zh.tex
cd ../../../..
pandoc papers/hypothesis-language/HYPOTHESIS_LANGUAGE.zh.md --pdf-engine=xelatex \
  -H docs/zh_pdf_header.tex -V mainfont='Noto Serif' -V CJKmainfont='Noto Serif CJK SC' \
  -V sansfont='Noto Sans' -V monofont='DejaVu Sans Mono' -V geometry:margin=22mm \
  -V fontsize=11pt -o papers/hypothesis-language/HYPOTHESIS_LANGUAGE.zh.pdf
pandoc papers/cumulative-search/CUMULATIVE_SEARCH.zh.md --pdf-engine=xelatex \
  -H docs/zh_pdf_header.tex -V mainfont='Noto Serif' -V CJKmainfont='Noto Serif CJK SC' \
  -V sansfont='Noto Sans' -V monofont='DejaVu Sans Mono' -V geometry:margin=22mm \
  -V fontsize=11pt -o papers/cumulative-search/CUMULATIVE_SEARCH.zh.pdf
```

A [CI job](../.github/workflows/preprint-translations.yml) rebuilds the four translated PDFs and publishes their current byte-level hashes in [translation digest manifest](PREPRINT_TRANSLATIONS_SHA256.json). The generated PDFs may have different build-time metadata on different platforms; the source TeX/Markdown and the scientific assertions remain the canonical objects.
