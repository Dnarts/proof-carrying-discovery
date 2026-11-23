# Meta-Synset and Invariant · v2.4

**Aleksandr Strand · 23 November 2026 · preprint**

A typed revision system for research representations: heuristic cross-domain expansion is separated from scoped verification by `Freeze`. The paper formalizes the distinction between changing the memory class after refutation and refining the observation port under a certified non-identifiability obstruction.

| Edition | XeLaTeX source | PDF |
|---|---|---|
| English | [Source](src/meta_synset_invariant_preprint_v2_4_en.tex) | [PDF](meta_synset_invariant_preprint_v2_4_en.pdf) |
| Русский | [Исходник сборки](src/meta_synset_invariant_preprint_v2_4_ru.tex) | [PDF](meta_synset_invariant_preprint_v2_4_ru.pdf) |
| 简体中文 | [LaTeX 源文件](src/meta_synset_invariant_preprint_v2_4_zh.tex) | [PDF](meta_synset_invariant_preprint_v2_4_zh.pdf) |

## Evidence and scope

The supplied [verification log](evidence/ALL_4_MODULES_v2_4_VERIFICATION.log) records a Lean 4.36.0 run and SHA-256 for the four unmodified [Lean modules](evidence/). The 44 audited declarations comprise 15 in the kernel, 10 in Gate 14, 8 in Gate 15 and 11 in Gate 16. Of these, 23 use no axioms. The earlier [Gate 11–12 v12.3](../gate11-gate12-v12.3/) has separate evidence and should be cited separately.

- A gap says what the current witness leaves uncovered; it is not a counterexample by itself. The pointwise obstruction to total justification requires the stated premises and an incompatible point in the requested region.
- Gate 14 distinguishes a public-port gauge equivalence from absence of a model in a fixed hypothesis class. The two-axis router remains conditional; it does not diagnose both causes from a finite transcript.
- Gate 15's control-mask check is local. The two confounding examples are distinct: one gives misleading order dependence, the other an apparent one-step semantic shift despite commuting interventions. Gate 16 covers a fixed pair of independent e-variables; it is not an arbitrary adaptive stopping theorem.
- Gate 13's general queue/stack separation and empirical claims about total search cost remain open in this edition.

English and Simplified Chinese are translations of the supplied Russian v2.4 PDF. The Russian release build reproduces the v2.4 text with redrawn diagrams and harmonized version/count labels and prose aligned with the checked hypotheses and counterexamples in §§4 and 7–8; its PDF is not required to be byte-identical to the author's supplied PDF. Those editorial changes do not change the Lean sources or theorem scopes.

## Reproduce

Use XeLaTeX, Noto Serif, Noto Sans, Noto Mono, and CTeX/Fandol. Run XeLaTeX twice per source from `src/`. From `evidence/`, use Lean 4.36.0 and `bash run_all_v2_4_verification.sh` (this rewrites the local log). The release archive includes separate source and PDF digests.
