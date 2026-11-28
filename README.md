# Proof-Carrying Discovery

## CRTT — Contract-Relative Transformation Theory · v1.0-rc4

**From Certified Discovery to Meta-Policy Closure**  
Aleksandr Strand · November 2026  
[strandlex@gmail.com](mailto:strandlex@gmail.com)

A Lean-verified framework for changing how a system searches while it runs. In a finite, budgeted model, a certified replacement can reduce modeled cost without changing which results the search must return.

| Materials / Материалы | English | Русский |
| --- | --- | --- |
| Preprint PDF · 20 pages / страниц | [Read PDF](papers/contract-relative-transformation/v1.0-rc4/CRTT-preprint-v1.0-rc4.pdf) | [Читать PDF](papers/contract-relative-transformation/v1.0-rc4/CRTT-preprint-v1.0-rc4-ru.pdf) |
| Single-file LaTeX / Один TEX-файл | [TEX](papers/contract-relative-transformation/v1.0-rc4/CRTT-preprint-v1.0-rc4.tex) | [TEX](papers/contract-relative-transformation/v1.0-rc4/CRTT-preprint-v1.0-rc4-ru.tex) |
| Plain-language guide / Научпоп | [HTML](papers/contract-relative-transformation/v1.0-rc4/crtt-en.html) | [HTML](papers/contract-relative-transformation/v1.0-rc4/crtt.html) |

**Formal artifact / Формальное приложение:** [Full archive · ZIP](papers/contract-relative-transformation/v1.0-rc4/CRTT-v1.0-FULL-ARCHITECTURE-RECONCILED.zip) · [SHA-256](papers/contract-relative-transformation/v1.0-rc4/CRTT-v1.0-FULL-ARCHITECTURE-RECONCILED.zip.sha256) · [Lean sources](papers/contract-relative-transformation/v1.0-rc4/formal/canonical/) · [Verification status](papers/contract-relative-transformation/v1.0-rc4/formal/VERIFICATION_RU.md).

**[Overview / Обзор](papers/contract-relative-transformation/v1.0-rc4/README.md) · [All SHA-256 checksums / Все контрольные суммы](papers/contract-relative-transformation/v1.0-rc4/SHA256SUMS.txt).**

**Fresh Lean 4.36.0 verification / Свежая проверка Lean:** PASS on Linux, with 542 audited declarations and 9 CLI/reference matches. [Run log and status / Журнал и статус](papers/contract-relative-transformation/v1.0-rc4/publication/supplement/CRTT-RC4-fresh-Linux-verification.zip).

---

**When may an autonomous system change its hypothesis language, and how can it carry an independently checkable reason?**

Evidence-scoped program discovery, finite model-class refutation, controlled representation escalation and formal verification of synthesized programs.

**English** · [Русский](#русский) · [简体中文](#中文简介)

[**All preprints: English · Русский · 简体中文 · עברית**](docs/PREPRINT_LANGUAGES.md)

## Recursive Switching and Modular Oracle Separations under NP = UP (26 November 2026)

In an oracle model, unique witnesses do not remove the gap between access in one fixed characteristic and access across characteristics.

[English PDF](papers/recursive-switching-np-up/recursive_switching_np_up_en.pdf) · [Русский PDF](papers/recursive-switching-np-up/recursive_switching_np_up_ru.pdf) · [简体中文 PDF](papers/recursive-switching-np-up/recursive_switching_np_up_zh.pdf) · [עברית PDF](papers/recursive-switching-np-up/recursive_switching_np_up_he.pdf)

**Научпоп / Plain-language companion:** [Русский PDF](papers/recursive-switching-np-up/interface_barrier_popular_ru.pdf) · [English PDF](papers/recursive-switching-np-up/interface_barrier_popular_en.pdf) · [简体中文 PDF](papers/recursive-switching-np-up/interface_barrier_popular_zh.pdf) · [עברית PDF](papers/recursive-switching-np-up/interface_barrier_popular_he.pdf)

[Full bundle (ZIP)](papers/recursive-switching-np-up/rs_bundle.zip) · [Zenodo](https://zenodo.org/records/24585707?preview=1&preview_file=recursive_switching_np_up_en.pdf) · [Lean 4 verification artifact (ZIP)](papers/recursive-switching-np-up/recursive-switching-lean4-artifact-v1.0.zip) · [Translation sources (ZIP)](papers/recursive-switching-np-up/recursive_switching_np_up_translation_sources.zip) · [Sources and checksums](papers/recursive-switching-np-up/)

**Lean 4 verification artifact**

Can eliminating ambiguity make a hard problem easy? This work shows that, in a constructed oracle model, the answer is no. The oracle is built so that every problem in NP has an unambiguous verifier, yet a single second-level problem, deciding whether a table has an empty row, remains beyond polynomial-time counting modulo any fixed prime. Even extending the field without changing its characteristic does not make the problem decidable in deterministic polynomial time. Allowing access across different prime characteristics does.

The proof develops a recursive switching method that simplifies what a machine can observe across layers of the oracle while preserving the distinction between a table with an empty row and one without. This companion artifact contains seven Lean 4.36.0 modules that formalize selected combinatorial and algebraic steps and a conditional bridge for the finite-stage argument. The construction of the infinite oracle and the full separation are proved analytically in the preprint. The result is about oracle models, not the unrelativized relationship between P and NP.

## Information-Theoretic Blind Spots of Finite Black-Box Auditing v2.0 (25 November 2026)

Information-theoretic bounds on what a finite audit profile can certify, with a separate, partially Lean-formalized oracle result.

[English PDF](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_en.pdf) · [Русский PDF](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_ru.pdf) · [简体中文 PDF](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_zh.pdf) · [עברית PDF](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_he.pdf) · [Sources and evidence ZIP](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_sources_and_evidence.zip) · [Overview and checksums](papers/blackbox-auditing/v2.0/)

## Certified Structural Discovery v4.0 (25 November 2026)

An executable search for cross-domain state correspondences and safe bypasses, with independently checked certificates and method transfer on finite benchmarks. The stochastic LLM evaluation layer is outside this release’s deterministic core.

[**English PDF**](papers/certified-structural-discovery/v4.0/preprint/certified_structural_discovery_v4_0_preprint_en.pdf) · [**Русский PDF**](papers/certified-structural-discovery/v4.0/preprint/certified_structural_discovery_v4_0_preprint_ru.pdf) · [**简体中文 PDF**](papers/certified-structural-discovery/v4.0/preprint/certified_structural_discovery_v4_0_preprint_zh.pdf) · [**עברית PDF**](papers/certified-structural-discovery/v4.0/preprint/certified_structural_discovery_v4_0_preprint_he.pdf) · [Release ZIP](papers/certified-structural-discovery/v4.0/certified_structural_discovery_v4_0_MULTILINGUAL_FINAL.zip) · [Source and verification records](papers/certified-structural-discovery/v4.0/)

**Plain-language companion: [No Way Around](papers/certified-structural-discovery/v4.0/explainer/)** · [English PDF](papers/certified-structural-discovery/v4.0/explainer/nobypassstructuraldiscoveryv4popularen.pdf) · [Русский PDF](papers/certified-structural-discovery/v4.0/explainer/nobypassstructuraldiscoveryv4popularru.pdf) · [简体中文 PDF](papers/certified-structural-discovery/v4.0/explainer/nobypassstructuraldiscoveryv4popularzh.pdf) · [עברית PDF](papers/certified-structural-discovery/v4.0/explainer/nobypassstructuraldiscoveryv4popularhe.pdf)

To run the supplied Python suite from the release directory: `python3 python/test_v4_0.py`.

## Epistemic Deformation of Reachability v3.2 (25 November 2026)

A finite deterministic model in which a diagnostic probe can reveal the hidden state while irreversibly closing the path to the goal. Includes an unbounded-horizon impossibility result, a belief-space characterization, and a negative value-of-information example.

[**English PDF**](papers/epistemic-deformation-reachability/v3.2/epistemic_deformation_reachability_v3_2_preprint_en.pdf) · [**Русский PDF**](papers/epistemic-deformation-reachability/v3.2/epistemic_deformation_reachability_v3_2_preprint_ru.pdf) · [Release ZIP](papers/epistemic-deformation-reachability/v3.2/epistemic_deformation_reachability_v3_2_BILINGUAL_FINAL.zip) · [Source and verification records](papers/epistemic-deformation-reachability/v3.2/)

## Observe, Change Representation, or Act (v2.6.1, corrected edition, 24 November 2026)

Certified strategy selection under memory, budget, and time constraints. The release distinguishes when to probe, change representation or observation port, or act before a causal deadline.

[**English PDF**](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_en.pdf) · [**Русский PDF**](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1.pdf) · [**简体中文 PDF**](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_zh.pdf) · [עברית PDF](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_he.pdf) · [Source, Lean, Python and verification records](papers/certified-strategy-selection/v2.6.1/) · [Corrected release ZIP](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_v2_6_1_FINAL_RELEASE.zip)

## Goal-Relative Information Sufficiency and the Research Repair Atom v1.3 (24 November 2026)

A finite worst-case model of when observations suffice to guarantee an action within a hard budget, without identifying the world. The release includes a scalar Lean kernel and a bounded local cellular-automaton benchmark.

[**English PDF**](papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_en.pdf) · [**Русский PDF**](papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3.pdf) · [**简体中文 PDF**](papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_zh.pdf) · [עברית PDF](papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_he.pdf) · [Source, code and verification records](papers/repair-budget-atom/v1.3/)

## Meta-Synset and Invariant v2.5 (23 November 2026)

**A Typed System for Revising Research Representations.** Cross-domain transfer is proposed as a heuristic; Lean verifies the typed checking protocol under stated assumptions.

[**English PDF**](papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5_en.pdf) · [**Русский PDF**](papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5.pdf) · [**简体中文 PDF**](papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5_zh.pdf) · [עברית PDF](papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5_he.pdf) · [English source ZIP](papers/hypothesis-language/meta-synset-v2.5/meta_synset_v2_5_english_source.zip) · [Lean sources and verification logs](papers/hypothesis-language/meta-synset-v2.5/evidence/)

## Gate 11–12 (23 November 2026)

**Hypothesis Languages and Proof-Carrying Representation Escalation.** Previous paper in the hypothesis-language series.

**Preprint PDFs:** [English](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_en.pdf) · [Русский](papers/hypothesis-language/gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf) · [简体中文](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_zh.pdf) · [עברית PDF](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_he.pdf)

[Original Russian LaTeX](papers/hypothesis-language/gate11-gate12-v12.3/src/hypothesis_language_gate12_ru.tex) · [reproducible ZIP](papers/hypothesis-language/gate11-gate12-v12.3/gate12_reproducible_bundle.zip) · [Lean sources](papers/hypothesis-language/gate11-gate12-v12.3/gate12/) · [evidence and limits](papers/hypothesis-language/gate11-gate12-v12.3/README.md)

[Successful Lean 4.36.0 + XeLaTeX publication workflow](https://github.com/Dnarts/proof-carrying-discovery/actions/runs/45134680055).

The main progression is:

**Acquire a useful program → test whether it is identified → refute an inadequate model class → change representation → synthesize a new program → formally check its behavior.**

The full translated PDFs preserve the proof scopes and mathematical claims of the original Russian version. For earlier publications, English was already available; [Chinese translations now accompany both earlier papers](docs/PREPRINT_LANGUAGES.md).

The Gate 11–12 result distinguishes four different forms of evidence. A finite prefix–suffix witness rules out DFA models with **at most a specified number of states**. A separate mathematical theorem can rule out all finite DFAs for a **formally defined** nonregular language. An exported canonical two-phase stack program is proved to recognize its stated infinite-word language; under explicit binary-distinguishing assumptions, the formalization rules out every finite-control DFA and one-counter machine in the declared Lean models. A selected-history checker validates recorded witness prefixes but **not the chronological order of all actual Python oracle calls**.

This is not a proof that a finite unknown-oracle transcript establishes nonregularity, that all pushdown automata have been verified, or that the controller can invent arbitrary new architectures.

## Research lineage

| Stage | Scientific question | Research artifact |
|---|---|---|
| **1 — Cumulative discovery (v1.1)** | When do acquired macros, inferred invariants, and transfer actually reduce total work once acquisition and audit costs are counted? | [Original EN PDF](PREPRINT_v1.1.en.pdf) · [RU PDF](PREPRINT_v1.1.ru.pdf) · [עברית PDF](papers/cumulative-search/CUMULATIVE_SEARCH.he.pdf) · [clean editions](papers/cumulative-search/) · [code/results](v1_1/) |
| **2 — Controlled representation change (Lean)** | When is escalation justified by a sound impossibility witness, and what does it cost? | [Formal results EN](docs/FORMAL_RESULTS.en.md) · [RU](docs/FORMAL_RESULTS.ru.md) · [Lean](formal/) |
| **3 — Model-relative identification (Gate 4B–5)** | How do language-relative uniqueness, discriminating/falsifying queries, channel checks, and origin uncertainty differ? | [Methods paper EN](papers/hypothesis-language/HYPOTHESIS_LANGUAGE.en.md) · [עברית PDF](papers/hypothesis-language/HYPOTHESIS_LANGUAGE.he.pdf) · [RU](papers/hypothesis-language/HYPOTHESIS_LANGUAGE.ru.md) · [finite Lean source](papers/hypothesis-language/formal/) |
| **4 — Proof-carrying escalation (Gate 11–12)** | Can the old bounded class be refuted and the generated replacement proved for **all words** in a declared formal family? | [Gate 11–12 preprint](papers/hypothesis-language/gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf) · [verified source bundle](papers/hypothesis-language/gate11-gate12-v12.3/) |

Gate 6–10 explored representation changes and competing operators in finite settings; **complete independently replicated packages for every intermediate Gate are not all present in this repository**. Their research history is not silently promoted to the status of the Gate 11–12 Lean theorems.

### What the evidence does and does not establish

- **Finite rejection versus universal rejection:** excluding DFA(≤k) from finite observations is not the same as ruling out all DFA for an unknown target. Universal theorems here refer to mathematically specified languages.
- **Program correctness versus generator correctness:** Lean checks the submitted machine and its parametric proof premises; it does not automatically prove Python-to-Lean compiler equivalence or unrestricted synthesis correctness.
- **A recorded trace versus causal history:** the published Gate 12 run has 88/107 oracle calls and only 60/61 selected records for its two tasks. Prefix ordering within that retained list is proved, but no-lookahead for the complete controller is not.
- **A finite observer versus physical origin:** Gate 5 uses an augmented radius-one cellular automaton with a Rule 110 base layer. Observation-class identification does not certify the complete unknown initial state.
- **Cost is model-specific:** improvements in search branches or audit work depend on the declared task family, grammar and resource accounting.

## Reproduce and find sources

**Latest Gate 12:** [instructions and release manifest](papers/hypothesis-language/gate11-gate12-v12.3/README.md), [Python controller](papers/hypothesis-language/gate11-gate12-v12.3/gate12/gate12_blind_chomsky_escalation.py), [Lean hierarchy checker](papers/hypothesis-language/gate11-gate12-v12.3/gate12/gate12_hierarchy_checker.lean), [exported Lean programs](papers/hypothesis-language/gate11-gate12-v12.3/gate12/gate12_exported_pal_mid.lean), [independent audit](papers/hypothesis-language/gate11-gate12-v12.3/verification/GATE12_REVIEW_RU.md).

**Original v1.1 Python experiment:** from the repository root run:

~~~bash
python3 tests/audit_release.py
~~~

The root [MANIFEST.json](MANIFEST.json) and [SHA256SUMS.txt](SHA256SUMS.txt) index the original **v1.1.1 release**, not every later paper. The Gate 12 publication has [its own digest manifest](papers/hypothesis-language/gate11-gate12-v12.3/RELEASE_SHA256.json). Historical originals remain under [v1_1/](v1_1/), [legacy/](legacy/), and [history/](history/).

[Full research lineage and claim boundaries](docs/RESEARCH_LINEAGE.en.md) · [русская карта исследования](docs/RESEARCH_LINEAGE.ru.md).

**Related, separate research:** [Rule 110 Dependency Fronts](https://github.com/Dnarts/rule110-dependency-fronts) · [Channel Topology and Memory](https://github.com/Dnarts/channel-topology-and-memory). Their proofs should not be attributed to this repository's results without an explicit bridge.

## Citation

Cite the **specific preprint and source commit** supporting each claim: [Meta-Synset v2.5](papers/hypothesis-language/meta-synset-v2.5/), [Gate 11–12](papers/hypothesis-language/gate11-gate12-v12.3/), [v1.1](PREPRINT_v1.1.en.pdf), or the [abstract formal supplement](docs/FORMAL_RESULTS.en.md). [Citation metadata](CITATION.cff) · [MIT license](LICENSE). No DOI or peer review is claimed for the latest paper.

---

# Русский

**При каких условиях система вправе изменить язык поиска и как независимо проверить основания этого перехода?**

Основная линия: **найти программу → проверить идентифицируемость → опровергнуть недостаточный класс → сменить представление → синтезировать решение → формально проверить его поведение.**

## «Рекурсивные switching-леммы и модульные оракульные разделения при NP = UP»

Оракульное разделение между доступом в фиксированной характеристике и доступом с её сменой при единственности свидетелей. Это не утверждение о нерелятивизированном NP = UP.

[English PDF](papers/recursive-switching-np-up/recursive_switching_np_up_en.pdf) · [Русский PDF](papers/recursive-switching-np-up/recursive_switching_np_up_ru.pdf) · [简体中文 PDF](papers/recursive-switching-np-up/recursive_switching_np_up_zh.pdf) · [עברית PDF](papers/recursive-switching-np-up/recursive_switching_np_up_he.pdf)

**Научпоп / Plain-language companion:** [Русский PDF](papers/recursive-switching-np-up/interface_barrier_popular_ru.pdf) · [English PDF](papers/recursive-switching-np-up/interface_barrier_popular_en.pdf) · [简体中文 PDF](papers/recursive-switching-np-up/interface_barrier_popular_zh.pdf) · [עברית PDF](papers/recursive-switching-np-up/interface_barrier_popular_he.pdf)

[Full bundle (ZIP)](papers/recursive-switching-np-up/rs_bundle.zip) · [Zenodo](https://zenodo.org/records/24585707?preview=1&preview_file=recursive_switching_np_up_en.pdf) · [Lean 4 verification artifact (ZIP)](papers/recursive-switching-np-up/recursive-switching-lean4-artifact-v1.0.zip) · [Translation sources (ZIP)](papers/recursive-switching-np-up/recursive_switching_np_up_translation_sources.zip) · [Sources and checksums](papers/recursive-switching-np-up/)

## «Информационно-теоретические слепые зоны конечного black-box аудита» v2.0

Что конечный набор тестов может и не может удостоверить по своему профилю ответов.

[English PDF](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_en.pdf) · [Русский PDF](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_ru.pdf) · [简体中文 PDF](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_zh.pdf) · [עברית PDF](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_he.pdf) · [Sources and evidence ZIP](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_sources_and_evidence.zip)

## Certified Structural Discovery v4.0

Поиск соответствий между моделями, проверка сертификатов и перенос методов на конечных тестах. [**English PDF**](papers/certified-structural-discovery/v4.0/preprint/certified_structural_discovery_v4_0_preprint_en.pdf) · [**Русский PDF**](papers/certified-structural-discovery/v4.0/preprint/certified_structural_discovery_v4_0_preprint_ru.pdf) · [**简体中文 PDF**](papers/certified-structural-discovery/v4.0/preprint/certified_structural_discovery_v4_0_preprint_zh.pdf) · [**עברית PDF**](papers/certified-structural-discovery/v4.0/preprint/certified_structural_discovery_v4_0_preprint_he.pdf) · [Release ZIP](papers/certified-structural-discovery/v4.0/certified_structural_discovery_v4_0_MULTILINGUAL_FINAL.zip) · [Source and verification records](papers/certified-structural-discovery/v4.0/)

Популярный разбор: [«Обхода нет»](papers/certified-structural-discovery/v4.0/explainer/) · [English PDF](papers/certified-structural-discovery/v4.0/explainer/nobypassstructuraldiscoveryv4popularen.pdf) · [Русский PDF](papers/certified-structural-discovery/v4.0/explainer/nobypassstructuraldiscoveryv4popularru.pdf) · [简体中文 PDF](papers/certified-structural-discovery/v4.0/explainer/nobypassstructuraldiscoveryv4popularzh.pdf) · [עברית PDF](papers/certified-structural-discovery/v4.0/explainer/nobypassstructuraldiscoveryv4popularhe.pdf)

## «Эпистемическая деформация достижимости» v3.2

Когда диагностический зонд раскрывает скрытое состояние, но необратимо закрывает путь к цели. [**English PDF**](papers/epistemic-deformation-reachability/v3.2/epistemic_deformation_reachability_v3_2_preprint_en.pdf) · [**Русский PDF**](papers/epistemic-deformation-reachability/v3.2/epistemic_deformation_reachability_v3_2_preprint_ru.pdf) · [Release ZIP](papers/epistemic-deformation-reachability/v3.2/epistemic_deformation_reachability_v3_2_BILINGUAL_FINAL.zip) · [Source and verification records](papers/epistemic-deformation-reachability/v3.2/)

## «Наблюдать, менять представление или действовать» v2.6.1 (исправленная редакция)

[**Русский PDF**](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1.pdf) · [English PDF](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_en.pdf) · [简体中文 PDF](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_zh.pdf) · [עברית PDF](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_he.pdf) · [Исходники, Lean, Python и журнал проверки](papers/certified-strategy-selection/v2.6.1/) · [Исправленный ZIP](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_v2_6_1_FINAL_RELEASE.zip)

## «Целевая достаточность информации и атом исследовательского ремонта» v1.3

[**Оригинал PDF**](papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3.pdf) · [English PDF](papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_en.pdf) · [简体中文 PDF](papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_zh.pdf) · [עברית PDF](papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_he.pdf) · [Исходники, код и журналы проверки](papers/repair-budget-atom/v1.3/)

## «Мета-синсет и инвариант» v2.5

[Оригинал PDF](papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5.pdf) · [Английский PDF](papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5_en.pdf) · [Китайский PDF](papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5_zh.pdf) · [עברית PDF](papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5_he.pdf) · [Lean и журналы проверки](papers/hypothesis-language/meta-synset-v2.5/evidence/)

## Gate 11–12

**«Языки гипотез и доказательная эскалация представления»**, 10 страниц на русском.

**Препринт:** [English PDF](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_en.pdf) · [Русский PDF](papers/hypothesis-language/gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf) · [中文 PDF](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_zh.pdf) · [עברית PDF](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_he.pdf)

[Русский LaTeX](papers/hypothesis-language/gate11-gate12-v12.3/src/hypothesis_language_gate12_ru.tex) · [Бандл ZIP](papers/hypothesis-language/gate11-gate12-v12.3/gate12_reproducible_bundle.zip) · [Lean](papers/hypothesis-language/gate11-gate12-v12.3/gate12/) · [Границы и аудит](papers/hypothesis-language/gate11-gate12-v12.3/README.md).

Теперь речь не только о конечном исключении DFA(≤k). Для **формально заданных** языков и канонических двухфазных стековых программ доказаны универсальные утверждения на всех конечных словах. В допустимом семействе с различающим биты преобразованием исключены DFA и односчётчиковые автоматы с произвольным конечным числом управляющих состояний. Но **для произвольного чёрного ящика такого вывода из конечной выборки нет**.

Контроллер проверяет выбранные исторические префиксы свидетельств. Полный порядок всех запросов Python-оракулу не сертифицирован; универсальная проверка экспортированного автомата не равнозначна проверке всей процедуры его получения.

[Проверка Lean 4.36.0 в GitHub Actions — SUCCESS](https://github.com/Dnarts/proof-carrying-discovery/actions/runs/45134680055).

## Научная последовательность

| Этап | Что установлено | Ссылки |
|---|---|---|
| **v1.1 — накопительное открытие** | NAND/XOR, стоимость приобретения макросов и законов, условия переноса | [EN PDF](PREPRINT_v1.1.en.pdf) · [RU PDF](PREPRINT_v1.1.ru.pdf) · [עברית PDF](papers/cumulative-search/CUMULATIVE_SEARCH.he.pdf) · [код](v1_1/) |
| **Формальная смена представления** | Условная безопасность эскалации, разделение заданных DFA/1-DCA | [Теоремы Lean](docs/FORMAL_RESULTS.ru.md) |
| **Gate 4B–5 — язык и свидетельства** | Семантическая единственность, фальсификация языка, контроль наблюдений | [RU](papers/hypothesis-language/HYPOTHESIS_LANGUAGE.ru.md) · [EN](papers/hypothesis-language/HYPOTHESIS_LANGUAGE.en.md) · [עברית PDF](papers/hypothesis-language/HYPOTHESIS_LANGUAGE.he.pdf) |
| **Gate 11–12 — доказательная эскалация** | Недостаточность ограниченного класса + универсальный сертификат найденной программы | [Препринт](papers/hypothesis-language/gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf) · [ZIP](papers/hypothesis-language/gate11-gate12-v12.3/gate12_reproducible_bundle.zip) |

Эксперименты Gate 6–10 связывают эти этапы, но не все имеют самостоятельные независимо перепроверенные пакеты в текущем репозитории. Их статус нельзя отождествлять с доказанными в Lean утверждениями Gate 11–12.

## Структура репозитория

Для чтения начать с [основного препринта](papers/hypothesis-language/gate11-gate12-v12.3/), затем перейти к [предыдущей методологической редакции](papers/hypothesis-language/), [формальным основаниям](formal/) и [исходному эксперименту v1.1](papers/cumulative-search/). Развёрнутая [карта исследования](docs/RESEARCH_LINEAGE.ru.md) объясняет область каждого свидетельства.

[MANIFEST.json](MANIFEST.json) относится только к историческому выпуску v1.1.1; у новых работ собственные хэши. [Как цитировать](CITATION.cff) · [MIT](LICENSE). Связанные, но отдельные направления: [Rule 110](https://github.com/Dnarts/rule110-dependency-fronts) и [Channel Topology and Memory](https://github.com/Dnarts/channel-topology-and-memory).


---

# 中文简介

**递归转换与 NP = UP 条件下的模计数预言机分离** · [English PDF](papers/recursive-switching-np-up/recursive_switching_np_up_en.pdf) · [Русский PDF](papers/recursive-switching-np-up/recursive_switching_np_up_ru.pdf) · [简体中文 PDF](papers/recursive-switching-np-up/recursive_switching_np_up_zh.pdf) · [עברית PDF](papers/recursive-switching-np-up/recursive_switching_np_up_he.pdf)

**Научпоп / Plain-language companion:** [Русский PDF](papers/recursive-switching-np-up/interface_barrier_popular_ru.pdf) · [English PDF](papers/recursive-switching-np-up/interface_barrier_popular_en.pdf) · [简体中文 PDF](papers/recursive-switching-np-up/interface_barrier_popular_zh.pdf) · [עברית PDF](papers/recursive-switching-np-up/interface_barrier_popular_he.pdf)

[Full bundle (ZIP)](papers/recursive-switching-np-up/rs_bundle.zip) · [Zenodo](https://zenodo.org/records/24585707?preview=1&preview_file=recursive_switching_np_up_en.pdf) · [Lean 4 verification artifact (ZIP)](papers/recursive-switching-np-up/recursive-switching-lean4-artifact-v1.0.zip) · [Translation sources (ZIP)](papers/recursive-switching-np-up/recursive_switching_np_up_translation_sources.zip) · [Sources and checksums](papers/recursive-switching-np-up/)

**有限黑箱审计的信息论盲区 v2.0** · [English PDF](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_en.pdf) · [Русский PDF](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_ru.pdf) · [简体中文 PDF](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_zh.pdf) · [עברית PDF](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_he.pdf) · [Sources and evidence ZIP](papers/blackbox-auditing/v2.0/blackbox_auditing_v2_sources_and_evidence.zip)

**本项目的核心问题：何时有证据支持改变假设语言，如何独立核验这种改变？**

最新预印本：Certified Structural Discovery v4.0（[**English PDF**](papers/certified-structural-discovery/v4.0/preprint/certified_structural_discovery_v4_0_preprint_en.pdf) · [**Русский PDF**](papers/certified-structural-discovery/v4.0/preprint/certified_structural_discovery_v4_0_preprint_ru.pdf) · [**简体中文 PDF**](papers/certified-structural-discovery/v4.0/preprint/certified_structural_discovery_v4_0_preprint_zh.pdf) · [**עברית PDF**](papers/certified-structural-discovery/v4.0/preprint/certified_structural_discovery_v4_0_preprint_he.pdf) · [Release ZIP](papers/certified-structural-discovery/v4.0/certified_structural_discovery_v4_0_MULTILINGUAL_FINAL.zip) · [Source and verification records](papers/certified-structural-discovery/v4.0/)）。

《可达性的认知形变》v3.2（[English PDF](papers/epistemic-deformation-reachability/v3.2/epistemic_deformation_reachability_v3_2_preprint_en.pdf) · [俄文 PDF](papers/epistemic-deformation-reachability/v3.2/epistemic_deformation_reachability_v3_2_preprint_ru.pdf)）。

观察、改变表征，还是行动（v2.6.1 修订版）。[简体中文 PDF](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_zh.pdf) · [עברית PDF](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_he.pdf) · [English PDF](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1_en.pdf) · [俄文 PDF](papers/certified-strategy-selection/v2.6.1/certified_strategy_selection_preprint_v2_6_1.pdf) · [源代码与验证记录](papers/certified-strategy-selection/v2.6.1/)。

目标相关的信息充分性与研究修复原子 v1.3。[简体中文 PDF](papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_zh.pdf) · [עברית PDF](papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_he.pdf) · [English PDF](papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3_en.pdf) · [俄文 PDF](papers/repair-budget-atom/v1.3/repair_budget_atom_preprint_v1_3.pdf) · [源代码与验证记录](papers/repair-budget-atom/v1.3/)。

《元同义词集与不变量：研究表征的类型化修订系统》v2.5。[简体中文 PDF](papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5_zh.pdf) · [עברית PDF](papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5_he.pdf) · [中文源文件 ZIP](papers/hypothesis-language/meta-synset-v2.5/meta_synset_v2_5_chinese_source.zip) · [English PDF](papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5_en.pdf) · [Русский PDF](papers/hypothesis-language/meta-synset-v2.5/meta_synset_invariant_preprint_v2_5.pdf)。

Gate 11–12 v12.3：《假设语言与携证表征升级》。[English PDF](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_en.pdf) · [Русский PDF](papers/hypothesis-language/gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf) · [中文 PDF](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_zh.pdf) · [עברית PDF](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_he.pdf) · [源代码与证据](papers/hypothesis-language/gate11-gate12-v12.3/)。

完整研究链条：**累积程序发现 → 语义可识别性检验 → 对有界模型类的有限反证 → 表征升级 → 新程序合成 → 在已声明形式模型中验证其全称规格**。有限观测不能证明任意未知黑箱语言的非正则性；Gate 12 的参数化定理只涵盖满足规范结构条件的两阶段栈程序。历史因果检查针对选定的证据列表，而非全部真实预言机调用。

另外两篇论文：[假设语言与限定证据范围的识别（中文 PDF）](papers/hypothesis-language/HYPOTHESIS_LANGUAGE.zh.pdf) · [固定引擎中的累积搜索（中文 PDF）](papers/cumulative-search/CUMULATIVE_SEARCH.zh.pdf)。[全部预印本的语言版本索引](docs/PREPRINT_LANGUAGES.md)。
