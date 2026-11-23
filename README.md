# Proof-Carrying Discovery

**When may an autonomous system change its hypothesis language, and how can it carry an independently checkable reason?**

Evidence-scoped program discovery, finite model-class refutation, controlled representation escalation and formal verification of synthesized programs.

**English** · [Русский](#русский) · [简体中文](#中文简介)

[**All preprints in EN / RU / 简体中文**](docs/PREPRINT_LANGUAGES.md)

## New preprint — Meta-Synset and Invariant v2.4

**A Typed Revision System for Research Representations.** A companion to Gate 11–12, with pointwise evidence coverage and a second escalation axis for observation ports, interventions, and stochastic gaps. The 44 audited Lean declarations do not establish an unconditional router or a search-cost advantage.

[EN PDF](papers/hypothesis-language/meta-synset-v2.4/meta_synset_invariant_preprint_v2_4_en.pdf) · [RU PDF](papers/hypothesis-language/meta-synset-v2.4/original/meta_synset_invariant_preprint_v2_4.pdf) · [简体中文 PDF](papers/hypothesis-language/meta-synset-v2.4/meta_synset_invariant_preprint_v2_4_zh.pdf) · [Lean & bundle](papers/hypothesis-language/meta-synset-v2.4/)

## Start here for the Gate 11–12 line (23 November 2026)

**Hypothesis Languages and Proof-Carrying Representation Escalation.** Foundational preprint for the language-escalation line; available in all three languages.

**Preprint PDFs:** [English](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_en.pdf) · [Русский](papers/hypothesis-language/gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf) · [简体中文](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_zh.pdf)

[Original Russian LaTeX](papers/hypothesis-language/gate11-gate12-v12.3/src/hypothesis_language_gate12_ru.tex) · [reproducible ZIP](papers/hypothesis-language/gate11-gate12-v12.3/gate12_reproducible_bundle.zip) · [Lean sources](papers/hypothesis-language/gate11-gate12-v12.3/gate12/) · [evidence and limits](papers/hypothesis-language/gate11-gate12-v12.3/README.md)

[Successful Lean 4.36.0 + XeLaTeX publication workflow](https://github.com/Dnarts/proof-carrying-discovery/actions/runs/45134680055).

The main progression is:

**Acquire a useful program → test whether it is identified → refute an inadequate model class → change representation → synthesize a new program → formally check its behavior.**

The full translated PDFs preserve the proof scopes and mathematical claims of the original Russian version. For earlier publications, English was already available; [Chinese translations now accompany both earlier papers](docs/PREPRINT_LANGUAGES.md).

The latest result distinguishes four different forms of evidence. A finite prefix–suffix witness rules out DFA models with **at most a specified number of states**. A separate mathematical theorem can rule out all finite DFAs for a **formally defined** nonregular language. An exported canonical two-phase stack program is proved to recognize its stated infinite-word language; under explicit binary-distinguishing assumptions, the formalization rules out every finite-control DFA and one-counter machine in the declared Lean models. A selected-history checker validates recorded witness prefixes but **not the chronological order of all actual Python oracle calls**.

This is not a proof that a finite unknown-oracle transcript establishes nonregularity, that all pushdown automata have been verified, or that the controller can invent arbitrary new architectures.

## Research lineage

| Stage | Scientific question | Research artifact |
|---|---|---|
| **1 — Cumulative discovery (v1.1)** | When do acquired macros, inferred invariants, and transfer actually reduce total work once acquisition and audit costs are counted? | [Original EN PDF](PREPRINT_v1.1.en.pdf) · [RU PDF](PREPRINT_v1.1.ru.pdf) · [clean editions](papers/cumulative-search/) · [code/results](v1_1/) |
| **2 — Controlled representation change (Lean)** | When is escalation justified by a sound impossibility witness, and what does it cost? | [Formal results EN](docs/FORMAL_RESULTS.en.md) · [RU](docs/FORMAL_RESULTS.ru.md) · [Lean](formal/) |
| **3 — Model-relative identification (Gate 4B–5)** | How do language-relative uniqueness, discriminating/falsifying queries, channel checks, and origin uncertainty differ? | [Methods paper EN](papers/hypothesis-language/HYPOTHESIS_LANGUAGE.en.md) · [RU](papers/hypothesis-language/HYPOTHESIS_LANGUAGE.ru.md) · [finite Lean source](papers/hypothesis-language/formal/) |
| **4 — Proof-carrying escalation (Gate 11–12)** | Can the old bounded class be refuted and the generated replacement proved for **all words** in a declared formal family? | [Latest preprint](papers/hypothesis-language/gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf) · [verified source bundle](papers/hypothesis-language/gate11-gate12-v12.3/) |

Gate 6–10 explored representation changes and competing operators in finite settings; **complete independently replicated packages for every intermediate Gate are not all present in this repository**. Their research history is not silently promoted to the status of the latest Lean theorems.

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

Cite the **specific preprint and source commit** supporting each claim: [Gate 11–12](papers/hypothesis-language/gate11-gate12-v12.3/), [v1.1](PREPRINT_v1.1.en.pdf), or the [abstract formal supplement](docs/FORMAL_RESULTS.en.md). [Citation metadata](CITATION.cff) · [MIT license](LICENSE). No DOI or peer review is claimed for the latest paper.

---

# Русский

**При каких условиях система вправе изменить язык поиска и как независимо проверить основания этого перехода?**

Основная линия: **найти программу → проверить идентифицируемость → опровергнуть недостаточный класс → сменить представление → синтезировать решение → формально проверить его поведение.**

## Новый препринт: «Мета-синсет и инвариант» v2.4

Типизированная ревизия исследовательских представлений: где менять класс гипотез, а где нужен другой канал наблюдения. [EN PDF](papers/hypothesis-language/meta-synset-v2.4/meta_synset_invariant_preprint_v2_4_en.pdf) · [RU PDF](papers/hypothesis-language/meta-synset-v2.4/original/meta_synset_invariant_preprint_v2_4.pdf) · [简体中文 PDF](papers/hypothesis-language/meta-synset-v2.4/meta_synset_invariant_preprint_v2_4_zh.pdf) · [Lean & bundle](papers/hypothesis-language/meta-synset-v2.4/).

## Основная работа по эскалации представлений — Gate 11–12

**«Языки гипотез и доказательная эскалация представления»**, 10 страниц на русском.

**Препринт:** [English PDF](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_en.pdf) · [Русский PDF](papers/hypothesis-language/gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf) · [中文 PDF](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_zh.pdf)

[Русский LaTeX](papers/hypothesis-language/gate11-gate12-v12.3/src/hypothesis_language_gate12_ru.tex) · [Бандл ZIP](papers/hypothesis-language/gate11-gate12-v12.3/gate12_reproducible_bundle.zip) · [Lean](papers/hypothesis-language/gate11-gate12-v12.3/gate12/) · [Границы и аудит](papers/hypothesis-language/gate11-gate12-v12.3/README.md).

Теперь речь не только о конечном исключении DFA(≤k). Для **формально заданных** языков и канонических двухфазных стековых программ доказаны универсальные утверждения на всех конечных словах. В допустимом семействе с различающим биты преобразованием исключены DFA и односчётчиковые автоматы с произвольным конечным числом управляющих состояний. Но **для произвольного чёрного ящика такого вывода из конечной выборки нет**.

Контроллер проверяет выбранные исторические префиксы свидетельств. Полный порядок всех запросов Python-оракулу не сертифицирован; универсальная проверка экспортированного автомата не равнозначна проверке всей процедуры его получения.

[Проверка Lean 4.36.0 в GitHub Actions — SUCCESS](https://github.com/Dnarts/proof-carrying-discovery/actions/runs/45134680055).

## Научная последовательность

| Этап | Что установлено | Ссылки |
|---|---|---|
| **v1.1 — накопительное открытие** | NAND/XOR, стоимость приобретения макросов и законов, условия переноса | [EN PDF](PREPRINT_v1.1.en.pdf) · [RU PDF](PREPRINT_v1.1.ru.pdf) · [код](v1_1/) |
| **Формальная смена представления** | Условная безопасность эскалации, разделение заданных DFA/1-DCA | [Теоремы Lean](docs/FORMAL_RESULTS.ru.md) |
| **Gate 4B–5 — язык и свидетельства** | Семантическая единственность, фальсификация языка, контроль наблюдений | [RU](papers/hypothesis-language/HYPOTHESIS_LANGUAGE.ru.md) · [EN](papers/hypothesis-language/HYPOTHESIS_LANGUAGE.en.md) |
| **Gate 11–12 — доказательная эскалация** | Недостаточность ограниченного класса + универсальный сертификат найденной программы | [Препринт](papers/hypothesis-language/gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf) · [ZIP](papers/hypothesis-language/gate11-gate12-v12.3/gate12_reproducible_bundle.zip) |

Эксперименты Gate 6–10 связывают эти этапы, но не все имеют самостоятельные независимо перепроверенные пакеты в текущем репозитории. Их статус нельзя отождествлять с доказанными в Lean утверждениями Gate 11–12.

## Структура репозитория

Для чтения начать с [основного препринта](papers/hypothesis-language/gate11-gate12-v12.3/), затем перейти к [предыдущей методологической редакции](papers/hypothesis-language/), [формальным основаниям](formal/) и [исходному эксперименту v1.1](papers/cumulative-search/). Развёрнутая [карта исследования](docs/RESEARCH_LINEAGE.ru.md) объясняет область каждого свидетельства.

[MANIFEST.json](MANIFEST.json) относится только к историческому выпуску v1.1.1; у новых работ собственные хэши. [Как цитировать](CITATION.cff) · [MIT](LICENSE). Связанные, но отдельные направления: [Rule 110](https://github.com/Dnarts/rule110-dependency-fronts) и [Channel Topology and Memory](https://github.com/Dnarts/channel-topology-and-memory).


---

# 中文简介

**本项目的核心问题：何时有证据支持改变假设语言，如何独立核验这种改变？**

新预印本：《元同义词集与不变量》v2.4。区分假设类别升级与观测端口升级。[EN PDF](papers/hypothesis-language/meta-synset-v2.4/meta_synset_invariant_preprint_v2_4_en.pdf) · [RU PDF](papers/hypothesis-language/meta-synset-v2.4/original/meta_synset_invariant_preprint_v2_4.pdf) · [简体中文 PDF](papers/hypothesis-language/meta-synset-v2.4/meta_synset_invariant_preprint_v2_4_zh.pdf) · [Lean & bundle](papers/hypothesis-language/meta-synset-v2.4/)。

Gate 11–12 v12.3 的表征升级论文：《假设语言与携证表征升级》。[English PDF](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_en.pdf) · [Русский PDF](papers/hypothesis-language/gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf) · [中文 PDF](papers/hypothesis-language/translations/gate11-gate12-v12.3/hypothesis_language_gate12_zh.pdf) · [源代码与证据](papers/hypothesis-language/gate11-gate12-v12.3/)。

完整研究链条：**累积程序发现 → 语义可识别性检验 → 对有界模型类的有限反证 → 表征升级 → 新程序合成 → 在已声明形式模型中验证其全称规格**。有限观测不能证明任意未知黑箱语言的非正则性；Gate 12 的参数化定理只涵盖满足规范结构条件的两阶段栈程序。历史因果检查针对选定的证据列表，而非全部真实预言机调用。

另外两篇论文：[假设语言与限定证据范围的识别（中文 PDF）](papers/hypothesis-language/HYPOTHESIS_LANGUAGE.zh.pdf) · [固定引擎中的累积搜索（中文 PDF）](papers/cumulative-search/CUMULATIVE_SEARCH.zh.pdf)。[三个研究方向的语言版本索引](docs/PREPRINT_LANGUAGES.md)。
