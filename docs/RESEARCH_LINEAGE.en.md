# Research lineage: from acquired rules to certified representation change

[Main README](../README.md) · [Русская версия](RESEARCH_LINEAGE.ru.md)

The scientific unit of the project is not just a discovered program. It is a **claim with its domain, the rejected alternative classes, the synthesized representation, and independently checkable evidence**. These do not merge into a single “verified” flag.

## Chain of results

| Stage | Evidence in this repository | Established scope |
|---|---|---|
| **Cumulative discovery, software v1.1.1** | [Original preprint](../PREPRINT_v1.1.en.pdf), [experiments](../v1_1/) | Macro/law acquisition, causal contribution under a declared cost model, and bounded one-counter synthesis/transfer. No general search-performance guarantee. |
| **Controlled language change** | [Lean modules](../formal/), [formal supplement](FORMAL_RESULTS.en.md) | Safety of escalation assuming a sound structural witness; a mathematically specified nonregular language has no DFA recognizer and has a constructed 1-DCA recognizer. |
| **Model-relative identification, Gate 4B–5** | [Earlier hypothesis-language paper](../papers/hypothesis-language/HYPOTHESIS_LANGUAGE.en.md), [finite Lean source](../papers/hypothesis-language/formal/) | Semantic version spaces, agreement queries, and a finite observer with an augmented Rule 110 base. Does not establish origin membership of arbitrary initial states. |
| **Proof-carrying escalation, Gate 11–12 v12.3** | [Latest Russian PDF](../papers/hypothesis-language/gate11-gate12-v12.3/hypothesis_language_gate12_ru.pdf), [Lean program and checker](../papers/hypothesis-language/gate11-gate12-v12.3/gate12/), [reproduction package](../papers/hypothesis-language/gate11-gate12-v12.3/) | Bounded finite-class refutation; reusable parametric theorem for canonical two-phase stack programs; global exclusion of finite-control DFA/1-DCA in the *declared Lean models*, when the binary map separates the two symbols. |

Gate 6–10 explored more elaborate language transformations and their finite controls. Their complete separately audited research bundles are **not all present here**, so they must not be promoted to a stronger status than their actual available evidence.

## The logical discontinuities

**1. Finite exclusion of bounded DFA.** Given \(k+1\) pairwise distinguishable prefixes, a finite certificate contradicts the existence of any matching DFA with at most \(k\) states. It does **not** exclude all finite DFAs of arbitrary size for an unknown oracle.

**2. Universal separation of a defined language.** Myhill–Nerode and counting arguments prove that certain *fully specified* languages cannot be recognized by any finite-control DFA/1-DCA in the stated model. A theorem with unbounded quantifiers is not derived solely from finitely many black-box answers.

**3. Universal certification of a generated program.** The current Lean source proves the recognized language of a canonical StackProgram 2 under the formal predicate and the binary-map assumptions. Two generated examples use identity and complement maps. It does **not** prove arbitrary DPDA soundness or general Python/Lean compiler equivalence.

**4. Causal history verification.** The checker validates the timestamps and correctness of *selected observation-list prefixes*. The full Python oracle-call sequence is not represented by that list: the two tasks had 88/107 calls, while only 60/61 observations were retained. A no-lookahead theorem for the actual decision process remains **unestablished**.

These are four distinct proof obligations. A claim becomes stronger only when a new witness supplies the missing obligation, not when a historical PASS label is restated.

## Which artifact to cite

For Gate 11–12 universal assertions, cite the [current manuscript and exported Lean file](../papers/hypothesis-language/gate11-gate12-v12.3/) together with the [successful independent GitHub Actions run](https://github.com/Dnarts/proof-carrying-discovery/actions/runs/45134680055). For the original search-cost evidence cite [v1.1](../PREPRINT_v1.1.en.pdf). For language-relative identification cite the [earlier methods paper](../papers/hypothesis-language/). For abstract representational-change safety cite the [formal supplement](FORMAL_RESULTS.en.md).

The root [MANIFEST.json](../MANIFEST.json) and [SHA256SUMS.txt](../SHA256SUMS.txt) are the **historical v1.1.1 release index**, not a claim that all later materials belong to that software release. The Gate 11–12 work has its [own file-level digest manifest](../papers/hypothesis-language/gate11-gate12-v12.3/RELEASE_SHA256.json).

For related but separately justified results see [Rule 110 Dependency Fronts](https://github.com/Dnarts/rule110-dependency-fronts) and [Channel Topology and Memory](https://github.com/Dnarts/channel-topology-and-memory).
