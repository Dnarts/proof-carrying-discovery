# Hypothesis Languages and Evidence-Scoped Identification

**Canonical location:** this directory in **Proof-Carrying Discovery**. The Rule 110 repository remains the *domain-specific experimental companion*, not the canonical home for this language-and-certification argument.

**Working preprint, editorial revision 23 November 2026:** [English manuscript](HYPOTHESIS_LANGUAGE.en.md) · [Русская редакция](HYPOTHESIS_LANGUAGE.ru.md) · [Claim/evidence audit](CLAIMS_AND_PROVENANCE.md).

## What is new here?

The earlier [Cumulative Search preprint v1.1](../../PREPRINT_v1.1.en.md) studies fixed-engine search, acquisition of program macros, inferred invariants, and bounded representation escalation. This companion asks a different question: **what does it take to justify calling a hypothesis uniquely identified, when the language, observation channel and evidence state can change?**

The paper is structured around (1) language-scoped semantic version spaces, (2) an exact two-sided window in finite-dimensional $\mathbb F_2$-linear languages, (3) distinguishing versus model-falsifying agreement queries, and (4) a finite augmented Rule 110 observer as a constructive case study.

This is **not** a theorem that the binary Rule 110 automaton learns a new language or that it can fully certify its own origin. It does **not** replace the three Rule 110 papers or claim novelty for Hamming codes, OGIS or runtime verification.

## Exactly which evidence is here?

- [Verbatim supplied Lean 4.36.0 source](formal/gate5_invariants.lean), SHA-256: **2baaffcb0b30bea445917b3dfbf7c75823cff4213d0ab53b955eb0fbe6b49d78**.
- [Verification log with a personal local path replaced](formal/verification.redacted.log). Source verification log SHA-256 before redaction: **d2938e1d26a9e891db8d8bd80cfce3c48084c2176b35922a73ea1091d1d4648c**. Reports Lean 4.36.0, 10 declarations, zero failed checks; this snapshot was not recompiled by the editor.
- Original seven-page Russian PDF (22 Nov 2026): SHA-256 **aa3b995113bfec3313a30f9824f8da27a1d670558ec8a7dc06d92adf70f235fb**. It was supplied as an attachment and is preserved by the author; **the original PDF binary is not embedded in this repository snapshot**. The Markdown manuscripts are new, explicitly scoped scholarly editions, not byte-for-byte transcription of the historical PDF.
- **Not included**: the full Python source for Gate 5 v3.2, an independent end-to-end v3.2 run, or a Lean proof of the 64-site augmented dynamics.

## Reproduce the formal subset

Install **Lean 4.36.0**; from this directory run the core source using:

~~~sh
lean formal/gate5_invariants.lean
~~~

The theorem names and reported axiom dependencies are documented in [the claim ledger](CLAIMS_AND_PROVENANCE.md). This check establishes the finite mathematical statements *as encoded in Lean*, not the complete cellular-automaton trace.

## Placement

- **Proof-Carrying Discovery**: primary work on evidence-scoped identification, certification and changes of representation.
- [Rule 110 Dependency Fronts](https://github.com/Dnarts/rule110-dependency-fronts): exact causal fronts, observability and dynamics; reference the present paper as a related *methodological* companion when accessible.
- [Channel Topology and Memory](https://github.com/Dnarts/channel-topology-and-memory): a distinct line on stochastic channels and retained memory.

This repository is publicly accessible at the time of the 23 November 2026 readback. No DOI, peer review, or independent end-to-end Gate 5 v3.2 replication is claimed. Repository visibility is a separate owner-controlled setting and was not changed by these file commits.