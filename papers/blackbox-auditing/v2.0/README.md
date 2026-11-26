# Information-Theoretic Blind Spots of Finite Black-Box Auditing

Revised preprint v2.0, 25 November 2026.

[English PDF](blackbox_auditing_v2_en.pdf) · [Русский PDF](blackbox_auditing_v2_ru.pdf) · [Bilingual LaTeX sources and Lean evidence (ZIP)](blackbox_auditing_v2_sources_and_evidence.zip) · [SHA-256](SHA256SUMS.txt)

A finite audit can preserve the entire distribution of its outputs while missing a change in the probability of a target predicate. The paper gives an information-theoretic bound for this effect and characterizes exact certification for a prescribed predicate family by factorization through the audit profile.

Конечный аудит может сохранять весь совместный закон выходов и всё же не замечать изменения вероятности целевого предиката. В работе дана информационно-теоретическая граница этого эффекта и критерий точной сертификации заданного семейства предикатов через факторизацию по профилю аудита.

The Lean files and logs in the supplied archive cover components of the separate oracle result. The new entropy and factorization propositions are analytical, not Lean-verified. See §5 of the preprint for the exact formal scope. The manuscript proposes an LLM evaluation; it does not report results from one.
