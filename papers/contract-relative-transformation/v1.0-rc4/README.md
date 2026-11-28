# Contract-Relative Transformation Theory (CRTT)

**From Certified Discovery to Meta-Policy Closure** — Aleksandr Strand, November 2026. Manuscript release candidate v1.0-rc4. Contact: strandlex@gmail.com.

## Preprints / Препринты

| | English | Русский |
|---|---|---|
| PDF (20 pages each) | [English](CRTT-preprint-v1.0-rc4.pdf) | [Русский](CRTT-preprint-v1.0-rc4-ru.pdf) |
| Complete publication package | [ZIP](CRTT-preprint-v1.0-rc4.zip) | [ZIP](CRTT-preprint-v1.0-rc4-ru.zip) |
| Clean LaTeX source | [ZIP](CRTT-arxiv-source-v1.0-rc4.zip) · [browse](source/en/) | [ZIP](CRTT-arxiv-source-v1.0-rc4-ru.zip) · [browse](source/ru/) |

**Formal artifact:** [Full architecture archive](CRTT-v1.0-FULL-ARCHITECTURE-RECONCILED.zip) · [SHA-256](CRTT-v1.0-FULL-ARCHITECTURE-RECONCILED.zip.sha256) · [canonical Lean sources and runner](formal/canonical/) · [verification scope](formal/VERIFICATION_RU.md) · [supplied T32 kernel log](formal/evidence/freeze/T32-KERNEL_CHECK.log).

**Publication evidence:** [response to review](publication/REVIEW.md) · [claim-to-source map A/B](publication/SOURCE_MAP_AB.md) · [map C](publication/SOURCE_MAP_C.md) · [map D](publication/SOURCE_MAP_D.md) · [companion references](publication/supplement/COMPANION_REFERENCES.pdf) · [translation audit](publication/ru/TRANSLATION_AUDIT.json).

## Scope

CRTT studies finite, contract-relative, budgeted discovery and certified controller and meta-policy replacement. The executable closure preserves canonical result membership, exact impossibility characterization, modeled resource conservation and certified history for the declared funded input and finite schedule. It does not prove arbitrary self-rewriting, general-purpose discovery, or universal physical speedup.

The supplied successful Lean 4.36.0 run records 21 source files, 542 audited declarations and nine CLI/reference scenarios. The unchanged RECONCILED archive preserves complete logs, the independent finite cross-checks, and replay evidence. RC4's clean local attempt stopped at exit 127 (compiler unavailable); no new successful independent Lean compilation or formal-artifact DOI is claimed. The manuscript is a preprint, not an assertion of peer-reviewed acceptance. Early historical numbering gaps remain documented in the full archive.

## Verify and build

From this directory on macOS: `shasum -a 256 -c SHA256SUMS.txt` (Linux: `sha256sum -c SHA256SUMS.txt`). The original English and Russian publication ZIPs and the full formal ZIP are unchanged. The standalone English PDF here is the exact PDF in the English ZIP (the earlier standalone PDF had identical rendered pages, extracted text and link targets but different PDF bytes); the Russian standalone PDF already matched. See [packaging receipt](publication/PUBLICATION_CHECK.json).

For a fresh, independent Lean verification, install the pinned toolchain and run:

```bash
bash publication/supplement/verify_fresh.sh \
  CRTT-v1.0-FULL-ARCHITECTURE-RECONCILED.zip \
  ../fresh-lean-evidence
```

Keep verification output outside the immutable archive. See [fresh verification instructions](publication/supplement/FRESH_VERIFICATION.md).

Build English from `source/en/` with pdfLaTeX twice, Russian from `source/ru/` with XeLaTeX twice (FreeSerif and DejaVu Sans Mono installed locally). See the language-specific original README files in `publication/`.

## Русский

Контрактно-относительная теория преобразований: от сертифицированного открытия к замыканию метаполитик. В комплект входят английский и русский препринты, исходники LaTeX, формальный архив CRTT v1.0, полные журналы и SHA-256. Формальные гарантии относятся к объявленной конечной детерминированной модели. Сохранённый успешный журнал и повторный аудит не заменяют новый независимый запуск Lean. DOI формального приложения ещё не присвоен.
