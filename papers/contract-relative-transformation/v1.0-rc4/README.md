# Contract-Relative Transformation Theory (CRTT)

**From Certified Discovery to Meta-Policy Closure** — Aleksandr Strand, November 2026. Manuscript release candidate v1.0-rc4. Contact: strandlex@gmail.com.

## Preprints / Препринты

| | English | Русский |
|---|---|---|
| PDF (20 pages each) | [English](CRTT-preprint-v1.0-rc4.pdf) | [Русский](CRTT-preprint-v1.0-rc4-ru.pdf) |
| Single-file LaTeX | [TEX](CRTT-preprint-v1.0-rc4.tex) | [TEX](CRTT-preprint-v1.0-rc4-ru.tex) |
| Plain-language guide / Научпоп | [HTML](crtt-en.html) | [HTML](crtt.html) |
| Clean LaTeX source | [ZIP](CRTT-arxiv-source-v1.0-rc4.zip) · [browse](source/en/) | [ZIP](CRTT-arxiv-source-v1.0-rc4-ru.zip) · [browse](source/ru/) |

**Formal artifact:** [Full architecture archive](CRTT-v1.0-FULL-ARCHITECTURE-RECONCILED.zip) · [SHA-256](CRTT-v1.0-FULL-ARCHITECTURE-RECONCILED.zip.sha256) · [canonical Lean sources and runner](formal/canonical/) · [verification scope](formal/VERIFICATION_RU.md) · [supplied T32 kernel log](formal/evidence/freeze/T32-KERNEL_CHECK.log).

**Research supplements:** [claim-to-source map A/B](publication/SOURCE_MAP_AB.md) · [map C](publication/SOURCE_MAP_C.md) · [map D](publication/SOURCE_MAP_D.md) · [companion references](publication/supplement/COMPANION_REFERENCES.pdf).

## Scope

CRTT studies finite, contract-relative, budgeted discovery and certified controller and meta-policy replacement. The executable closure preserves canonical result membership, exact impossibility characterization, modeled resource conservation and certified history for the declared funded input and finite schedule. It does not prove arbitrary self-rewriting, general-purpose discovery, or universal physical speedup.

**Fresh Lean verification (28 November 2026): PASS.** The published wrapper verified the exact RECONCILED archive and ran Lean 4.36.0 on x86-64 Linux: 21 source files, 542 audited declarations and nine CLI/reference matches. [Transcript and status (ZIP)](publication/supplement/CRTT-RC4-fresh-Linux-verification.zip) · [reproduction notes](publication/supplement/FRESH_VERIFICATION.md). This run is separate from the historical exit 127 in §8.3 and from the successful Python log replay. It is not peer review.

## Verify and build

Check the current directory with `shasum -a 256 -c SHA256SUMS.txt` on macOS or `sha256sum -c SHA256SUMS.txt` on Linux. The PDFs and the formal archive are unchanged.

For a fresh, independent Lean verification, install the pinned toolchain and run:

```bash
bash publication/supplement/verify_fresh.sh \
  CRTT-v1.0-FULL-ARCHITECTURE-RECONCILED.zip \
  ../fresh-lean-evidence
```

Keep verification output outside the immutable archive. See [fresh verification instructions](publication/supplement/FRESH_VERIFICATION.md).

Build English from `source/en/` with pdfLaTeX twice, Russian from `source/ru/` with XeLaTeX twice (FreeSerif and DejaVu Sans Mono installed locally).

The `.tex` files next to the PDFs inline all manuscript sections and bibliography from the corresponding `source/` directory. Each is a complete single-file source; standard LaTeX packages and the fonts named above are still required. Run pdfLaTeX twice on `CRTT-preprint-v1.0-rc4.tex`, or XeLaTeX twice on `CRTT-preprint-v1.0-rc4-ru.tex`.

The Russian [plain-language guide](crtt.html) and its [English translation](crtt-en.html) are self-contained HTML pages with inline styles, a linear reading order and one optional budget slider. Download an HTML file and open it in a browser. The explanatory calculator illustrates the arithmetic of the model; it is not a Lean verifier.

## Русский

Контрактно-относительная теория преобразований: от сертифицированного открытия к замыканию метаполитик. В комплект входят английский и русский препринты, самостоятельные TEX-файлы рядом с PDF, модульные исходники LaTeX, [русская научно-популярная страница](crtt.html) и [английский перевод](crtt-en.html), формальный архив CRTT v1.0, полные журналы и SHA-256. Формальные гарантии относятся к объявленной конечной детерминированной модели. [Свежий запуск Lean 4.36.0 на Linux](publication/supplement/CRTT-RC4-fresh-Linux-verification.zip) завершился успешно: 21 файл, 542 проверенные декларации и девять совпадений CLI с эталоном. Исторический `exit 127` относится к другой среде и сохранён в препринте.
