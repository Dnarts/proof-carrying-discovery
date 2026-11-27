# Recursive Switching and Modular Oracle Separations under NP = UP

Canonical English and Russian editions, 26 November 2026 (Cycle XXI).

- Technical preprint: [English PDF](recursive_switching_np_up_en.pdf) · [TeX](recursive_switching_np_up_en.tex) · [Русский PDF](recursive_switching_np_up_ru.pdf) · [TeX](recursive_switching_np_up_ru.tex) · [简体中文 PDF](recursive_switching_np_up_zh.pdf) · [TeX](recursive_switching_np_up_zh.tex) · [עברית PDF](recursive_switching_np_up_he.pdf) · [TeX](recursive_switching_np_up_he.tex).
- Plain-language companion / Научпоп: [English PDF](interface_barrier_popular_en.pdf) · [TeX](interface_barrier_popular_en.tex) · [Русский PDF](interface_barrier_popular_ru.pdf) · [TeX](interface_barrier_popular_ru.tex) · [简体中文 PDF](interface_barrier_popular_zh.pdf) · [TeX](interface_barrier_popular_zh.tex) · [עברית PDF](interface_barrier_popular_he.pdf) · [TeX](interface_barrier_popular_he.tex).
- [Translation sources (ZIP)](recursive_switching_np_up_translation_sources.zip): English companion and Hebrew and Simplified Chinese TeX for both texts, with build notes and checksums.
- The Hebrew and Simplified Chinese PDFs translate the current editions and retain the stated scope of the analytic result and the Lean audit.
- [Full canonical bundle](rs_bundle.zip): two preprints, seven Lean 4.36.0 modules, source drafts, verification scripts and logs, and a matching checksum manifest.
- [Lean 4 verification artifact (ZIP)](recursive-switching-lean4-artifact-v1.0.zip): seven modules, original audit logs, a verifier, and checksums.
- [Checksums for this directory](SHA256SUMS.txt) · [Canonical manifest for the extracted bundle](BUNDLE_SHA256SUMS.txt). The explainer and translations are separate from the canonical bundle.

## Scope

The separation concerns oracle models with \(\mathrm{NP}^A = \mathrm{UP}^A\), not the unrelativized equality. The supplied Lean audit covers 45 statements across seven modules, including selected combinatorial, algebraic and finite-stage bridge results. The full oracle separation and its analytic ingredients are developed in the preprint, not claimed as an end-to-end Lean theorem.
