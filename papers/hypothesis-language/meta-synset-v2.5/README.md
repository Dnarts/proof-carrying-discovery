# Meta-Synset and Invariant v2.5

Aleksandr Strand · 23 November 2026

[English PDF](meta_synset_invariant_preprint_v2_5_en.pdf) · [Русский PDF (авторский оригинал)](meta_synset_invariant_preprint_v2_5.pdf) · [简体中文 PDF](meta_synset_invariant_preprint_v2_5_zh.pdf) · [Editable English sources (ZIP)](meta_synset_v2_5_english_source.zip) · [中文源文件 ZIP](meta_synset_v2_5_chinese_source.zip) · [Editorial scope notes](EDITORIAL_NOTE.md) · [译稿编校说明](EDITORIAL_NOTE.zh.md)

**A Typed System for Revising Research Representations.** The preprint proposes cross-domain structural transfer as a research heuristic. Its Lean formalization verifies the typed protocol for checking candidate transfers, inference licenses, and controller transitions under stated premises. It does not establish that the heuristic works universally or that the proposed ADT-HYPOTHESIS/1 experiment has been completed.

## Verification artifacts

The [Lean sources and author logs](evidence/) cover the revision kernel, Gates 14–16, and the unified two-axis controller. The author reports 48 declarations checked in Lean 4.36.0, including 25 with no axiom dependencies and none with `sorryAx`. The [author manifest](evidence/AUTHOR_MANIFEST.json) is preserved as supplied; it also indexes the author's original Russian TeX and verification driver, which are not included in this repository snapshot. [SHA256SUMS](SHA256SUMS) lists the files actually shipped here.

With Lean 4.36.0 selected, the five self-contained modules can be checked separately:

```sh
cd evidence
for f in *.lean; do lean "$f" || exit; done
```

The English ZIP contains TeX, Markdown, and translated figures. The Chinese ZIP contains TeX and translated figures. Both translations follow the same Russian PDF, which is byte-identical to the author’s copy.
