# Meta-Synset and Invariant v2.5

Aleksandr Strand · 23 November 2026

[English PDF](meta_synset_invariant_preprint_v2_5_en.pdf) · [Русский PDF (авторский оригинал)](meta_synset_invariant_preprint_v2_5.pdf) · [Editable English sources (ZIP)](meta_synset_v2_5_english_source.zip) · [Editorial scope notes](EDITORIAL_NOTE.md)

**A Typed System for Revising Research Representations.** The preprint proposes cross-domain structural transfer as a research heuristic. Its Lean formalization verifies the typed protocol for checking candidate transfers, inference licenses, and controller transitions under stated premises. It does not establish that the heuristic works universally or that the proposed ADT-HYPOTHESIS/1 experiment has been completed.

## Verification artifacts

The [Lean sources and author logs](evidence/) cover the revision kernel, Gates 14–16, and the unified two-axis controller. The author reports 48 declarations checked in Lean 4.36.0, including 25 with no axiom dependencies and none with `sorryAx`. The [author manifest](evidence/AUTHOR_MANIFEST.json) is preserved as supplied; it also indexes the author's original Russian TeX and verification driver, which are not included in this repository snapshot. [SHA256SUMS](SHA256SUMS) lists the files actually shipped here.

With Lean 4.36.0 selected, the five self-contained modules can be checked separately:

```sh
cd evidence
for f in *.lean; do lean "$f" || exit; done
```

The English ZIP includes its TeX, Markdown, and translated figures. The Russian PDF is byte-identical to the author’s copy. No Chinese edition of v2.5 is included.
