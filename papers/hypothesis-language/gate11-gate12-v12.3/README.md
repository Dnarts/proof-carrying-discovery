# Hypothesis Languages and Proof-Carrying Representation Escalation — Gate 11–12

**Александр Странд · 23 ноября 2026 г. · Русская научная редакция**

This release is a new manuscript edition, not a replacement for any previous
preprint or its DOI, hashes or verification history.

## Main result and domain

The manuscript separates four evidence objects: a finite counterexample to a
resource-bounded model class, a formal proof about a precisely defined language,
a generated new program, and an evidence record of the controller's historical
process. These objects are not interchangeable.

`Gate12Hierarchy.canonicalMidDPDA_eval_eq_true_iff` gives a parametric,
infinite-domain specification for a **canonical two-phase** StackProgram 2
satisfying `isCanonicalMidDPDA P f = true`. The theorems
`canonicalMidDPDA_not_DFA` and `canonicalMidDPDA_not_1DCA` exclude all finite
control-state bounds in the stated Lean-defined machine classes **if** the
binary transformation distinguishes 0 and 1. The checked family covers
identity and complement; the bundle does **not** prove any statement about all
possible DPDAs.

The `checkCausalEscalation` certificate checks *selected observation-list*
prefixes, not the complete actual chronological series of all oracle calls.
The audit measured 88 versus 60 oracle calls/list records for the ordinary
palindrome task and 107 versus 61 for the complemented task. Thus the stronger
no-lookahead / policy-provenance assertion is **not established**. The Lean
proof of the formal export does not prove Python–Lean compiler equivalence.

## Reproduce locally

```bash
python3 src/build_revision.py
cd src && xelatex -halt-on-error -interaction=nonstopmode hypothesis_language_gate12_ru.tex
xelatex -halt-on-error -interaction=nonstopmode hypothesis_language_gate12_ru.tex
cd ../gate12 && python3 gate12_blind_chomsky_escalation.py --test
cd .. && python3 verification/independent_gate12_audit.py
```

The third-party version pin is Lean **4.36.0**. If `lean` is available, the
provided project sources may be checked in their original order (the exported
file is a standalone self-contained module):

```bash
cd gate12
lean gate11_soundness.lean
lean gate11_trace_checker.lean
lean gate12_exported_pal_mid.lean
```

The supplied Lean logs report exit code 0; this environment independently
replayed Python checks and hashes but **did not recompile Lean**. The original
`gate12_final_manifest.json` applies only to files in `gate12/`; the additional
release file hashes are in `RELEASE_SHA256.json`.

The `verification/` directory contains the independent finite audit and a
local XeLaTeX build log. `gate12/` preserves the research sources unmodified,
including the generator-exported Lean proof and its verification receipts.

## Content

- `hypothesis_language_gate12_ru.pdf` — compiled 10-page Russian article
- `src/hypothesis_language_gate12_ru.tex` — editable XeLaTeX article
- `src/hypothesis_language_gate11_ru.original.tex` — historical input to the editorial rebuild
- `src/build_revision.py` — deterministic build/edit instructions
- `gate12/` — upstream Gate 11/12 v12.3 source archive unpacked, 10 exact files
- `verification/` — independent finite audit files and logs
- `RELEASE_SHA256.json` — release manifest including file digests and evidence boundaries

**Publication scope:** original scientific theorems versus familiar
Myhill–Nerode, pigeonhole and counter-machine techniques require independent
prior-art comparison; this package claims a reproducible integration, not
novelty for those underlying mathematical tools.
