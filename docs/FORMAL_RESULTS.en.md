# Formal supplement: controlled representation change (22 November 2026)

**Status:** submitted Lean 4.36.0 source and author-provided successful verification receipts. CI independently checks the pinned toolchain and both exact source files. This is a supplement to [v1.1](../PREPRINT_v1.1.en.md), not a silent revision of the historical Python experiments.

## Modules

- [ControlledRepChange.lean](../formal/ControlledRepChange.lean): abstract fixed-verifier framework, no-false-escalation under explicit assumptions (T1), early stopping costs (T2), break-even condition (T3), and static versus dependency-closure deletion (T4).
- [DFAto1DCASeparation.lean](../formal/DFAto1DCASeparation.lean): Myhill–Nerode witness soundness for bounded DFAs, concrete instantiation of the safety environment, a constructed three-control-state one-counter recognizer for the Boolean encoding of a^n b^n, and proof of nonrecognizability by any finite DFA.
- [Author-provided Lean receipts](../formal/verification/): reported Lean 4.36.0 exit code 0 and `#print axioms` outputs. The receipts are provenance evidence; the CI run is the independent check.

Source SHA-256:
- `ControlledRepChange.lean`: `fcdcb52c6407b726a93cb804388dbf38fd239ef2798cb8ccd7ebb4c14dc2be90`
- `DFAto1DCASeparation.lean`: `7c5d80eb3f78d5e616f74c0c4c2b83d41d417c948f32899fc8413733d38ef7ee`

## What the theorems do not prove

They do not show that an algorithm invents the counter memory class, discovers a new invariant without a supplied template, automatically constructs a Myhill–Nerode certificate from an unknown oracle, or recursively discovers further invariants. The monitor-soundness assumption is discharged for a *valid mathematical witness*, not for an arbitrary external monitor's outputs. Cost comparisons are conditional on the explicitly formalized cost model. Lean's standard axioms (`propext`, `Quot.sound`, and where applicable `Classical.choice`) appear in the receipts; no custom axioms, `sorry`, or `native_decide` are declared in these modules.

## Reproduce

From the repository root, with Lean 4.36.0 installed:

```sh
cd formal
lean ControlledRepChange.lean
lean DFAto1DCASeparation.lean
sha256sum -c <(printf '%s\n' 'fcdcb52c6407b726a93cb804388dbf38fd239ef2798cb8ccd7ebb4c14dc2be90  ControlledRepChange.lean' '7c5d80eb3f78d5e616f74c0c4c2b83d41d417c948f32899fc8413733d38ef7ee  DFAto1DCASeparation.lean')
```

The existing Python v1.1 reproduction remains `python3 tests/audit_release.py` from the repository root.

## Related experiments

The separate equational-transfer v1.2/v1.3 prototypes investigate representation repair, coordinate transport, and ablation of a stored edit versus its resulting expression. These are **Python experiments, not Lean theorems**, and their bridge to the actual v1.1 NAND-synthesized XOR artifact remains to be built.
