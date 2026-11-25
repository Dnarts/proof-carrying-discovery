# Epistemic Deformation of Reachability: Logical Irreducibility, SafeBeliefReach, and Negative Value of Information (v3.2 Bilingual Camera-Ready Release)

**License:** `FORMAL_CROSS_IRREDUCIBILITY` — proved in Lean 4.36.0 core (`27/27` declarations, `0 sorryAx`, `0 ofReduceBool`: 6 axiom-free, 10 `[propext]`, 1 `[Classical.choice]`, 8 `[propext, Quot.sound]`, 2 `[propext, Classical.choice, Quot.sound]`). Does not auto-claim `INDEPENDENT_CROSS_DISCOVERY`.

## Contents
- `epistemic_deformation_reachability_v3_2_preprint_en.pdf` & `.tex`: English camera-ready preprint (arXiv-ready LuaLaTeX, `Noto Sans`, 7 pages, 0 warnings, 0 overfull boxes).
- `epistemic_deformation_reachability_v3_2_preprint_ru.pdf` & `.tex`: Russian camera-ready preprint (LuaLaTeX, `Noto Sans`, 8 pages, 0 warnings, 0 overfull boxes).
- `lean/epistemic_deformation_reachability_v3_2.lean`: Verified Lean 4.36.0 module (zero imports, `EpistemicDeformationReachabilityV32`, 56,468 bytes, SHA-256 `0a215b6673a27802b28ff5abe59fff9d8f90219afb5c2d5950561958128ff39f`, `27/27` declarations).
- `lean/V3_2_VERIFICATION.log`: Lean 4.36.0 fail-closed verification log (`PASS`, `decls=27/27`).
- `python/epistemic_deformation_reachability_v3_2.py`, `python/test_v3_2.py`, `python/v3_2_witness_report.json`: Pure stdlib Python 3 reference engine and test suite across all 12 modules (`5/5 SafeBeliefReachInit == Policy`).
- `verify_lean.sh`: Fail-closed Lean verification wrapper (`decls=27/27`).
- `SHA256SUMS.txt`: Per-file SHA-256 manifest for all 11 release files.

## Reproduction
```bash
shasum -a 256 -c SHA256SUMS.txt
python3 python/test_v3_2.py
bash verify_lean.sh lean/epistemic_deformation_reachability_v3_2.lean 27
```
