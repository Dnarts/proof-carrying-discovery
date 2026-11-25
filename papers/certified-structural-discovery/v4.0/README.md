# Certified Structural Discovery (v4.0) — Complete `X0–X4b` Core + Lean 4.36.0 Kernel (`18/18`)

**Epistemic Status:**
- **Lean 4.36.0 formal kernel (`lean/certified_structural_discovery_v4_0.lean`):** COMPILED & KERNEL-VERIFIED (`exit=0`, `18/18` declarations, `0` external imports, `0 sorryAx`, `0 ofReduceBool` / `native_decide`, `0 Classical.choice`: `15/18` completely axiom-free, `1/18` `[propext]`, `2/18` `[propext, Quot.sound]`).
- **Python 3 executable core + standalone zero-trust verifier (`X0–X4b` + `B6` + 12 negative controls `nc1–nc12`):** EXECUTED & VERIFIED (`exit=0`, `100% PASS`).
- **Scope Boundary:** Certifies all five pillars of `DISCOVER_v4.0` (`IndependentDomains + GlueSynthesis + CrossIrreducibility + SafeBypassSynthesis + CertifiedTransfer`, hypotheses `H12–H20`, benchmarks `X0`, `X1`, `X1_H18`, `X2`, `X3`, `X4a`, `X4b`, and baseline `B6 WithMemory < NoMemory`) on finite discrete domains. Stage `X5` (bounded stochastic LLM discoverer harness) remains an optional external evaluation layer outside the deterministic formal core.

## Verified Pillars & Closed Audit Properties (`H12–H20`)

1. **Zero State-ID Leakage (`H12`, `H18`):** `D1`, `D2`, `D3` live on pairwise disjoint opaque state spaces (`set(S1) ∩ set(S2) = ∅`, `set(S1) ∩ set(S3) = ∅`, `set(S2) ∩ set(S3) = ∅`) under three independent permutation seeds `(seed1, seed2, seed3)`. `InterfaceGlue` synthesizes explicit bijections `sigma12: S1 -> S2` and `sigma13: S1 -> S3`.
2. **True Zero-Trust Separation & Kernel Invariance (`Discoverer ≠ Verifier`, `nc9–nc11`):** `independent_verifier_v4_0.py` imports only Python stdlib (zero imports from the discoverer), enforces pre-state probe observation semantics (`probe_obs[s]`, matching Lean `probeSucc`), verifies serialized JSON certificates (`ClosedLosingRegion` for all horizons `k ∈ N` + 3 ablation `PlanTree`s `C1/C2/C4`), and requires universal `∀`-bijection coverage (`n!` distinct bijections, Lean Theorems `7a/7b`) before accepting any `UNBYPASSABLE` verdict (`nc10`).
3. **Honest `A0` vs `A1` Completeness & Speedup (`H16`, `H17`):** `A0` enumerates full bijection pairs `Bij(S1,S2) × Bij(S1,S3)`; `A1` joins name-invariant structural indices `I1 |><| I2 |><| I3` with full index-cost accounting and exact completeness `Accepted(A1) == Accepted(A0)` across `X0` (`6.52x`), `X1` (`16.42x`), `X2` (`33.10x`), and `X4a` (`17.73x`, `28,800` bijection pairs over `n=5`).
4. **Genuine Rule 110 Ring Sub-Automaton (`X3`):** `X3` derives its transitions directly from synchronous 2-step Wolfram Rule 110 evolution on `Z/6Z` (`c0=(1,1,0,0,1,0)`, `c1=(0,0,1,0,1,0)` vs vacuum fixed point `(0,0,0,0,0,0)`), strictly scoped to this finite sub-automaton.
5. **Certified Cross-Library Method Transfer (`X4a`, `X4b`, `H19`, `H20`, `B6`):**
   - **Fail-closed precondition gating (`nc12`, Lean Theorem `10`):** Narrow `POINT_SINK_F2` method tokens are fail-closed blocked (`PRECONDITION_MISMATCH`) on target libraries with cyclic SCC traps or `F_3` modular observation ports, whereas `QUOTIENT_SCC_MOD` transfers soundly.
   - **Verifier kernel invariance to cyclic SCC traps (`H20`, Lean Theorems `8a/8b/9`):** `X4a` (`n=5`, `F_3`, 2-cycle trap, `0` point sinks) and `X4b` (`n=9`, complete `F_3^2` state space, 2-cycle active trap SCC + 3-cycle decoy SCC, `0` point sinks, `4 * (9!)^2 = 526,727,577,600` theoretical `A0` bijection pairs) are certified with **zero changes** to `IsClosedLosingRegion` or `verify_closed_losing_region` / `verify_plan_tree`.
   - **Method memory cost amortization (`B6`, Lean Theorem `11`):** `Cost(WithMemory) < Cost(NoMemory)` verified both per episode (`3,353 < 3,383`) and across a 3-episode target stream (`10,089 < 10,149`).

## Reproduction

```bash
shasum -a 256 -c SHA256SUMS.txt
python3 test_v4_0.py
bash lean/verify_v4_0.sh
```
