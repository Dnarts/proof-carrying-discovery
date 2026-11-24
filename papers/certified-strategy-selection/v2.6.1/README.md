# Observe, Change Representation, or Act: Certified Strategy Selection under Memory, Budget, and Time Constraints (v2.6.1 Final Release)

## Contents
- `certified_strategy_selection_preprint_v2_6_1.pdf`: Compiled Russian preprint (LuaLaTeX, `Noto Serif`, 9 pages, clickable `hyperref` links, 0 warnings, 0 overfull boxes).
- `certified_strategy_selection_preprint_v2_6_1.tex`: Russian preprint LaTeX source (7 sections, Remark 6.2 on `H12` scope, `#print axioms` table, and scope boundaries).
- `lean/certified_strategy_selection_v2_6_1.lean`: Self-contained Lean 4.36.0 module (zero Mathlib, 1,253 lines, pure LF, 27/27 declarations closing $H_1\text{--}H_{12}$, 0 `sorryAx`, 0 `native_decide`, 0 warnings).
- `lean/V2_6_1_VERIFICATION.log`: Full Lean 4.36.0 verification log (`arm64-apple-darwin24.6.0`, commit `611c117b`) and `#print axioms` audit matching `lean/certified_strategy_selection_v2_6_1.lean` byte-for-byte.
- `python/certified_strategy_selection_v2_6.py`, `python/test_v2_6.py`, `python/v2_6_witness_report.json`: Reproducible stdlib Python 3 reference engine (including explicit `W != []` non-vacuous guard in `repair_reach`), fail-closed `S0` contract auditor, and deterministic witness report across $H_1\text{--}H_{12}$.
- `SHA256SUMS.txt`: Complete per-file SHA-256 manifest covering every file in this release (8/8).

## Reproduction Commands
```bash
shasum -a 256 -c SHA256SUMS.txt
python3 python/test_v2_6.py
lean lean/certified_strategy_selection_v2_6_1.lean
```

## Results & Theorem Matrix ($H_1\text{--}H_{12}$)
| ID | Scope | Status | Key Lean 4.36.0 Declarations |
| :--- | :--- | :--- | :--- |
| **$H_1$** | 3-Coordinate Accessibility $\mathcal{E}(E) = \langle \mathcal{X}_E, \mathcal{D}_E, \mathcal{J}_E \rangle$ | **VERIFIED** | `H1_identifiable_implies_expressible`, `H1_identifiable_implies_distinguishable`, `H1_three_coordinate_strict_separation` |
| **$H_2$** | Multi-Symbol FIFO `evalQueue` vs 1-Parameter Arbitrary-Capacity `evalStack(inv, cap)` | **VERIFIED** | `H2_queue_recognizes_fifo_copy`, `H2_stack_recognizes_lifo_palindrome`, `H2_gate13_queue_separates_from_arbitrary_stack` |
| **$H_3$** | Computable Detector `checkSpuriousFin` for Spurious Sensor Extensions | **VERIFIED** | `H3_checkSpuriousFin_sound`, `H3_detector_separates_spurious_from_genuine` |
| **$H_4\text{--}H_6$** | Unified Controller `LicensedStep` (Probe, Lang/Port Escalation, Intervention, Stochastic E-Value, Memory, Privilege Separation) | **VERIFIED** | `H4_licensed_step_preserves_vector_budget`, `H4_privilege_separation_blocks_timeout_escalation`, `H5_spurious_port_blocked`, `H6_gate15_and_gate16_certificates_enforced` |
| **$H_7 / H_7^+$** | 5D Vector Budget `CostVec` (`spent(s') <= B`) & Strict Epistemic Progress Score | **VERIFIED** | `H7_licensed_step_strict_epistemic_progress` |
| **$H_8$** | Algorithmic Feature Synthesis (`projFeature`, `isAxialSplit`, `freezeAxisQuery`) | **VERIFIED** | `H8_partition_length_conservation`, `H8_algorithmic_metasynset_minimax_gain_ge_1`, `H8_cross_domain_instance_verified` |
| **$H_9\text{--}H_{11}$** | Typed `RevisionMemory` (`Store`/`Recover`), Stream Amortization ($c_m < c_s$), & Rule 110 Ring Background Blocking | **VERIFIED** | `H9_recoverToken_preserves_provenance_and_gap`, `H10_memory_transfer_strict_stream_amortization`, `H11_unsound_transfer_blocked_on_r110_zero_bg_and_d4_shortcut` |
| **$H_{12}$** | Causal-Epistemic Horizon Closure ($t^*=3, \Delta t=2$) & 2-Step Port Cycle / Anomaly Trigger ($t^*=4$ contrast lives in `causal_dynamic_repair_v1_5_fixed.lean`) | **VERIFIED** | `H12_causal_epistemic_horizon_synthesis`, `H12_rule110_algebraic_xor_gate`, `H12_temporal_subject_period2_and_anomaly_trigger` |

## Lean 4.36.0 Declarations & Axiom Profile (27/27, 0 `sorryAx`, 0 `native_decide`)
- **Axiom-free (10):** `H1_identifiable_implies_expressible`, `H1_identifiable_implies_distinguishable`, `H2_queue_recognizes_fifo_copy`, `H2_stack_recognizes_lifo_palindrome`, `H3_detector_separates_spurious_from_genuine`, `H8_cross_domain_instance_verified`, `H11_unsound_transfer_blocked_on_r110_zero_bg_and_d4_shortcut`, `H12_causal_epistemic_horizon_synthesis`, `H12_rule110_algebraic_xor_gate`, `H12_temporal_subject_period2_and_anomaly_trigger`
- **`[propext]` (6):** `H1_E2_distinguishable_not_expressible`, `H3_checkSpuriousFin_sound`, `H4_licensed_step_preserves_vector_budget`, `H4_privilege_separation_blocks_timeout_escalation`, `H5_spurious_port_blocked`, `H6_gate15_and_gate16_certificates_enforced`
- **`[propext, Quot.sound]` (7):** `H1_E1_expressible_not_distinguishable`, `H1_E3_expr_and_dist_not_identifiable`, `H1_three_coordinate_strict_separation`, `H2_stack_inv_false_rejects_w01`, `H2_stack_inv_true_rejects_w00`, `H2_gate13_queue_separates_from_arbitrary_stack`, `H8_partition_length_conservation`
- **`[propext, Classical.choice, Quot.sound]` (4):** `H7_licensed_step_strict_epistemic_progress`, `H8_algorithmic_metasynset_minimax_gain_ge_1`, `H9_recoverToken_preserves_provenance_and_gap`, `H10_memory_transfer_strict_stream_amortization`
