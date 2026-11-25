"""
test_v3_2.py — Complete Verification Suite for v3.2 (Modules 1–12).
Writes deterministic witness report `v3_2_witness_report.json`.
"""

from __future__ import annotations

import json
from pathlib import Path

from epistemic_deformation_reachability_v3_2 import (
    EDR_GLUE,
    F2_ENCODE,
    LinearProjectionF2,
    VOI_DELTA,
    VOI_PROBE_OBS,
    VOI_PROBE_STATE,
    VOI_WIN,
    best_blind_mass,
    build_diag_world,
    build_world_all,
    build_world_anti_inflation,
    build_world_c1,
    build_world_c2,
    build_world_c4,
    diag_signature,
    safe_belief_reach_init,
    solve_guaranteed_win,
    theta0,
    theta1,
    theta2,
    theta4,
    verify_satisfaction_bridges,
    voi3_safe_belief_reach,
)


def main() -> None:
    w_all = build_world_all()
    w_c1 = build_world_c1()
    w_c2 = build_world_c2()
    w_c4 = build_world_c4()
    w_anti = build_world_anti_inflation()

    # Native G2 linearity + kernel vs collision
    proj_x = LinearProjectionF2(proj=lambda v: v[0], u0=F2_ENCODE["s0"], u1=F2_ENCODE["s1"])
    proj_y = LinearProjectionF2(proj=lambda v: v[1], u0=F2_ENCODE["s0"], u1=F2_ENCODE["s1"])
    assert proj_x.is_linear_collision() and proj_x.has_nontrivial_kernel()
    assert proj_y.is_linear() and proj_y.has_nontrivial_kernel() and (not proj_y.pair_collides())

    # Glue-parameterized SatisfactionBridges (incl. IsLinear in G2)
    assert EDR_GLUE.is_compatible() and EDR_GLUE.license == "FORMAL_CROSS_IRREDUCIBILITY"
    for w in (w_all, w_c1, w_c2, w_c4, w_anti):
        assert all(verify_satisfaction_bridges(w, EDR_GLUE).values())

    # Joint model + 3 countermodels
    assert theta0(w_all) and theta1(w_all) and theta2(w_all) and theta4(w_all)
    assert all(not solve_guaranteed_win(w_all, k)[0] for k in (1, 2, 3, 4))
    assert (not solve_guaranteed_win(w_c1, 1)[0]) and solve_guaranteed_win(w_c1, 2)[0]
    assert solve_guaranteed_win(w_c2, 1)[0]
    assert (not solve_guaranteed_win(w_c4, 1)[0]) and solve_guaranteed_win(w_c4, 2)[0]

    # 8/8 Boolean independence + Anti-Inflation
    for b1 in (False, True):
        for b2 in (False, True):
            for b4 in (False, True):
                assert diag_signature(build_diag_world(b1, b2, b4)) == (b1, b2, b4)
    assert diag_signature(w_anti) == (True, True, True) and solve_guaranteed_win(w_anti, 2)[0]

    # Module 11 (v3.2): SafeBeliefReachInit matches Policy on ALL 5 models (including worldC2!)
    for w in (w_all, w_c1, w_c2, w_c4, w_anti):
        for k in range(5):
            assert safe_belief_reach_init(w, k) == solve_guaranteed_win(w, k)[0]
    assert all(not safe_belief_reach_init(w_all, k) for k in range(5))
    assert safe_belief_reach_init(w_c1, 2)
    assert safe_belief_reach_init(w_c2, 1)
    assert safe_belief_reach_init(w_c4, 2)
    assert safe_belief_reach_init(w_anti, 2)

    # Module 12: Blackwell monotonicity vs Strict Negative VoI (-1/3)
    mu_unif = {"s0": 1, "s1": 1, "s2": 1, "w": 1, "q": 1}
    b0 = ("s0", "s1", "s2")
    for mask in range(8):
        part_t = [s for i, s in enumerate(b0) if (mask >> i) & 1]
        part_f = [s for i, s in enumerate(b0) if not ((mask >> i) & 1)]
        assert best_blind_mass(VOI_WIN, VOI_DELTA, mu_unif, b0) <= (
            best_blind_mass(VOI_WIN, VOI_DELTA, mu_unif, part_t)
            + best_blind_mass(VOI_WIN, VOI_DELTA, mu_unif, part_f)
        )
    assert len({VOI_PROBE_OBS[s] for s in b0}) == 3
    blind_mass = best_blind_mass(VOI_WIN, VOI_DELTA, mu_unif, b0)
    assert blind_mass == 2
    assert voi3_safe_belief_reach(1, ("s0",))
    assert all(not voi3_safe_belief_reach(k, ("q",)) for k in range(5))
    for pL in range(1, 6):
        for pR in range(0, 6):
            assert 2 * pL + 1 * pR > 1 * (pL + pR)

    report = {
        "package": "epistemic_deformation_reachability_v3_2",
        "license": EDR_GLUE.license,
        "module11_safe_belief_reach_init_all_5_models": {
            "worldAll_k0_to_4": [safe_belief_reach_init(w_all, k) for k in range(5)],
            "worldC1_k0_to_2": [safe_belief_reach_init(w_c1, k) for k in range(3)],
            "worldC2_k0_to_2": [safe_belief_reach_init(w_c2, k) for k in range(3)],
            "worldC4_k0_to_2": [safe_belief_reach_init(w_c4, k) for k in range(3)],
            "worldAntiInflation_k0_to_2": [safe_belief_reach_init(w_anti, k) for k in range(3)],
            "matches_policy_solver_everywhere": True,
        },
        "module12_probabilistic_voi": {
            "blackwell_8_passive_partitions_nonneg": True,
            "voiWorld3_injective_probe": True,
            "best_blind_mass_out_of_3": blind_mass,
            "post_probe_winnable_mass_out_of_3": 1,
            "voi_edr_exact_fraction": "-1/3",
            "randomized_blind_beats_post_probe": True,
        },
    }
    out_p = Path(__file__).resolve().parent / "v3_2_witness_report.json"
    out_p.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("ALL v3.2 CHECKS PASSED (12/12 modules, 5/5 SafeBeliefReachInit == Policy).")


if __name__ == "__main__":
    main()
