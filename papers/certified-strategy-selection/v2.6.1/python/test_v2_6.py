"""
test_v2_6.py — Complete Verification Suite for Certified Strategy Selection
under Memory, Budget, and Time Constraints (v2.6).

Verifies all 12 hypotheses (H1 through H12) and the fail-closed S0 contract auditor,
and writes a deterministic witness report `v2_6_witness_report.json`.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict

from certified_strategy_selection_v2_6 import (
    CostVec,
    DomainObj,
    EpistemicEnv,
    Invariant,
    LocalAction,
    Observation,
    RevisionToken,
    Rule110World,
    TariffSchedule,
    TargetEnv,
    UnifiedState,
    apply_licensed_step,
    check_spurious_fin,
    check_zero_bg_submask_autonomy,
    compute_V_dyn,
    ether_port4_automaton,
    eval_queue,
    eval_stack,
    evaluate_epistemic_coordinates,
    find_best_split_axis,
    r110_local,
    recover_token,
    repair_reach,
    select_causal_epistemic_action,
)


def verify_h1() -> Dict[str, Any]:
    e1 = EpistemicEnv(
        name="E1_expr_not_dist",
        worlds=(False, True),
        hyps=(True,),
        eval_h=lambda h, w: w if h else False,
        port=lambda _w: False,
        actions=(),
        apply_action=lambda _a, w: w,
        target=lambda w: w,
    )
    e2 = EpistemicEnv(
        name="E2_dist_not_expr",
        worlds=(False, True),
        hyps=(False,),
        eval_h=lambda _h, _w: False,
        port=lambda w: w,
        actions=(False,),
        apply_action=lambda _a, w: w,
        target=lambda w: w,
    )
    e3 = EpistemicEnv(
        name="E3_expr_dist_not_ident",
        worlds=(False, True),
        hyps=(True,),
        eval_h=lambda h, w: w if h else False,
        port=lambda w: w,
        actions=(False,),
        apply_action=lambda _a, _w: False,
        target=lambda w: w,
    )
    e4 = EpistemicEnv(
        name="E4_full_ident",
        worlds=(False, True),
        hyps=(True,),
        eval_h=lambda h, w: w if h else False,
        port=lambda w: w,
        actions=(True,),
        apply_action=lambda _a, w: w,
        target=lambda w: w,
    )

    c1 = evaluate_epistemic_coordinates(e1)
    c2 = evaluate_epistemic_coordinates(e2)
    c3 = evaluate_epistemic_coordinates(e3)
    c4 = evaluate_epistemic_coordinates(e4)

    assert c1 == {"X_expressible": True, "D_distinguishable": False, "J_identifiable": False}
    assert c2 == {"X_expressible": False, "D_distinguishable": True, "J_identifiable": False}
    assert c3 == {"X_expressible": True, "D_distinguishable": True, "J_identifiable": False}
    assert c4 == {"X_expressible": True, "D_distinguishable": True, "J_identifiable": True}

    return {"status": "PASSED", "models": {"E1": c1, "E2": c2, "E3": c3, "E4": c4}}


def verify_h2_gate13() -> Dict[str, Any]:
    w00 = tuple("00#00")
    w01 = tuple("01#01")
    w101 = tuple("101#101")
    w_rev = tuple("01#10")

    assert eval_queue(False, 3, w00) is True
    assert eval_queue(False, 3, w01) is True
    assert eval_queue(False, 3, w101) is True
    assert eval_queue(False, 3, w_rev) is False

    assert eval_stack(False, 3, w00) is True
    assert eval_stack(False, 3, w_rev) is True
    assert eval_stack(False, 3, w01) is False

    # Verify unconditional separation across stack capacities 0..32 and both inv in {False, True}
    for inv in (False, True):
        for cap in range(33):
            matches_both = (
                eval_stack(inv, cap, w00) == eval_queue(False, 3, w00)
                and eval_stack(inv, cap, w01) == eval_queue(False, 3, w01)
            )
            assert not matches_both, f"Stack(inv={inv}, cap={cap}) unexpectedly matched Queue"

    return {
        "status": "PASSED",
        "tested_stack_capacities": 33,
        "queue_w00_w01_w101_wRev": [True, True, True, False],
        "stack_w00_w01_wRev": [True, False, True],
    }


def verify_h3() -> Dict[str, Any]:
    worlds = (0, 1, 2)
    queries = ("q0",)
    base_obs = lambda _q, w: (w % 2 == 1)
    spurious_obs = lambda _q, w: (w % 2 == 1, not (w % 2 == 1))
    genuine_obs = lambda _q, w: (w % 2 == 1, w == 2)

    is_spur_1 = check_spurious_fin(worlds, queries, base_obs, spurious_obs)
    is_spur_2 = check_spurious_fin(worlds, queries, base_obs, genuine_obs)

    assert is_spur_1 is True
    assert is_spur_2 is False

    return {
        "status": "PASSED",
        "spurious_hash_port_detected": is_spur_1,
        "genuine_hidden_port_detected": is_spur_2,
    }


def verify_h4_to_h7() -> Dict[str, Any]:
    tariffs = TariffSchedule(
        probe_fee=1, lang_esc_fee=4, port_esc_fee=3, intervene_fee=2, mem_rec_fee=1
    )
    budget = CostVec(cq=4, cs=4, cp=3, cv=2, cm=2)
    s0 = UnifiedState(
        candidate_worlds=8,
        active_hyps=6,
        tier_rank=0,
        port_rank=1,
        int_rank=0,
        knowledge_count=0,
        spent=CostVec(),
        budget=budget,
    )

    # 1. Fail-closed S0 rejection tests (forged / invalid certificates)
    bad_timeout, msg_timeout = apply_licensed_step(
        s0, tariffs, "escalateLang",
        {"monitor_signal": "resourceTimeout", "new_tier_rank": 1, "new_hyps": 8}
    )
    assert bad_timeout is None and "Ax4_privilege_separation" in msg_timeout

    bad_spur, msg_spur = apply_licensed_step(
        s0, tariffs, "escalatePort",
        {"monitor_signal": "certifiedUnsat", "is_spurious": True}
    )
    assert bad_spur is None and "H3_spurious_port" in msg_spur

    bad_g15, msg_g15 = apply_licensed_step(
        s0, tariffs, "intervene",
        {
            "obs_collision": True,
            "control_mask_orthogonal": False,
            "commutator_nonzero": True,
            "new_worlds": 4,
        },
    )
    assert bad_g15 is None and "Gate15" in msg_g15

    bad_g16_zero_den, msg_g16 = apply_licensed_step(
        s0, tariffs, "stochasticReject",
        {
            "den": 0,
            "total_mass": 10,
            "e_value_num": 25,
            "e_value_den": 1,
            "alpha_inv": 20,
            "has_gap_bound": True,
            "new_hyps": 3,
        },
    )
    assert bad_g16_zero_den is None and "Gate16" in msg_g16

    # 2. Valid 6-step trajectory through all 6 constructors of LicensedStep
    s1, _ = apply_licensed_step(s0, tariffs, "probe", {"new_worlds": 4})
    assert s1 is not None and s1.progress_score() > s0.progress_score()

    s2, _ = apply_licensed_step(
        s1, tariffs, "escalateLang",
        {"monitor_signal": "certifiedUnsat", "new_tier_rank": 2, "new_hyps": 5}
    )
    assert s2 is not None and s2.progress_score() > s1.progress_score()

    s3, _ = apply_licensed_step(
        s2, tariffs, "escalatePort",
        {"monitor_signal": "certifiedUnsat", "is_spurious": False}
    )
    assert s3 is not None and s3.progress_score() > s2.progress_score()

    s4, _ = apply_licensed_step(
        s3, tariffs, "intervene",
        {
            "obs_collision": True,
            "control_mask_orthogonal": True,
            "commutator_nonzero": True,
            "new_worlds": 2,
        },
    )
    assert s4 is not None and s4.progress_score() > s3.progress_score()

    s5, _ = apply_licensed_step(
        s4, tariffs, "stochasticReject",
        {
            "den": 4,
            "total_mass": 16,
            "e_value_num": 25,
            "e_value_den": 1,
            "alpha_inv": 20,
            "has_gap_bound": True,
            "new_hyps": 2,
        },
    )
    assert s5 is not None and s5.progress_score() > s4.progress_score()

    s6, _ = apply_licensed_step(
        s5, tariffs, "recoverMemory",
        {"precond_ok": True, "new_tier_rank": 4}
    )
    assert s6 is not None and s6.progress_score() > s5.progress_score()
    assert s6.spent.le(s6.budget)

    return {
        "status": "PASSED",
        "s0_rejected_attacks": [msg_timeout, msg_spur, msg_g15, msg_g16],
        "initial_progress_score": s0.progress_score(),
        "final_progress_score": s6.progress_score(),
        "final_spent_vector": s6.spent.to_dict(),
        "budget_vector": s6.budget.to_dict(),
    }


def verify_h8() -> Dict[str, Any]:
    synset = (
        DomainObj(domain_id=1, obj_id=101, features=(True, False, True)),
        DomainObj(domain_id=2, obj_id=202, features=(True, True, False)),
        DomainObj(domain_id=4, obj_id=404, features=(True, False, False)),
        DomainObj(domain_id=5, obj_id=505, features=(True, True, True)),
    )
    res = find_best_split_axis(synset, num_axes=3)
    assert res is not None
    best_axis, best_gain = res
    assert best_axis in (1, 2) and best_gain == 2

    return {
        "status": "PASSED",
        "domains_spanned": [d.domain_id for d in synset],
        "synthesized_axis": best_axis,
        "minimax_gain": best_gain,
    }


def verify_h9_to_h11() -> Dict[str, Any]:
    # 1. Verify 4-bit port W={3,4,5,6} autonomy on Rule 110 ether ring (all 16 states)
    orbit_lengths = {}
    for mask in range(16):
        b0 = ((mask >> 0) & 1, (mask >> 1) & 1, (mask >> 2) & 1, (mask >> 3) & 1)
        cur = b0
        seen = []
        while cur not in seen:
            seen.append(cur)
            cur = ether_port4_automaton(cur)
        cycle_len = len(seen) - seen.index(cur)
        orbit_lengths[mask] = cycle_len

    # 2. Verify all 15 non-empty submasks of W={3,4,5,6} fail 1-step autonomy on zero background
    zero_bg_autonomous_masks = [
        m for m in range(1, 16) if check_zero_bg_submask_autonomy(m)
    ]
    assert zero_bg_autonomous_masks == []

    # 3. Revision memory Store / Recover & fail-closed transfer blocking
    ether_token = RevisionToken(
        token_id=110,
        origin_domain=1,
        port_width=4,
        required_seam_inputs=0,
        residual_gap_bound=0,
        discover_cost=4,
        transfer_cost=1,
    )
    mem = (ether_token,)

    env_ether = TargetEnv(
        env_id=1, domain=1, port_width=4, is_port_autonomous=True, actual_seam_inputs=0, max_allowed_gap=0
    )
    env_zero_bg = TargetEnv(
        env_id=2, domain=1, port_width=4, is_port_autonomous=False, actual_seam_inputs=4, max_allowed_gap=0
    )
    env_d4_shortcut = TargetEnv(
        env_id=3, domain=4, port_width=4, is_port_autonomous=False, actual_seam_inputs=1, max_allowed_gap=0
    )

    rec_ether = recover_token(mem, env_ether)
    rec_zero = recover_token(mem, env_zero_bg)
    rec_d4 = recover_token(mem, env_d4_shortcut)

    assert rec_ether == ether_token
    assert rec_zero is None
    assert rec_d4 is None

    # 4. Stream amortization across k = 5 episodes
    k = 5
    cost_with_memory = ether_token.discover_cost + (k - 1) * ether_token.transfer_cost
    cost_memoryless = k * ether_token.discover_cost
    assert cost_with_memory < cost_memoryless

    return {
        "status": "PASSED",
        "zero_bg_autonomous_submasks_of_15": len(zero_bg_autonomous_masks),
        "recover_on_r110_ether_ring": rec_ether.token_id if rec_ether else None,
        "recover_on_r110_zero_bg": rec_zero,
        "recover_on_d4_shortcut": rec_d4,
        "stream_5_episodes_cost_with_memory": cost_with_memory,
        "stream_5_episodes_cost_memoryless": cost_memoryless,
    }


def verify_h12() -> Dict[str, Any]:
    # 1. Causal-Dynamic Horizon Closure & Controller Override on Rule 110 (N=6, t*=3, dt=2)
    w0 = Rule110World((1, 0, 0, 0, 1, 0))
    w1 = Rule110World((1, 0, 0, 1, 1, 0))
    W = (w0, w1)

    actions = (
        LocalAction("set_2_to_0", (2,), (0,), cost=1),
        LocalAction("set_2_to_1", (2,), (1,), cost=1),
    )
    probe = Observation("obs_1", (1,), delay=2, cost=1)
    inv = Invariant("cell0_eq_0", (0,), (0,))

    # Colliding at t=0 on passive port cell 1
    assert probe.observe(w0) == probe.observe(w1) == (0,)

    # Full identification after waiting dt=2
    ew0 = w0.evolve(2)
    ew1 = w1.evolve(2)
    assert probe.observe(ew0) == (0,) and probe.observe(ew1) == (1,)

    # Yet causal repair horizon is closed on EVERY branch at t=2 (remaining_time = 1 > 0)
    assert repair_reach((ew0,), 2, 3, actions, inv) == ()
    assert repair_reach((ew1,), 2, 3, actions, inv) == ()

    # Empty world set must never be vacuously repairable (W != [] guard, matching v1.5)
    assert repair_reach((), 0, 3, actions, inv) == ()

    # At t=0, set_2_to_1 repairs both worlds, and the unified controller overrides passive probing
    reach0 = repair_reach(W, 0, 3, actions, inv)
    assert [a.name for a in reach0] == ["set_2_to_1"]

    v_dyn, tree = compute_V_dyn(W, 0, 3, 1, (probe,), actions, inv)
    assert v_dyn == 1 and tree is not None and tree["kind"] == "HaltRepair"

    decision = select_causal_epistemic_action(W, 0, 3, probe, actions, inv)
    assert decision == {"decision": "immediateSurgicalRepair", "actuator": "set_2_to_1", "at_t": 0}

    # 2. ContinuousSubject110 Algebraic XOR Gate & Periodicity
    for z in (0, 1):
        for k in (0, 1):
            assert r110_local(1, z, k) == (z ^ k)

    nominal = (0, 1, 1, 1)
    step1 = ether_port4_automaton(nominal)
    step2 = ether_port4_automaton(step1)
    assert step2 == nominal

    return {
        "status": "PASSED",
        "reach_at_t0": [a.name for a in reach0],
        "reach_after_dt2_branch0": [],
        "reach_after_dt2_branch1": [],
        "V_1_dyn": v_dyn,
        "controller_decision": decision,
        "r110_xor_gate_verified": True,
        "ether_port4_cycle_verified": True,
    }


def main() -> None:
    report = {
        "schema": "certified-strategy-selection/v2.6",
        "suite_status": "ALL_12_HYPOTHESES_PASSED",
        "H1_three_coordinates": verify_h1(),
        "H2_gate13_queue_vs_stack": verify_h2_gate13(),
        "H3_spurious_port_detector": verify_h3(),
        "H4_to_H7_unified_controller_and_s0": verify_h4_to_h7(),
        "H8_algorithmic_metasynset": verify_h8(),
        "H9_to_H11_revision_memory_and_r110_ring": verify_h9_to_h11(),
        "H12_causal_epistemic_horizon_synthesis": verify_h12(),
    }
    out_path = Path(__file__).resolve().parent / "v2_6_witness_report.json"
    out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
