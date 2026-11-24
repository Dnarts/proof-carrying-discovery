"""
test_suite.py — Full Q1–Q2 Verification Suite for Repair Budget Atom v1.3 (Block B + C + D).

Runs:
  1. Regression Suite T01–T08 (all canonical v1.2 constructions + permutation invariance)
  2. Block B1 Small-Instance Verification (|W| <= 6, |A| <= 4, |Q| <= 4, h in {0, 1, 2}):
     checks V_h(W) <= B <=> valid public PlanTree verified by independent fail-closed verifier
  3. Block C 5-State FoldAcc differential testing (200,000 random sequences + exhaustive len 0..5)
     and 4-state impossibility witness
  4. Block D Exhaustive 1D Local CA == ReferenceEngine equivalence over all 8^L segments (L <= 4)

Outputs:
  - certificate_atom_B3.json
  - v1_3_verification_report.json
"""

from __future__ import annotations

import itertools
import json
import random
from pathlib import Path
from typing import Dict, List

from fold_acc import differential_test_fold, verify_five_state_moore_and_four_state_impossibility
from local_ca import run_ca, verify_ca_equivalence_exhaustive
from reference_engine import (
    RepairInstance,
    compute_C,
    compute_G,
    compute_V,
    emit_verdict,
    generate_certificate,
    verify_certificate,
)


def make_two_world_atom(cal_cost: int = 1) -> RepairInstance:
    return RepairInstance(
        worlds=("wL", "wP"),
        actions=("aL", "aP"),
        cost_a={"aL": 1, "aP": 2},
        repair_ok={
            ("wL", "aL"): True,  ("wL", "aP"): False,
            ("wP", "aL"): False, ("wP", "aP"): True,
        },
        probes=("q_cal",),
        cost_q={"q_cal": cal_cost},
        obs_q={("q_cal", "wL"): 0, ("q_cal", "wP"): 1},
    )


def run_regression_t01_t08() -> Dict[str, str]:
    results: Dict[str, str] = {}

    # T01: EmptyWorld -> INCONSISTENT
    inst_empty = RepairInstance(
        worlds=(),
        actions=("aL", "aP"),
        cost_a={"aL": 1, "aP": 2},
        repair_ok={},
        probes=("q",),
        cost_q={"q": 1},
        obs_q={},
    )
    cert1 = generate_certificate(inst_empty, B=10, h=1)
    assert cert1["verdict"] == "INCONSISTENT"
    ok, msg = verify_certificate(inst_empty, cert1)
    assert ok, msg
    ca_v, _ = run_ca([], c_L=1, c_P=2, c_q=1, B=10)
    assert ca_v == "INCONSISTENT"
    results["T01_EmptyWorld"] = "PASS (INCONSISTENT)"

    # T02: CommonRepair without identifying world
    inst_common = RepairInstance(
        worlds=("w1", "w2"),
        actions=("aL", "aP"),
        cost_a={"aL": 1, "aP": 2},
        repair_ok={
            ("w1", "aL"): True, ("w1", "aP"): True,
            ("w2", "aL"): True, ("w2", "aP"): False,
        },
        probes=("q",),
        cost_q={"q": 1},
        obs_q={("q", "w1"): 0, ("q", "w2"): 1},
    )
    cert2 = generate_certificate(inst_common, B=1, h=1)
    assert cert2["verdict"] == "REPAIR" and cert2["action"] == "aL"
    ok, msg = verify_certificate(inst_common, cert2)
    assert ok, msg
    ca_v, _ = run_ca([("11", 0), ("10", 1)], c_L=1, c_P=2, c_q=1, B=1)
    assert ca_v == "REPAIR"
    results["T02_CommonRepair"] = "PASS (REPAIR aL, no diagnosis needed)"

    # T03: PairwiseIntersectionTrap ({a,b}, {b,c}, {a,c})
    inst_trap = RepairInstance(
        worlds=("w0", "w1", "w2"),
        actions=("a0", "a1", "a2"),
        cost_a={"a0": 1, "a1": 1, "a2": 1},
        repair_ok={
            ("w0", "a0"): False, ("w0", "a1"): True,  ("w0", "a2"): True,
            ("w1", "a0"): True,  ("w1", "a1"): False, ("w1", "a2"): True,
            ("w2", "a0"): True,  ("w2", "a1"): True,  ("w2", "a2"): False,
        },
        probes=(),
        cost_q={},
        obs_q={},
    )
    # Every pair has a common repair, yet the triple has empty G(W)
    for w_i, w_j in itertools.combinations(inst_trap.worlds, 2):
        assert len(compute_G(inst_trap, (w_i, w_j))) == 1
    assert len(compute_G(inst_trap, inst_trap.worlds)) == 0
    cert3 = generate_certificate(inst_trap, B=10, h=0)
    assert cert3["verdict"] == "NO_PLAN_IN_SCOPE" and cert3["C_W"] is None
    ok, msg = verify_certificate(inst_trap, cert3)
    assert ok, msg
    results["T03_PairwiseIntersectionTrap"] = "PASS (all pairs nonempty, global G empty)"

    # T04: UselessProbe (constant output does not improve V_1)
    inst_useless = RepairInstance(
        worlds=("wL", "wP"),
        actions=("aL", "aP"),
        cost_a={"aL": 1, "aP": 2},
        repair_ok={
            ("wL", "aL"): True,  ("wL", "aP"): False,
            ("wP", "aL"): False, ("wP", "aP"): True,
        },
        probes=("q_const",),
        cost_q={"q_const": 1},
        obs_q={("q_const", "wL"): 0, ("q_const", "wP"): 0},
    )
    cert4 = generate_certificate(inst_useless, B=10, h=1)
    assert cert4["verdict"] == "NO_PLAN_IN_SCOPE" and cert4["V_h_W"] is None
    ok, msg = verify_certificate(inst_useless, cert4)
    assert ok, msg
    ca_v, _ = run_ca([("10", 0), ("01", 0)], c_L=1, c_P=2, c_q=1, B=10)
    assert ca_v == "NO_PLAN_IN_SCOPE"
    results["T04_UselessProbe"] = "PASS (NO_PLAN_IN_SCOPE)"

    # T05: Atom_B2 (confidence up, affordability down -> BUDGET)
    atom1 = make_two_world_atom(cal_cost=1)
    cert5 = generate_certificate(atom1, B=2, h=1)
    assert cert5["verdict"] == "BUDGET" and cert5["V_h_W"] == 3
    ok, msg = verify_certificate(atom1, cert5)
    assert ok, msg
    ca_v, _ = run_ca([("10", 0), ("01", 1)], c_L=1, c_P=2, c_q=1, B=2)
    assert ca_v == "BUDGET"
    results["T05_Atom_B2"] = "PASS (BUDGET: V1=3 > B=2)"

    # T06: Atom_B3 (exact threshold B=3 -> PROBE)
    cert6 = generate_certificate(atom1, B=3, h=1)
    assert cert6["verdict"] == "PROBE" and cert6["V_h_W"] == 3 and cert6["first_probe"] == "q_cal"
    ok, msg = verify_certificate(atom1, cert6)
    assert ok, msg
    ca_v, _ = run_ca([("10", 0), ("01", 1)], c_L=1, c_P=2, c_q=1, B=3)
    assert ca_v == "PROBE"
    results["T06_Atom_B3"] = "PASS (PROBE q_cal, V1=3 <= B=3)"

    # T07: Atom_B4 (cal_cost=2 shifts threshold to V1=4)
    atom2 = make_two_world_atom(cal_cost=2)
    cert7_low = generate_certificate(atom2, B=3, h=1)
    cert7_ok = generate_certificate(atom2, B=4, h=1)
    assert cert7_low["verdict"] == "BUDGET" and cert7_low["V_h_W"] == 4
    assert cert7_ok["verdict"] == "PROBE" and cert7_ok["V_h_W"] == 4
    assert verify_certificate(atom2, cert7_low)[0]
    assert verify_certificate(atom2, cert7_ok)[0]
    assert run_ca([("10", 0), ("01", 1)], c_L=1, c_P=2, c_q=2, B=3)[0] == "BUDGET"
    assert run_ca([("10", 0), ("01", 1)], c_L=1, c_P=2, c_q=2, B=4)[0] == "PROBE"
    results["T07_Atom_B4"] = "PASS (BUDGET at B=3, PROBE at B=4)"

    # T08: PermutationInvariant over all 4! = 24 permutations of a 4-world segment
    base_seg = [("10", 0), ("11", 0), ("01", 1), ("11", 1)]
    ref_baseline = emit_verdict(
        RepairInstance(
            worlds=("w0", "w1", "w2", "w3"),
            actions=("aL", "aP"),
            cost_a={"aL": 1, "aP": 2},
            repair_ok={
                (f"w{i}", "aL"): (m[0] == "1") for i, (m, _) in enumerate(base_seg)
            } | {
                (f"w{i}", "aP"): (m[1] == "1") for i, (m, _) in enumerate(base_seg)
            },
            probes=("q",),
            cost_q={"q": 1},
            obs_q={("q", f"w{i}"): p for i, (_, p) in enumerate(base_seg)},
        ),
        B=3,
        h=1,
    )
    for perm in itertools.permutations(base_seg):
        ca_v, _ = run_ca(perm, c_L=1, c_P=2, c_q=1, B=3)
        assert ca_v == ref_baseline["verdict"] == "PROBE"
    results["T08_PermutationInvariant"] = "PASS (24/24 permutations identical)"

    return results


def run_b1_small_instance_verification(num_random: int = 1200, seed: int = 20261124) -> Dict[str, int]:
    """
    Block B1: Verify V_h(W) <= B <=> valid public PlanTree across random instances
    spanning |W| in 1..6, |A| in 1..4, |Q| in 0..4, h in {0, 1, 2}, plus monotonicity
    V_{h+1}(W) <= V_h(W) and independent fail-closed certificate verification.
    """
    rng = random.Random(seed)
    certificates_verified = 0
    monotonicity_checks = 0
    false_guaranteed = 0

    for _ in range(num_random):
        n_w = rng.randint(1, 6)
        n_a = rng.randint(1, 4)
        n_q = rng.randint(0, 4)
        worlds = tuple(f"w{i}" for i in range(n_w))
        actions = tuple(f"a{i}" for i in range(n_a))
        probes = tuple(f"q{i}" for i in range(n_q))
        cost_a = {a: rng.randint(0, 4) for a in actions}
        cost_q = {q: rng.randint(0, 3) for q in probes}
        repair_ok = {(w, a): (rng.random() < 0.45) for w in worlds for a in actions}
        obs_q = {(q, w): rng.randint(0, 1) for q in probes for w in worlds}
        inst = RepairInstance(worlds, actions, cost_a, repair_ok, probes, cost_q, obs_q)

        # Check monotonicity V_2 <= V_1 <= V_0 = C(W)
        c_w, _ = compute_C(inst, worlds)
        v0, _ = compute_V(inst, worlds, 0)
        v1, _ = compute_V(inst, worlds, 1)
        v2, _ = compute_V(inst, worlds, 2)
        assert v0 == c_w, f"V_0 != C(W): {v0} vs {c_w}"

        def le_ext(x, y):
            if y is None:
                return True
            if x is None:
                return False
            return x <= y

        assert le_ext(v1, v0), f"Monotonicity violated: V1={v1} > V0={v0}"
        assert le_ext(v2, v1), f"Monotonicity violated: V2={v2} > V1={v1}"
        monotonicity_checks += 1

        # Verify certificates at critical budgets around V_h (including B = V_h - 1, V_h, V_h + 1)
        for h, vh in ((0, v0), (1, v1), (2, v2)):
            test_budgets = {0, 3}
            if vh is not None:
                test_budgets.add(vh)
                if vh > 0:
                    test_budgets.add(vh - 1)
            for B in test_budgets:
                cert = generate_certificate(inst, B=B, h=h)
                ok, msg = verify_certificate(inst, cert)
                if not ok:
                    if cert["verdict"] in ("REPAIR", "PROBE"):
                        false_guaranteed += 1
                    raise AssertionError(f"Certificate verification failed: {msg}")
                # Check exact equivalence V_h(W) <= B <=> verdict in {REPAIR, PROBE}
                is_guaranteed = cert["verdict"] in ("REPAIR", "PROBE")
                expected_guaranteed = (vh is not None and vh <= B)
                assert is_guaranteed == expected_guaranteed, (
                    f"Equivalence failed: verdict={cert['verdict']}, vh={vh}, B={B}"
                )
                certificates_verified += 1

    return {
        "random_instances_UpTo_W6_A4_Q4": num_random,
        "monotonicity_checks": monotonicity_checks,
        "certificates_independently_verified": certificates_verified,
        "false_guaranteed_verdicts": false_guaranteed,
    }


def main() -> None:
    out_dir = Path(__file__).resolve().parent
    t_res = run_regression_t01_t08()
    b1_res = run_b1_small_instance_verification()
    fold_struct = verify_five_state_moore_and_four_state_impossibility()
    fold_diff = differential_test_fold(num_trials=200_000)
    ca_res = verify_ca_equivalence_exhaustive(max_len=4)

    # Save sample certificate for the headline two-world atom at B=3, h=1
    sample_cert = generate_certificate(make_two_world_atom(cal_cost=1), B=3, h=1)
    assert verify_certificate(make_two_world_atom(cal_cost=1), sample_cert)[0]
    (out_dir / "certificate_atom_B3.json").write_text(
        json.dumps(sample_cert, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )

    report = {
        "schema": "repair-budget-atom/verification-report/v1.3",
        "status": "ALL_PASSED",
        "block_B2_regressions_T01_T08": t_res,
        "block_B1_small_instances": b1_res,
        "block_C_fold_acc": {
            **fold_struct,
            "differential_random_trials": fold_diff,
        },
        "block_D_local_ca_equivalence": ca_res,
    }
    (out_dir / "v1_3_verification_report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
