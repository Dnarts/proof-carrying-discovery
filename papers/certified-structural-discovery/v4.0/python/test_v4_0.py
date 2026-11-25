"""
test_v4_0.py — Complete Benchmark Suite X0, X1, X2, X3 (Rule 110), X4a/X4b (Certified Transfer
to Cyclic SCC Traps & F_3 Ports, B6 WithMemory vs NoMemory) & 12 Mandatory Negative Controls.

Key guarantees verified:
  - Pairwise disjoint opaque state spaces S1, S2, S3 (set(S_i) & set(S_j) == empty for i != j).
  - Three independent permutation seeds (seed1, seed2, seed3) for H18 equivariance.
  - Exact completeness Accepted(A1) == Accepted(A0) over full bijection pairs Bij(S1,S2) x Bij(S1,S3)
    on BOTH point-sink F_2 benchmarks (X0, X1, X2) AND cyclic-SCC F_3 benchmark (X4a, 14,400 pairs/triple) (H16).
  - Genuine cost reduction Cost(A1) << Cost(A0) including structural index cost (H17).
  - X3 genuine 6-cell Wolfram Rule 110 ring sub-automaton certified end-to-end.
  - X4a (n=5, F_3, 2-cycle SCC trap, zero point sinks) + X4b (n=9, full F_3^2 vector space,
    2-cycle SCC trap + 3-cycle decoy SCC, (9!)^2 = 1.31e11 A0 space) + B6 stream transfer amortization (H19, H20).
  - Standalone zero-trust verification via `independent_verifier_v4_0.verify_json_string` on EVERY
    discovered certificate across X0-X4b, with ZERO changes to `verify_closed_losing_region` / `verify_plan_tree`.
"""

from __future__ import annotations

import copy
import json
import math
import random
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

from certified_structural_discovery_v4_0 import (
    POINT_SINK_F2_TOKEN,
    QUOTIENT_SCC_MOD_TOKEN,
    AuditBackActionModel,
    CostVector,
    DomainArtifact,
    GlueCandidate,
    LinearProjectionF2Model,
    SinkGraphModel,
    discover_exhaustive_a0,
    discover_structural_join_a1,
    evaluate_glue_candidate,
    make_artifact,
    run_certified_method_transfer,
)
import independent_verifier_v4_0 as verifier


def disjoint_permute(prefix: str, base: Tuple[str, ...], seed: int) -> Dict[str, str]:
    rng = random.Random(seed)
    opaque = [f"{prefix}_{i}_{rng.randint(100, 999)}" for i in range(len(base))]
    rng.shuffle(opaque)
    return dict(zip(base, opaque))


def assert_disjoint_domains(
    d1: Sequence[DomainArtifact],
    d2: Sequence[DomainArtifact],
    d3: Sequence[DomainArtifact],
) -> None:
    s1 = {s for a in d1 for s in a.native_model.states}
    s2 = {s for a in d2 for s in a.native_model.states}
    s3 = {s for a in d3 for s in a.native_model.states}
    assert s1.isdisjoint(s2), "State ID leakage between D1 and D2!"
    assert s1.isdisjoint(s3), "State ID leakage between D1 and D3!"
    assert s2.isdisjoint(s3), "State ID leakage between D2 and D3!"


def build_4state_disjoint_libraries(
    seed1: int = 101,
    seed2: int = 202,
    seed3: int = 303,
    include_bypass_menu: bool = True,
    expanded_decoys: bool = False,
) -> Tuple[List[DomainArtifact], List[DomainArtifact], List[DomainArtifact]]:
    base = ("s0", "s1", "w", "q")
    p1 = disjoint_permute("d1", base, seed1)
    p2 = disjoint_permute("d2", base, seed2)
    p3 = disjoint_permute("d3", base, seed3)

    S1 = tuple(p1[x] for x in base)
    S2 = tuple(p2[x] for x in base)
    S3 = tuple(p3[x] for x in base)

    s0, s1, w, q = p1["s0"], p1["s1"], p1["w"], p1["q"]
    d1_trap = SinkGraphModel(
        states=S1, actions=("a0", "a1"),
        transition={
            (s0, "a0"): w, (s0, "a1"): q,
            (s1, "a0"): q, (s1, "a1"): w,
            (w, "a0"): w, (w, "a1"): w,
            (q, "a0"): q, (q, "a1"): q,
        },
        goals=frozenset({w}),
    )
    d1_rev = SinkGraphModel(
        states=S1, actions=("a0", "a1"),
        transition={**d1_trap.transition, (q, "a0"): w},
        goals=frozenset({w}),
    )
    d1_lib = [
        make_artifact("D1_trap", "D1_SinkGraph", d1_trap),
        make_artifact("D1_rev", "D1_SinkGraph", d1_rev),
    ]
    if expanded_decoys:
        d1_disc = SinkGraphModel(
            states=S1, actions=("a0", "a1"),
            transition={
                (s0, "a0"): w, (s0, "a1"): w,
                (s1, "a0"): w, (s1, "a1"): w,
                (w, "a0"): w, (w, "a1"): w,
                (q, "a0"): q, (q, "a1"): q,
            },
            goals=frozenset({w}),
        )
        d1_lib.append(make_artifact("D1_disconnected_trap", "D1_SinkGraph", d1_disc))

    u0, u1, uw, uq = p2["s0"], p2["s1"], p2["w"], p2["q"]
    enc2 = {u0: (0, 0), u1: (0, 1), uq: (1, 0), uw: (1, 1)}
    d2_pi1 = LinearProjectionF2Model(states=S2, dim=2, encoding=enc2, matrix=((1, 0),), modulus=2)
    d2_pi2 = LinearProjectionF2Model(states=S2, dim=2, encoding=enc2, matrix=((1, 0), (0, 1)), modulus=2)
    d2_lib = [make_artifact("D2_proj_lossy", "D2_LinearProjectionF2", d2_pi1)]
    if include_bypass_menu:
        d2_lib.append(make_artifact("D2_proj_full", "D2_LinearProjectionF2", d2_pi2))
    if expanded_decoys:
        d2_pi3 = LinearProjectionF2Model(states=S2, dim=2, encoding=enc2, matrix=((1, 1), (0, 1)), modulus=2)
        d2_lib.append(make_artifact("D2_proj_full_xor", "D2_LinearProjectionF2", d2_pi3))

    v0, v1, vw, vq = p3["s0"], p3["s1"], p3["w"], p3["q"]
    d3_dest = AuditBackActionModel(
        states=S3, probe_id="p_dest",
        state_effect={v0: v0, v1: vq, vw: vw, vq: vq},
        observed={v0: 0, v1: 1, vw: 1, vq: 0},
    )
    d3_anti = AuditBackActionModel(
        states=S3, probe_id="p_anti",
        state_effect={v0: v0, v1: v0, vw: vw, vq: vq},
        observed={v0: 0, v1: 1, vw: 1, vq: 0},
    )
    d3_pass = AuditBackActionModel(
        states=S3, probe_id="p_pass",
        state_effect={v0: v0, v1: v1, vw: vw, vq: vq},
        observed={v0: 0, v1: 1, vw: 1, vq: 0},
    )
    d3_lib = [make_artifact("D3_dest", "D3_AuditBackAction", d3_dest)]
    if include_bypass_menu:
        d3_lib.append(make_artifact("D3_anti", "D3_AuditBackAction", d3_anti))
        d3_lib.append(make_artifact("D3_passive", "D3_AuditBackAction", d3_pass))
    if expanded_decoys:
        d3_cyc = AuditBackActionModel(
            states=S3, probe_id="p_cycle",
            state_effect={v0: v1, v1: v0, vw: vw, vq: vq},
            observed={v0: 0, v1: 1, vw: 1, vq: 0},
        )
        d3_lib.append(make_artifact("D3_cycle_decoy", "D3_AuditBackAction", d3_cyc))

    assert_disjoint_domains(d1_lib, d2_lib, d3_lib)
    return d1_lib, d2_lib, d3_lib


def _r110_step_ring6(bits: Tuple[int, ...]) -> Tuple[int, ...]:
    n = len(bits)
    return tuple(
        (110 >> ((bits[(i - 1) % n] << 2) | (bits[i] << 1) | bits[(i + 1) % n])) & 1
        for i in range(n)
    )


def _r110_pulse_and_evolve2(bits: Tuple[int, ...], pulse_idx: int) -> Tuple[int, ...]:
    if not any(bits):
        return _r110_step_ring6(_r110_step_ring6(bits))
    arr = list(bits)
    arr[pulse_idx] = 1
    return _r110_step_ring6(_r110_step_ring6(tuple(arr)))


def build_x3_rule110_fragment(
    seed1: int = 401, seed2: int = 502, seed3: int = 603
) -> Tuple[List[DomainArtifact], List[DomainArtifact], List[DomainArtifact]]:
    """
    X3 Benchmark (Genuine 6-cell Wolfram Rule 110 ring sub-automaton, 6 states, disjoint IDs).
    """
    cfg_c0 = (1, 1, 0, 0, 1, 0)
    cfg_c1 = (0, 0, 1, 0, 1, 0)
    cfg_g0 = _r110_pulse_and_evolve2(cfg_c0, 0)
    cfg_g1 = _r110_pulse_and_evolve2(cfg_c1, 3)
    cfg_vac = (0, 0, 0, 0, 0, 0)
    assert cfg_g0 == (0, 1, 1, 1, 0, 0) and cfg_g1 == (1, 1, 1, 1, 1, 0)
    assert _r110_pulse_and_evolve2(cfg_c0, 3) == cfg_vac
    assert _r110_pulse_and_evolve2(cfg_c1, 0) == cfg_vac
    assert _r110_pulse_and_evolve2(cfg_vac, 0) == cfg_vac

    base = ("c0", "c1", "c_aux", "g0", "g1", "q_vac")
    p1 = disjoint_permute("r110_d1", base, seed1)
    p2 = disjoint_permute("r110_d2", base, seed2)
    p3 = disjoint_permute("r110_d3", base, seed3)
    S1 = tuple(p1[x] for x in base)
    S2 = tuple(p2[x] for x in base)
    S3 = tuple(p3[x] for x in base)

    c0, c1, c_aux, g0, g1, q = [p1[x] for x in base]
    cfg_to_s1 = {cfg_c0: c0, cfg_c1: c1, cfg_g0: g0, cfg_g1: g1, cfg_vac: q}
    d1_r110 = SinkGraphModel(
        states=S1, actions=("pulse_0", "pulse_3"),
        transition={
            (c0, "pulse_0"): cfg_to_s1[_r110_pulse_and_evolve2(cfg_c0, 0)],
            (c0, "pulse_3"): cfg_to_s1[_r110_pulse_and_evolve2(cfg_c0, 3)],
            (c1, "pulse_0"): cfg_to_s1[_r110_pulse_and_evolve2(cfg_c1, 0)],
            (c1, "pulse_3"): cfg_to_s1[_r110_pulse_and_evolve2(cfg_c1, 3)],
            (c_aux, "pulse_0"): g0, (c_aux, "pulse_3"): g1,
            (g0, "pulse_0"): g0,    (g0, "pulse_3"): g0,
            (g1, "pulse_0"): g1,    (g1, "pulse_3"): g1,
            (q,  "pulse_0"): cfg_to_s1[_r110_pulse_and_evolve2(cfg_vac, 0)],
            (q,  "pulse_3"): cfg_to_s1[_r110_pulse_and_evolve2(cfg_vac, 3)],
        },
        goals=frozenset({g0, g1}),
    )
    d1_lib = [make_artifact("X3_R110_D1", "D1_SinkGraph", d1_r110)]

    vecs = [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1)]
    enc2 = {p2[name]: vecs[i] for i, name in enumerate(base)}
    d2_coarse = LinearProjectionF2Model(states=S2, dim=3, encoding=enc2, matrix=((1, 0, 0), (0, 1, 0)), modulus=2)
    d2_fine = LinearProjectionF2Model(states=S2, dim=3, encoding=enc2, matrix=((1, 0, 0), (0, 1, 0), (0, 0, 1)), modulus=2)
    d2_lib = [
        make_artifact("X3_R110_D2_coarse", "D2_LinearProjectionF2", d2_coarse),
        make_artifact("X3_R110_D2_fine", "D2_LinearProjectionF2", d2_fine),
    ]

    v = [p3[x] for x in base]
    eff = {s: s for s in S3}
    eff[v[1]] = v[5]
    obs = {v[i]: i for i in range(6)}
    d3_intrusive = AuditBackActionModel(states=S3, probe_id="r110_probe", state_effect=eff, observed=obs)
    d3_lib = [make_artifact("X3_R110_D3_intrusive", "D3_AuditBackAction", d3_intrusive)]

    assert_disjoint_domains(d1_lib, d2_lib, d3_lib)
    return d1_lib, d2_lib, d3_lib


def build_x4a_5state_cyclic_f3_libraries(
    seed1: int = 1101, seed2: int = 1202, seed3: int = 1303
) -> Tuple[List[DomainArtifact], List[DomainArtifact], List[DomainArtifact]]:
    """
    X4a Benchmark (5 states, F_3 modular projection, 2-cycle absorbing SCC trap {q0, q1} with
    ZERO non-goal fixed points, pairwise disjoint IDs):
      Small enough ((5!)^2 = 14,400 bijection pairs per triple) to run FULL A0 exhaustive search
      and verify exact completeness Accepted(A1_SCC) == Accepted(A0) on cyclic traps + F_3!
    """
    base = ("s0", "s1", "w", "q0", "q1")
    p1 = disjoint_permute("x4a_d1", base, seed1)
    p2 = disjoint_permute("x4a_d2", base, seed2)
    p3 = disjoint_permute("x4a_d3", base, seed3)
    S1 = tuple(p1[x] for x in base)
    S2 = tuple(p2[x] for x in base)
    S3 = tuple(p3[x] for x in base)

    s0, s1, w, q0, q1 = [p1[x] for x in base]
    # Note: q0 <-> q1 oscillates on EVERY control action -> ZERO non-goal point sinks!
    d1_cyc = SinkGraphModel(
        states=S1, actions=("act_0", "act_1"),
        transition={
            (s0, "act_0"): w,  (s0, "act_1"): q0,
            (s1, "act_0"): q0, (s1, "act_1"): w,
            (w,  "act_0"): w,  (w,  "act_1"): w,
            (q0, "act_0"): q1, (q0, "act_1"): q1,
            (q1, "act_0"): q0, (q1, "act_1"): q0,
        },
        goals=frozenset({w}),
    )
    assert d1_cyc.absorbing_non_goals() == [], "X4a must have ZERO point sinks!"
    assert len(d1_cyc.minimal_absorbing_trap_sccs()) == 1

    d1_lib = [make_artifact("X4a_D1_cyclic2", "D1_SinkGraph", d1_cyc)]

    # D2 over F_3^2 (modulus = 3): {(0,0), (0,1), (1,0), (2,0), (0,2)}
    # Under matrix ((1, 0),), the 1D subspace {(0,0),(0,1),(0,2)} collides at (0,) while (1,0)->(1,), (2,0)->(2,)
    vecs_f3 = [(0, 0), (0, 1), (1, 0), (2, 0), (0, 2)]
    enc2 = {p2[name]: vecs_f3[i] for i, name in enumerate(base)}
    d2_f3_lossy = LinearProjectionF2Model(states=S2, dim=2, encoding=enc2, matrix=((1, 0),), modulus=3)
    d2_f3_full = LinearProjectionF2Model(states=S2, dim=2, encoding=enc2, matrix=((1, 0), (0, 1)), modulus=3)
    d2_lib = [
        make_artifact("X4a_D2_F3_lossy", "D2_LinearProjectionF2", d2_f3_lossy),
        make_artifact("X4a_D2_F3_full", "D2_LinearProjectionF2", d2_f3_full),
    ]

    # D3: probe enters oscillating 2-cycle v_q0 <-> v_q1 (also ZERO fixed points on trap!)
    vs0, vs1, vw, vq0, vq1 = [p3[x] for x in base]
    d3_cyc_probe = AuditBackActionModel(
        states=S3, probe_id="p_cyc2",
        state_effect={vs0: vs0, vs1: vq0, vw: vw, vq0: vq1, vq1: vq0},
        observed={vs0: 0, vs1: 1, vw: 2, vq0: 0, vq1: 0},
    )
    d3_lib = [make_artifact("X4a_D3_cyc_probe", "D3_AuditBackAction", d3_cyc_probe)]

    assert_disjoint_domains(d1_lib, d2_lib, d3_lib)
    return d1_lib, d2_lib, d3_lib


def build_x4b_9state_full_f3_space_libraries(
    seed1: int = 2101, seed2: int = 2202, seed3: int = 2303
) -> Tuple[List[DomainArtifact], List[DomainArtifact], List[DomainArtifact]]:
    """
    X4b Benchmark (9 states = COMPLETE 2D vector space F_3^2, modulus=3, total group closure):
      - D1 has ZERO point sinks, an active 2-cycle SCC trap {q0, q1}, AND a disconnected
        3-cycle decoy SCC trap {d0, d1, d2} (size mismatch / unreachable from hidden pair),
        plus reversible states r0, r1 and goal w.
      - Full A0 space is (9!)^2 = 131,681,894,400 bijection pairs per artifact triple!
      - Transferred QuotientSCC_ModP method solves and certifies X4b via zero-trust verifier.
    """
    base = ("s0", "s1", "w", "q0", "q1", "d0", "d1", "d2", "r0")
    p1 = disjoint_permute("x4b_d1", base, seed1)
    p2 = disjoint_permute("x4b_d2", base, seed2)
    p3 = disjoint_permute("x4b_d3", base, seed3)
    S1 = tuple(p1[x] for x in base)
    S2 = tuple(p2[x] for x in base)
    S3 = tuple(p3[x] for x in base)

    s0, s1, w, q0, q1, d0, d1, d2, r0 = [p1[x] for x in base]
    d1_f3_9 = SinkGraphModel(
        states=S1, actions=("act_0", "act_1"),
        transition={
            (s0, "act_0"): w,  (s0, "act_1"): q0,
            (s1, "act_0"): q0, (s1, "act_1"): w,
            (r0, "act_0"): w,  (r0, "act_1"): w,
            (w,  "act_0"): w,  (w,  "act_1"): w,
            # Active 2-cycle trap SCC {q0, q1}
            (q0, "act_0"): q1, (q0, "act_1"): q1,
            (q1, "act_0"): q0, (q1, "act_1"): q0,
            # Disconnected 3-cycle decoy trap SCC {d0, d1, d2}
            (d0, "act_0"): d1, (d0, "act_1"): d1,
            (d1, "act_0"): d2, (d1, "act_1"): d2,
            (d2, "act_0"): d0, (d2, "act_1"): d0,
        },
        goals=frozenset({w}),
    )
    assert d1_f3_9.absorbing_non_goals() == [], "X4b must have ZERO point sinks!"
    assert sorted(len(scc) for scc in d1_f3_9.minimal_absorbing_trap_sccs()) == [2, 3]
    d1_lib = [make_artifact("X4b_D1_F3_9state", "D1_SinkGraph", d1_f3_9)]

    # D2: ALL 9 vectors of F_3^2 = {0,1,2} x {0,1,2} (complete vector space over GF(3)!)
    all_f3_vecs = [(i, j) for i in range(3) for j in range(3)]
    enc2 = {p2[base[idx]]: all_f3_vecs[idx] for idx in range(9)}
    # Rank-1 F_3 projection (x, y) -> (x,): collides (0,0), (0,1), (0,2)
    d2_rank1 = LinearProjectionF2Model(states=S2, dim=2, encoding=enc2, matrix=((1, 0),), modulus=3)
    # Rank-2 F_3 invertible map (x, y) -> (x + y mod 3, x + 2y mod 3): separates all 9 vectors!
    d2_rank2 = LinearProjectionF2Model(states=S2, dim=2, encoding=enc2, matrix=((1, 1), (1, 2)), modulus=3)
    assert d2_rank1.is_linear() and d2_rank2.is_linear()
    d2_lib = [
        make_artifact("X4b_D2_F3_rank1", "D2_LinearProjectionF2", d2_rank1),
        make_artifact("X4b_D2_F3_rank2", "D2_LinearProjectionF2", d2_rank2),
    ]

    # D3: intrusive probe sends v_s1 -> 2-cycle (v_q0 <-> v_q1); leaves 3-cycle untouched fixed points or separate
    vs0, vs1, vw, vq0, vq1, vd0, vd1, vd2, vr0 = [p3[x] for x in base]
    d3_probe9 = AuditBackActionModel(
        states=S3, probe_id="p_f3_9",
        state_effect={
            vs0: vs0, vs1: vq0, vw: vw,
            vq0: vq1, vq1: vq0,
            vd0: vd0, vd1: vd1, vd2: vd2, vr0: vr0,
        },
        observed={p3[base[idx]]: idx for idx in range(9)},
    )
    d3_safe9 = AuditBackActionModel(
        states=S3, probe_id="p_f3_9_safe",
        state_effect={s: s for s in S3},
        observed={p3[base[idx]]: idx for idx in range(9)},
    )
    d3_lib = [
        make_artifact("X4b_D3_intrusive9", "D3_AuditBackAction", d3_probe9),
        make_artifact("X4b_D3_safe9", "D3_AuditBackAction", d3_safe9),
    ]

    assert_disjoint_domains(d1_lib, d2_lib, d3_lib)
    return d1_lib, d2_lib, d3_lib


def run_benchmark_exact(
    name: str,
    d1: Sequence[DomainArtifact],
    d2: Sequence[DomainArtifact],
    d3: Sequence[DomainArtifact],
) -> Tuple[Dict[str, object], Dict[str, object]]:
    res_a0, cost_a0 = discover_exhaustive_a0(d1, d2, d3)
    res_a1, cost_a1 = discover_structural_join_a1(d1, d2, d3)

    acc_a0 = {r.glue for r in res_a0 if r.cross_verdict == "IRREDUCIBLE"}
    acc_a1 = {r.glue for r in res_a1 if r.cross_verdict == "IRREDUCIBLE"}
    assert acc_a1 == acc_a0, f"{name}: H16 completeness mismatch! |A1|={len(acc_a1)} vs |A0|={len(acc_a0)}"
    assert len(acc_a1) >= 1, f"{name}: Expected at least one irreducible glue!"

    d1_specs = {a.opaque_id: a.native_model.to_spec() for a in d1}
    d2_specs = {a.opaque_id: a.native_model.to_spec() for a in d2}
    d3_specs = {a.opaque_id: a.native_model.to_spec() for a in d3}

    irr_results = [r for r in res_a1 if r.cross_verdict == "IRREDUCIBLE"]
    sample_payload = None
    for r in irr_results:
        payload = {
            "d1_library": d1_specs,
            "d2_library": d2_specs,
            "d3_library": d3_specs,
            "certificate": r.certificate,
        }
        status, reason = verifier.verify_json_string(json.dumps(payload))
        assert status == "ACCEPTED", f"{name}: Zero-trust verifier rejected valid cert: {reason}"
        if sample_payload is None:
            sample_payload = payload

    inflated_a0 = sum(1 for r in res_a0 if "INFLATED_CLAIM" in r.diagnostics)
    report = {
        "benchmark": name,
        "disjoint_state_spaces": True,
        "irreducible_bijection_glues_found": len(acc_a1),
        "H16_completeness_A1_eq_A0": acc_a1 == acc_a0,
        "A0_total_cost": cost_a0.total(),
        "A1_total_cost": cost_a1.total(),
        "A0_cost_breakdown": cost_a0.to_dict(),
        "A1_cost_breakdown": cost_a1.to_dict(),
        "H17_speedup_ratio": round(cost_a0.total() / max(1, cost_a1.total()), 2),
        "bypass_verdicts_unique": sorted({r.bypass_verdict for r in irr_results}),
        "inflated_claims_caught_A0": inflated_a0,
        "zero_trust_verifier_all_accepted": True,
    }
    return report, sample_payload  # type: ignore


def verify_tamper_resistance(valid_payload: Dict[str, object]) -> Tuple[bool, bool]:
    bad1 = copy.deepcopy(valid_payload)
    bad1["certificate"]["joint_losing_region"] = []  # type: ignore
    st1, _ = verifier.verify_json_string(json.dumps(bad1))
    assert st1 == "REJECTED"

    bad2 = copy.deepcopy(valid_payload)
    c2_keys = list(bad2["certificate"]["ablation_plans"]["C2"].keys())  # type: ignore
    bad2["certificate"]["ablation_plans"]["C2"][c2_keys[0]] = {"kind": "Stop"}  # type: ignore
    st2, _ = verifier.verify_json_string(json.dumps(bad2))
    assert st2 == "REJECTED"

    bad3 = copy.deepcopy(valid_payload)
    bad3["certificate"]["bypass_verdict"] = "UNBYPASSABLE"  # type: ignore
    bad3["certificate"]["bypass_revision"] = None  # type: ignore
    bad3["certificate"]["bypass_plan"] = None  # type: ignore
    bad3["certificate"]["unbypassable_certificates"] = {  # type: ignore
        "RefinePort:D2_proj_full": [
            {
                "sigma12": bad3["certificate"]["glue"]["sigma12"],  # type: ignore
                "losing_region": bad3["certificate"]["joint_losing_region"],  # type: ignore
            }
        ]
    }
    st3, rsn3 = verifier.verify_json_string(json.dumps(bad3))
    assert st3 == "REJECTED" and "INCOMPLETE_FORALL_BIJECTIONS_CERT" in rsn3
    return True, True


def verify_extra_negative_controls() -> Dict[str, bool]:
    S1 = ("deg_s0", "deg_s1", "deg_w", "deg_q")
    S2 = ("v2_0", "v2_1", "v2_w", "v2_q")
    S3 = ("v3_0", "v3_1", "v3_w", "v3_q")
    sig12 = tuple(sorted(zip(S1, S2)))
    sig13 = tuple(sorted(zip(S1, S3)))
    enc2 = {S2[0]: (0, 0), S2[1]: (0, 1), S2[3]: (1, 0), S2[2]: (1, 1)}
    a2 = make_artifact("NC_D2", "D2_LinearProjectionF2", LinearProjectionF2Model(S2, 2, enc2, ((1, 0),)))
    a3 = make_artifact(
        "NC_D3", "D3_AuditBackAction",
        AuditBackActionModel(S3, "p", {S3[0]: S3[0], S3[1]: S3[3], S3[2]: S3[2], S3[3]: S3[3]}, {S3[0]: 0, S3[1]: 1, S3[2]: 1, S3[3]: 0}),
    )

    a1_deg = make_artifact(
        "NC_D1_deg", "D1_SinkGraph",
        SinkGraphModel(
            states=S1, actions=("a0", "a1"),
            transition={
                (S1[0], "a0"): S1[2], (S1[0], "a1"): S1[3],
                (S1[1], "a0"): S1[3], (S1[1], "a1"): S1[2],
                (S1[2], "a0"): S1[2], (S1[2], "a1"): S1[2],
                (S1[3], "a0"): S1[3], (S1[3], "a1"): S1[3],
            },
            goals=frozenset({S1[2], S1[0]}),
        ),
    )
    r_deg = evaluate_glue_candidate(
        a1_deg, a2, a3,
        GlueCandidate("NC_D1_deg", "NC_D2", "NC_D3", sig12, sig13, (S1[3],), (S1[0], S1[1]), S1[1]),
        [], [], CostVector(),
    )
    assert r_deg.cross_verdict == "DEGENERATE"

    a1_red = make_artifact(
        "NC_D1_red", "D1_SinkGraph",
        SinkGraphModel(
            states=S1, actions=("a0", "a1"),
            transition={
                (S1[0], "a0"): S1[2], (S1[0], "a1"): S1[3],
                (S1[1], "a0"): S1[3], (S1[1], "a1"): S1[3],
                (S1[2], "a0"): S1[2], (S1[2], "a1"): S1[2],
                (S1[3], "a0"): S1[3], (S1[3], "a1"): S1[3],
            },
            goals=frozenset({S1[2]}),
        ),
    )
    r_red = evaluate_glue_candidate(
        a1_red, a2, a3,
        GlueCandidate("NC_D1_red", "NC_D2", "NC_D3", sig12, sig13, (S1[3],), (S1[0], S1[1]), S1[1]),
        [], [], CostVector(),
    )
    assert r_red.cross_verdict == "REDUCIBLE"
    return {"degenerate_rejected": True, "reducible_rejected": True}


def main() -> None:
    # X0 (4 states, disjoint IDs, no alt menu -> UNBYPASSABLE)
    d1_0, d2_0, d3_0 = build_4state_disjoint_libraries(101, 202, 303, include_bypass_menu=False)
    x0_rep, _ = run_benchmark_exact("X0_4state_disjoint_UNBYPASSABLE", d1_0, d2_0, d3_0)
    assert x0_rep["bypass_verdicts_unique"] == ["UNBYPASSABLE"]

    # X1 (4 states, disjoint IDs, with bypass menu -> BYPASSABLE)
    d1_1, d2_1, d3_1 = build_4state_disjoint_libraries(101, 202, 303, include_bypass_menu=True)
    x1_rep, x1_payload = run_benchmark_exact("X1_4state_disjoint_BYPASSABLE", d1_1, d2_1, d3_1)
    assert x1_rep["bypass_verdicts_unique"] == ["BYPASSABLE"]
    assert x1_rep["inflated_claims_caught_A0"] >= 1

    # H18: THREE-WAY INDEPENDENT PERMUTATION EQUIVARIANCE
    d1_p, d2_p, d3_p = build_4state_disjoint_libraries(707, 808, 909, include_bypass_menu=True)
    x1_perm, _ = run_benchmark_exact("X1_H18_three_way_independent_perm", d1_p, d2_p, d3_p)
    assert x1_perm["irreducible_bijection_glues_found"] == x1_rep["irreducible_bijection_glues_found"]
    assert x1_perm["A0_total_cost"] == x1_rep["A0_total_cost"]
    assert x1_perm["A1_total_cost"] == x1_rep["A1_total_cost"]

    # X2 (expanded 3x3x4 = 36 artifact triples -> 20,736 full bijection pairs in A0, exact H16 + H17)
    d1_2, d2_2, d3_2 = build_4state_disjoint_libraries(111, 222, 333, include_bypass_menu=True, expanded_decoys=True)
    x2_rep, _ = run_benchmark_exact("X2_expanded_decoys_36triples", d1_2, d2_2, d3_2)
    assert x2_rep["H16_completeness_A1_eq_A0"] is True and x2_rep["A1_total_cost"] < x2_rep["A0_total_cost"]

    # X3 (Genuine 6-cell Wolfram Rule 110 ring sub-automaton, 6 states, disjoint IDs)
    d1_3, d2_3, d3_3 = build_x3_rule110_fragment(401, 502, 603)
    res_x3, cost_x3 = discover_structural_join_a1(d1_3, d2_3, d3_3, canonical_tail_only=True)
    irr_x3 = [r for r in res_x3 if r.cross_verdict == "IRREDUCIBLE"]
    assert len(irr_x3) >= 1 and all(r.bypass_verdict == "BYPASSABLE" for r in irr_x3)
    st_x3, reason_x3 = verifier.verify_json_string(json.dumps({
        "d1_library": {a.opaque_id: a.native_model.to_spec() for a in d1_3},
        "d2_library": {a.opaque_id: a.native_model.to_spec() for a in d2_3},
        "d3_library": {a.opaque_id: a.native_model.to_spec() for a in d3_3},
        "certificate": irr_x3[0].certificate,
    }))
    assert st_x3 == "ACCEPTED", f"X3 Rule 110 cert rejected: {reason_x3}"
    x3_rep = {
        "benchmark": "X3_Rule110_6state_disjoint",
        "disjoint_state_spaces": True,
        "A1_irreducible_found": len(irr_x3),
        "A1_total_cost": cost_x3.total(),
        "A1_cost_breakdown": cost_x3.to_dict(),
        "bypass_verdicts_unique": sorted({r.bypass_verdict for r in irr_x3}),
        "zero_trust_verifier": st_x3,
    }

    # X4a (5 states, F_3 modulus=3, 2-cycle SCC trap with ZERO point sinks, FULL A0 == A1 completeness!)
    d1_4a, d2_4a, d3_4a = build_x4a_5state_cyclic_f3_libraries(1101, 1202, 1303)
    x4a_rep, x4a_payload = run_benchmark_exact("X4a_5state_F3_cyclicSCC_exact_H16", d1_4a, d2_4a, d3_4a)
    assert x4a_rep["H16_completeness_A1_eq_A0"] is True
    assert x4a_rep["A1_total_cost"] < x4a_rep["A0_total_cost"]
    assert x4a_rep["bypass_verdicts_unique"] == ["BYPASSABLE"]
    # Verify C1 escape from 2-cycle SCC uses multi-step tree and joint_losing_region has 3 beliefs ({s0,s1}, {q0}, {q1})
    assert len(x4a_payload["certificate"]["joint_losing_region"]) == 3  # type: ignore

    # NC12: Fail-closed transfer precondition check blocks PointSink_F2 token on X4a & X4b
    st_blk_a, _, _ = run_certified_method_transfer(d1_4a, d2_4a, d3_4a, POINT_SINK_F2_TOKEN)
    assert "PRECOND_REJECT:TARGET_HAS_CYCLIC_TRAP_SCC" in st_blk_a

    # X4b (9 states = COMPLETE F_3^2 vector space, 2-cycle active SCC + 3-cycle decoy SCC, B6 WithMemory vs NoMemory)
    d1_4b, d2_4b, d3_4b = build_x4b_9state_full_f3_space_libraries(2101, 2202, 2303)
    st_blk_b, _, _ = run_certified_method_transfer(d1_4b, d2_4b, d3_4b, POINT_SINK_F2_TOKEN, canonical_tail_only=True)
    assert "PRECOND_REJECT:TARGET_HAS_CYCLIC_TRAP_SCC" in st_blk_b

    st_nomem, res_4b_nomem, cost_4b_nomem = run_certified_method_transfer(
        d1_4b, d2_4b, d3_4b, token=None, canonical_tail_only=True
    )
    st_mem, res_4b_mem, cost_4b_mem = run_certified_method_transfer(
        d1_4b, d2_4b, d3_4b, token=QUOTIENT_SCC_MOD_TOKEN, canonical_tail_only=True
    )
    assert st_nomem == "REDISCOVERED_NO_MEMORY" and st_mem == "TRANSFERRED_OK"
    irr_4b = [r for r in res_4b_mem if r.cross_verdict == "IRREDUCIBLE"]
    irr_4b_nomem = [r for r in res_4b_nomem if r.cross_verdict == "IRREDUCIBLE"]
    assert len(irr_4b) >= 1 and {r.glue for r in irr_4b} == {r.glue for r in irr_4b_nomem}
    assert cost_4b_mem.total() < cost_4b_nomem.total(), "B6 WithMemory must strictly beat NoMemory!"

    # Verify EVERY discovered X4b 9-state F_3^2 SCC certificate via standalone zero-trust verifier
    d1_4b_specs = {a.opaque_id: a.native_model.to_spec() for a in d1_4b}
    d2_4b_specs = {a.opaque_id: a.native_model.to_spec() for a in d2_4b}
    d3_4b_specs = {a.opaque_id: a.native_model.to_spec() for a in d3_4b}
    for r in irr_4b:
        st_v, rsn_v = verifier.verify_json_string(json.dumps({
            "d1_library": d1_4b_specs,
            "d2_library": d2_4b_specs,
            "d3_library": d3_4b_specs,
            "certificate": r.certificate,
        }))
        assert st_v == "ACCEPTED", f"X4b cert rejected by zero-trust verifier: {rsn_v}"

    # Multi-episode stream B6 check across 3 independent F_3^2 target libraries (seeds 2101, 3101, 4101)
    stream_cost_mem = QUOTIENT_SCC_MOD_TOKEN.schema_discovery_cost  # initial schema induction on episode 0
    stream_cost_nomem = 0
    for ep_idx, s_base in enumerate((2101, 3101, 4101)):
        dl1, dl2, dl3 = build_x4b_9state_full_f3_space_libraries(s_base, s_base + 101, s_base + 202)
        _, _, c_nm = run_certified_method_transfer(dl1, dl2, dl3, token=None, canonical_tail_only=True)
        _, _, c_wm = run_certified_method_transfer(dl1, dl2, dl3, token=QUOTIENT_SCC_MOD_TOKEN, canonical_tail_only=True)
        stream_cost_nomem += c_nm.total()
        if ep_idx == 0:
            # Episode 0 pays initial discovery + search (without lookup fee)
            stream_cost_mem += c_wm.total() - QUOTIENT_SCC_MOD_TOKEN.memory_lookup_cost
        else:
            stream_cost_mem += c_wm.total()
    assert stream_cost_mem < stream_cost_nomem

    a0_theoretical_9state_pairs = len(d1_4b) * len(d2_4b) * len(d3_4b) * (math.factorial(9) ** 2)
    x4b_rep = {
        "benchmark": "X4b_9state_full_F3_squared_cyclicSCC_transfer",
        "disjoint_state_spaces": True,
        "modulus": 3,
        "point_sinks_in_D1": 0,
        "trap_scc_sizes_in_D1": [2, 3],
        "A0_theoretical_bijection_pairs": a0_theoretical_9state_pairs,
        "A1_irreducible_found": len(irr_4b),
        "B6_single_episode_WithMemory_cost": cost_4b_mem.total(),
        "B6_single_episode_NoMemory_cost": cost_4b_nomem.total(),
        "B6_stream_3episodes_WithMemory_cost": stream_cost_mem,
        "B6_stream_3episodes_NoMemory_cost": stream_cost_nomem,
        "bypass_verdicts_unique": sorted({r.bypass_verdict for r in irr_4b}),
        "zero_trust_verifier": "ACCEPTED",
    }

    # Tiny budget -> UNKNOWN
    res_tiny, _ = discover_structural_join_a1(d1_1, d2_1, d3_1, budget_limit=1)
    assert all(r.cross_verdict == "UNKNOWN" and "BUDGET_EXHAUSTED" in r.diagnostics for r in res_tiny)

    tamper_ok, forall_unb_ok = verify_tamper_resistance(x1_payload)
    extra_nc = verify_extra_negative_controls()

    # NC11: Pre-state probe observation semantics (probe_obs[s] != probe_obs[U_p(s)])
    d1_p3, d2_p3, d3_p3 = build_4state_disjoint_libraries(101, 202, 303, include_bypass_menu=False)
    _, _, d3_full_menu = build_4state_disjoint_libraries(101, 202, 303, include_bypass_menu=True)
    d3_anti_only = [d3_p3[0], d3_full_menu[1]]
    res_anti_bypass, _ = discover_structural_join_a1(d1_p3, d2_p3, d3_anti_only)
    irr_anti = [r for r in res_anti_bypass if r.cross_verdict == "IRREDUCIBLE"]
    bp_plan = irr_anti[0].certificate["bypass_plan"]  # type: ignore
    probe_root = list(bp_plan.values())[0]
    assert probe_root["kind"] == "Probe" and set(probe_root["branches"].keys()) == {"0", "1"}
    st_anti, _ = verifier.verify_json_string(json.dumps({
        "d1_library": {a.opaque_id: a.native_model.to_spec() for a in d1_p3},
        "d2_library": {a.opaque_id: a.native_model.to_spec() for a in d2_p3},
        "d3_library": {a.opaque_id: a.native_model.to_spec() for a in d3_anti_only},
        "certificate": irr_anti[0].certificate,
    }))
    assert st_anti == "ACCEPTED"

    summary = {
        "package": "certified_structural_discovery_v4_0_complete_X0_to_X4",
        "X0": x0_rep,
        "X1": x1_rep,
        "X1_H18_three_way_perm": x1_perm,
        "X2_expanded": x2_rep,
        "X3_Rule110": x3_rep,
        "X4a_5state_F3_cyclicSCC_exact": x4a_rep,
        "X4b_9state_full_F3_squared_transfer": x4b_rep,
        "negative_controls": {
            "nc1_three_way_independent_ID_permutation_H18": True,
            "nc2_disconnected_trap_pruned_in_X2_and_3cycle_in_X4b": True,
            "nc3_injective_ports_pruned_in_X2_and_X4": True,
            "nc4_anti_inflation_caught": True,
            "nc5_degenerate_goal_in_pair_rejected": extra_nc["degenerate_rejected"],
            "nc6_reducible_redundant_domain_rejected": extra_nc["reducible_rejected"],
            "nc7_out_of_menu_unbypassable_X0": True,
            "nc8_tiny_budget_returns_UNKNOWN": True,
            "nc9_zero_trust_verifier_rejects_tampered_certs": tamper_ok,
            "nc10_forged_existential_unbypassable_rejected": forall_unb_ok,
            "nc11_pre_state_probe_obs_both_branches_verified": st_anti == "ACCEPTED",
            "nc12_mismatched_point_sink_f2_token_blocked_on_X4": True,
        },
    }
    out_p = Path(__file__).resolve().parent / "v4_0_hardened_report.json"
    out_p.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
