"""
independent_verifier_v4_0.py — Zero-Trust Standalone Verifier for Certified Structural Discovery (v4.0).

STRICT ISOLATION GUARANTEE:
  - Imports ONLY Python standard library modules (no imports from any discovery or search module).
  - Performs ZERO search, ZERO fixed-point iteration, and ZERO candidate enumeration.
  - Verifies serialized JSON DiscoveryCertificates strictly by forward checking:
      1. Bijection validity of sigma12: S1 -> S2 and sigma13: S1 -> S3 (on disjoint state spaces).
      2. Native domain properties:
         - G1 minimal absorbing non-goal trap SCC `trap_set_s1` (point sinks |Q|=1 & cyclic SCCs |Q|>=2),
         - G2 modular homomorphism over (Z/mZ)^dim (F_2, F_3, ...) & pair collision,
         - G4 pre-state probe deformation entering `trap_set_s1`.
      3. Joint impossibility for ALL horizons k in N via ClosedLosingRegion certificate L subseteq P(S1)
         (unchanged across point sinks and cyclic SCC traps!).
      4. Strict irreducibility via 3 finite PlanTree certificates for ablation worlds C1, C2, C4.
      5. Honest SafeBypass (SolveOriginalTask vs SolveRestrictedTask) via PlanTree (BYPASSABLE)
         or universal forall-bijection (n!) ClosedLosingRegion certificates (UNBYPASSABLE).
"""

from __future__ import annotations

import json
import math
from typing import Any, Dict, FrozenSet, List, Sequence, Set, Tuple


def _is_bijection(mapping: Dict[str, str], dom: Sequence[str], cod: Sequence[str]) -> bool:
    dom_set = set(dom)
    cod_set = set(cod)
    if len(dom_set) != len(dom) or len(cod_set) != len(cod) or len(dom_set) != len(cod_set):
        return False
    if set(mapping.keys()) != dom_set:
        return False
    return set(mapping.values()) == cod_set


def _invert_bijection(mapping: Dict[str, str]) -> Dict[str, str]:
    return {v: k for k, v in mapping.items()}


def _mod_project(vec: Sequence[int], matrix: Sequence[Sequence[int]], modulus: int) -> Tuple[int, ...]:
    out: List[int] = []
    for row in matrix:
        acc = 0
        for a, b in zip(row, vec):
            acc = (acc + int(a) * int(b)) % modulus
        out.append(acc)
    return tuple(out)


def _check_mod_linear(spec_d2: Dict[str, Any]) -> bool:
    states: List[str] = spec_d2["states"]
    dim: int = int(spec_d2["dim"])
    modulus: int = int(spec_d2.get("modulus", 2))
    if modulus < 2:
        return False
    encoding: Dict[str, List[int]] = spec_d2["encoding"]
    matrix: List[List[int]] = spec_d2["matrix"]
    if set(encoding.keys()) != set(states):
        return False
    for s in states:
        v = encoding[s]
        if len(v) != dim or any(int(x) < 0 or int(x) >= modulus for x in v):
            return False
    if not matrix or any(len(row) != dim or any(int(x) < 0 or int(x) >= modulus for x in row) for row in matrix):
        return False
    vec_to_state = {tuple(encoding[s]): s for s in states}
    if len(vec_to_state) != len(states):
        return False
    proj = {s: _mod_project(encoding[s], matrix, modulus) for s in states}
    zero_v = (0,) * dim
    if zero_v in vec_to_state and proj[vec_to_state[zero_v]] != (0,) * len(matrix):
        return False
    for s1 in states:
        v1 = encoding[s1]
        for s2 in states:
            v2 = encoding[s2]
            v_sum = tuple((int(a) + int(b)) % modulus for a, b in zip(v1, v2))
            if v_sum in vec_to_state:
                lhs = proj[vec_to_state[v_sum]]
                rhs = tuple((int(a) + int(b)) % modulus for a, b in zip(proj[s1], proj[s2]))
                if lhs != rhs:
                    return False
    return True


def _is_minimal_absorbing_trap_scc(world: Dict[str, Any], trap_set: FrozenSet[str]) -> bool:
    """Verifies `trap_set` is a non-empty, goal-disjoint, delta-closed, strongly connected sink SCC."""
    if not trap_set or (trap_set & world["goals"]):
        return False
    if not set(trap_set).issubset(set(world["states"])):
        return False
    for start in trap_set:
        seen: Set[str] = {start}
        stack: List[str] = [start]
        while stack:
            u = stack.pop()
            for a in world["actions"]:
                v = world["delta"][(u, a)]
                if v not in trap_set:
                    return False
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        if seen != trap_set:
            return False
    return True


def _build_composed_world(
    spec_d1: Dict[str, Any],
    spec_d2: Dict[str, Any],
    spec_d3: Dict[str, Any],
    sigma12: Dict[str, str],
    sigma13: Dict[str, str],
) -> Dict[str, Any]:
    s1_states: List[str] = list(spec_d1["states"])
    actions: List[str] = list(spec_d1["actions"])
    goals: FrozenSet[str] = frozenset(spec_d1["goals"])
    modulus: int = int(spec_d2.get("modulus", 2))
    delta: Dict[Tuple[str, str], str] = {
        (k.split("||")[0], k.split("||")[1]): v for k, v in spec_d1["transition"].items()
    }
    inv13 = _invert_bijection(sigma13)
    pi: Dict[str, Tuple[int, ...]] = {
        s: _mod_project(spec_d2["encoding"][sigma12[s]], spec_d2["matrix"], modulus) for s in s1_states
    }
    probe_state: Dict[str, str] = {
        s: inv13[spec_d3["state_effect"][sigma13[s]]] for s in s1_states
    }
    probe_obs: Dict[str, int] = {
        s: int(spec_d3["observed"][sigma13[s]]) for s in s1_states
    }
    return {
        "states": s1_states,
        "actions": actions,
        "goals": goals,
        "delta": delta,
        "pi": pi,
        "probe_state": probe_state,
        "probe_obs": probe_obs,
    }


def _initial_active_branches(world: Dict[str, Any], init_belief: Sequence[str]) -> Dict[str, FrozenSet[str]]:
    groups: Dict[Tuple[int, ...], Set[str]] = {}
    for s in init_belief:
        groups.setdefault(world["pi"][s], set()).add(s)
    out: Dict[str, FrozenSet[str]] = {}
    for obs, grp in groups.items():
        key = ",".join(str(x) for x in obs)
        out[key] = frozenset(s for s in grp if s not in world["goals"])
    return out


def verify_closed_losing_region(
    world: Dict[str, Any],
    init_belief: Sequence[str],
    losing_region_raw: Sequence[Sequence[str]],
) -> Tuple[bool, str]:
    """
    Soundness check for A4 (UNCHANGED across point sinks and cyclic SCC traps!):
      Verifies L subseteq P(S1) is a non-empty closed losing invariant containing
      at least one initial passive branch B_{pi=o} \\ goals.
      By Theorem 2 (`closedLosingRegion_not_safeBeliefReachInit`), certifies
      forall k in N, not SafeBeliefReachInit(W, k, B_0).
    """
    if not losing_region_raw:
        return False, "EMPTY_LOSING_REGION"
    s1_set = set(world["states"])
    goals: FrozenSet[str] = world["goals"]
    L: Set[FrozenSet[str]] = set()
    for raw_b in losing_region_raw:
        b = frozenset(raw_b)
        if not b:
            return False, "EMPTY_BELIEF_IN_LOSING_REGION"
        if not b.issubset(s1_set):
            return False, "UNKNOWN_STATE_IN_LOSING_REGION"
        if b & goals:
            return False, "GOAL_STATE_IN_ACTIVE_LOSING_BELIEF"
        L.add(b)

    init_branches = _initial_active_branches(world, init_belief)
    if not any(b in L for b in init_branches.values()):
        return False, "NO_INITIAL_BRANCH_IN_LOSING_REGION"

    for b in L:
        for a in world["actions"]:
            by_pi: Dict[Tuple[int, ...], Set[str]] = {}
            for s in b:
                ns = world["delta"][(s, a)]
                if ns not in goals:
                    by_pi.setdefault(world["pi"][ns], set()).add(ns)
            if not any(frozenset(nxt) in L for nxt in by_pi.values()):
                return False, f"LOSING_REGION_NOT_CLOSED_UNDER_ACT:{a}"
        by_obs: Dict[int, Set[str]] = {}
        for s in b:
            ns = world["probe_state"][s]
            if ns not in goals:
                by_obs.setdefault(world["probe_obs"][s], set()).add(ns)
        if not any(frozenset(nxt) in L for nxt in by_obs.values()):
            return False, "LOSING_REGION_NOT_CLOSED_UNDER_PROBE"

    return True, "OK"


def _verify_plan_node(
    world: Dict[str, Any],
    belief: FrozenSet[str],
    node: Dict[str, Any],
    depth_limit: int = 64,
) -> Tuple[bool, str]:
    if depth_limit < 0:
        return False, "PLAN_DEPTH_EXCEEDED"
    kind = node.get("kind")
    if kind == "Stop":
        return (len(belief) == 0, "OK" if len(belief) == 0 else "STOP_WITH_NONEMPTY_ACTIVE_BELIEF")
    if kind == "Act":
        a = node.get("action")
        if a not in world["actions"]:
            return False, f"INVALID_ACTION:{a}"
        branches = node.get("branches", {})
        by_pi: Dict[str, Set[str]] = {}
        for s in belief:
            ns = world["delta"][(s, a)]
            if ns not in world["goals"]:
                k = ",".join(str(x) for x in world["pi"][ns])
                by_pi.setdefault(k, set()).add(ns)
        for obs_k, nxt in by_pi.items():
            if obs_k not in branches:
                return False, f"MISSING_ACT_BRANCH:{obs_k}"
            ok, msg = _verify_plan_node(world, frozenset(nxt), branches[obs_k], depth_limit - 1)
            if not ok:
                return False, msg
        return True, "OK"
    if kind == "Probe":
        branches = node.get("branches", {})
        by_obs: Dict[str, Set[str]] = {}
        for s in belief:
            ns = world["probe_state"][s]
            if ns not in world["goals"]:
                k = str(world["probe_obs"][s])
                by_obs.setdefault(k, set()).add(ns)
        for obs_k, nxt in by_obs.items():
            if obs_k not in branches:
                return False, f"MISSING_PROBE_BRANCH:{obs_k}"
            ok, msg = _verify_plan_node(world, frozenset(nxt), branches[obs_k], depth_limit - 1)
            if not ok:
                return False, msg
        return True, "OK"
    return False, f"UNKNOWN_PLAN_KIND:{kind}"


def verify_plan_tree(
    world: Dict[str, Any],
    init_belief: Sequence[str],
    init_plan_map: Dict[str, Dict[str, Any]],
) -> Tuple[bool, str]:
    init_branches = _initial_active_branches(world, init_belief)
    for obs_k, b in init_branches.items():
        if not b:
            continue
        if obs_k not in init_plan_map:
            return False, f"MISSING_INIT_BRANCH:{obs_k}"
        ok, msg = _verify_plan_node(world, b, init_plan_map[obs_k])
        if not ok:
            return False, msg
    return True, "OK"


def verify_certificate_bundle(
    d1_library: Dict[str, Dict[str, Any]],
    d2_library: Dict[str, Dict[str, Any]],
    d3_library: Dict[str, Dict[str, Any]],
    cert: Dict[str, Any],
) -> Tuple[str, str]:
    """
    Zero-trust verification of a serialized DiscoveryCertificate JSON dictionary.
    Returns ("ACCEPTED", "OK") or ("REJECTED", reason).
    """
    glue = cert.get("glue", {})
    d1_id = glue.get("d1_id")
    d2_id = glue.get("d2_id")
    d3_id = glue.get("d3_id")
    if d1_id not in d1_library or d2_id not in d2_library or d3_id not in d3_library:
        return "REJECTED", "UNKNOWN_ARTIFACT_ID"

    spec_d1 = d1_library[d1_id]
    spec_d2 = d2_library[d2_id]
    spec_d3 = d3_library[d3_id]
    sigma12: Dict[str, str] = glue.get("sigma12", {})
    sigma13: Dict[str, str] = glue.get("sigma13", {})

    if not _is_bijection(sigma12, spec_d1["states"], spec_d2["states"]):
        return "REJECTED", "INVALID_BIJECTION_SIGMA12"
    if not _is_bijection(sigma13, spec_d1["states"], spec_d3["states"]):
        return "REJECTED", "INVALID_BIJECTION_SIGMA13"

    s0, s1 = glue["pair_s1"]
    raw_trap_set = glue.get("trap_set_s1") or ([glue["trap_s1"]] if "trap_s1" in glue else [])
    trap_set = frozenset(raw_trap_set)
    target_s = glue["probe_target_s1"]
    goals = set(spec_d1["goals"])
    if (
        s0 == s1
        or s0 in goals
        or s1 in goals
        or not trap_set
        or (trap_set & goals)
        or target_s not in (s0, s1)
        or target_s in trap_set
    ):
        return "REJECTED", "INVALID_GLUE_ROLES"

    if not _check_mod_linear(spec_d2):
        return "REJECTED", "D2_NOT_LINEAR_HOMOMORPHISM"

    world = _build_composed_world(spec_d1, spec_d2, spec_d3, sigma12, sigma13)

    # Check structural G1 (minimal absorbing trap SCC + probe closure), G2 (collision), G4 (trap entry)
    if not _is_minimal_absorbing_trap_scc(world, trap_set) or not all(
        world["probe_state"][q] in trap_set for q in trap_set
    ):
        return "REJECTED", "G1_TRAP_SCC_NOT_ABSORBING_OR_MINIMAL"
    if world["pi"][s0] != world["pi"][s1]:
        return "REJECTED", "G2_PAIR_NOT_COLLIDING"
    if world["probe_state"][target_s] not in trap_set:
        return "REJECTED", "G4_PROBE_NOT_ENTERING_TRAP_SCC"

    # 1. Verify joint impossibility for ALL horizons k in N via ClosedLosingRegion
    if cert.get("cross_verdict") != "IRREDUCIBLE":
        return "REJECTED", "NOT_IRREDUCIBLE_CERT"
    ok, msg = verify_closed_losing_region(world, [s0, s1], cert.get("joint_losing_region", []))
    if not ok:
        return "REJECTED", f"JOINT_LOSING_CERT_FAILED:{msg}"

    # 2. Verify 3 ablation countermodel PlanTrees (C1, C2, C4)
    ablation_plans = cert.get("ablation_plans", {})
    goal_any = sorted(goals)[0]
    q_exit = sorted(trap_set)[0]
    c1_world = {**world, "delta": {**world["delta"], (q_exit, world["actions"][0]): goal_any}}
    c2_world = {**world, "pi": {**world["pi"], s0: (0,), s1: (1,)}}
    c4_world = {**world, "probe_state": {**world["probe_state"], target_s: target_s}}

    for tag, abl_w in (("C1", c1_world), ("C2", c2_world), ("C4", c4_world)):
        if tag not in ablation_plans:
            return "REJECTED", f"MISSING_ABLATION_PLAN:{tag}"
        ok, msg = verify_plan_tree(abl_w, [s0, s1], ablation_plans[tag])
        if not ok:
            return "REJECTED", f"ABLATION_{tag}_PLAN_FAILED:{msg}"

    # 3. Verify Shift 2 BypassVerdict (SolveOriginalTask strictly preserves B0={s0,s1} and goals)
    bv = cert.get("bypass_verdict")
    if bv == "BYPASSABLE":
        rev = cert.get("bypass_revision")
        plan = cert.get("bypass_plan")
        if not rev or not plan:
            return "REJECTED", "MISSING_BYPASS_WITNESS"
        kind = rev.get("kind")
        if kind == "RefinePort":
            alt_id = rev["alt_d2_id"]
            alt_sig12 = rev["alt_sigma12"]
            if alt_id not in d2_library or alt_id == d2_id:
                return "REJECTED", "UNLICENSED_ALT_PORT"
            if not _is_bijection(alt_sig12, spec_d1["states"], d2_library[alt_id]["states"]):
                return "REJECTED", "INVALID_ALT_SIGMA12"
            if not _check_mod_linear(d2_library[alt_id]):
                return "REJECTED", "ALT_D2_NOT_LINEAR"
            rev_world = _build_composed_world(spec_d1, d2_library[alt_id], spec_d3, alt_sig12, sigma13)
        elif kind == "ReplaceProbe":
            alt_id = rev["alt_d3_id"]
            alt_sig13 = rev["alt_sigma13"]
            if alt_id not in d3_library or alt_id == d3_id:
                return "REJECTED", "UNLICENSED_ALT_PROBE"
            if not _is_bijection(alt_sig13, spec_d1["states"], d3_library[alt_id]["states"]):
                return "REJECTED", "INVALID_ALT_SIGMA13"
            rev_world = _build_composed_world(spec_d1, spec_d2, d3_library[alt_id], sigma12, alt_sig13)
        else:
            return "REJECTED", f"INVALID_BYPASS_KIND:{kind}"
        ok, msg = verify_plan_tree(rev_world, [s0, s1], plan)
        if not ok:
            return "REJECTED", f"BYPASS_PLAN_FAILED:{msg}"
    elif bv == "UNBYPASSABLE":
        unb_certs: Dict[str, Any] = cert.get("unbypassable_certificates", {})
        expected_bij_count = math.factorial(len(spec_d1["states"]))
        for alt_id, alt_d2 in d2_library.items():
            if alt_id == d2_id or len(alt_d2["states"]) != len(spec_d1["states"]) or not _check_mod_linear(alt_d2):
                continue
            key = f"RefinePort:{alt_id}"
            fam = unb_certs.get(key)
            if not isinstance(fam, list) or len(fam) != expected_bij_count:
                return "REJECTED", f"INCOMPLETE_FORALL_BIJECTIONS_CERT:{key}"
            seen_sigs: Set[Tuple[Tuple[str, str], ...]] = set()
            for entry in fam:
                sig_c = entry.get("sigma12", {})
                if not _is_bijection(sig_c, spec_d1["states"], alt_d2["states"]):
                    return "REJECTED", f"INVALID_UNBYPASSABLE_BIJECTION:{key}"
                sig_key = tuple(sorted(sig_c.items()))
                if sig_key in seen_sigs:
                    return "REJECTED", f"DUPLICATE_BIJECTION_IN_UNBYPASSABLE_CERT:{key}"
                seen_sigs.add(sig_key)
                rev_world = _build_composed_world(spec_d1, alt_d2, spec_d3, sig_c, sigma13)
                ok, msg = verify_closed_losing_region(rev_world, [s0, s1], entry.get("losing_region", []))
                if not ok:
                    return "REJECTED", f"UNBYPASSABLE_CERT_FAILED:{key}:{msg}"
        for alt_id, alt_d3 in d3_library.items():
            if alt_id == d3_id or len(alt_d3["states"]) != len(spec_d1["states"]):
                continue
            key = f"ReplaceProbe:{alt_id}"
            fam = unb_certs.get(key)
            if not isinstance(fam, list) or len(fam) != expected_bij_count:
                return "REJECTED", f"INCOMPLETE_FORALL_BIJECTIONS_CERT:{key}"
            seen_sigs3: Set[Tuple[Tuple[str, str], ...]] = set()
            for entry in fam:
                sig_c3 = entry.get("sigma13", {})
                if not _is_bijection(sig_c3, spec_d1["states"], alt_d3["states"]):
                    return "REJECTED", f"INVALID_UNBYPASSABLE_BIJECTION:{key}"
                sig_key3 = tuple(sorted(sig_c3.items()))
                if sig_key3 in seen_sigs3:
                    return "REJECTED", f"DUPLICATE_BIJECTION_IN_UNBYPASSABLE_CERT:{key}"
                seen_sigs3.add(sig_key3)
                rev_world = _build_composed_world(spec_d1, spec_d2, alt_d3, sigma12, sig_c3)
                ok, msg = verify_closed_losing_region(rev_world, [s0, s1], entry.get("losing_region", []))
                if not ok:
                    return "REJECTED", f"UNBYPASSABLE_CERT_FAILED:{key}:{msg}"
    else:
        return "REJECTED", f"INVALID_BYPASS_VERDICT:{bv}"

    return "ACCEPTED", "OK"


def verify_json_string(payload_json: str) -> Tuple[str, str]:
    payload = json.loads(payload_json)
    return verify_certificate_bundle(
        payload["d1_library"],
        payload["d2_library"],
        payload["d3_library"],
        payload["certificate"],
    )
