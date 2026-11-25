"""
certified_structural_discovery_v4_0.py — Hardened Executable Core for Certified Structural Discovery (v4.0).

Covers Benchmarks X0, X1, X2, X3 (Rule 110), and X4 (Certified Transfer to Cyclic SCC Traps & F_p Ports):
  1. Pairwise disjoint opaque state spaces S1, S2, S3 across D1, D2, D3 (zero shared IDs).
  2. Explicit cross-domain bijections sigma12: S1 -> S2 and sigma13: S1 -> S3 in InterfaceGlue.
  3. Unified minimal absorbing trap SCCs `trap_set_s1` (|Q| = 1 point sinks and |Q| >= 2 limit cycles)
     and modular homomorphisms over Z/mZ^d (m = 2 for F_2, m = 3 for F_3, etc.).
  4. Honest A0 (full bijection pair enumeration Bij(S1,S2) x Bij(S1,S3)) vs A1 (name-invariant
     structural index join I1 |><| I2 |><| I3) with provable completeness Accepted(A1) == Accepted(A0).
  5. DiscoveryMemory `MethodToken` transfer with fail-closed precondition gate and B6 (WithMemory vs NoMemory).
  6. Emits self-contained JSON DiscoveryCertificates (ClosedLosingRegion + PlanTrees + forall-bijection
     UNBYPASSABLE witnesses) verified by standalone zero-trust `independent_verifier_v4_0.py`.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from dataclasses import dataclass
from typing import Any, Dict, FrozenSet, List, Optional, Sequence, Set, Tuple


# ==============================================================================
# 1. COST ACCOUNTING & FROZEN DOMAIN ARTIFACTS (DISJOINT STATE SPACES)
# ==============================================================================

@dataclass
class CostVector:
    observations: int = 0
    synthesis: int = 0       # includes structural indexing + bijection generation
    port_revision: int = 0
    verification: int = 0
    memory: int = 0

    def total(self) -> int:
        return self.observations + self.synthesis + self.port_revision + self.verification + self.memory

    def to_dict(self) -> Dict[str, int]:
        return {
            "observations": self.observations,
            "synthesis": self.synthesis,
            "port_revision": self.port_revision,
            "verification": self.verification,
            "memory": self.memory,
            "total": self.total(),
        }


@dataclass(frozen=True)
class SinkGraphModel:
    states: Tuple[str, ...]
    actions: Tuple[str, ...]
    transition: Dict[Tuple[str, str], str]
    goals: FrozenSet[str]

    def forward_closure(self, start: str) -> FrozenSet[str]:
        seen: Set[str] = {start}
        stack: List[str] = [start]
        while stack:
            u = stack.pop()
            for a in self.actions:
                v = self.transition[(u, a)]
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        return frozenset(seen)

    def absorbing_non_goals(self) -> List[str]:
        return [
            q for q in self.states
            if q not in self.goals and all(self.transition[(q, a)] == q for a in self.actions)
        ]

    def minimal_absorbing_trap_sccs(self) -> List[Tuple[str, ...]]:
        """
        Finds all minimal non-empty absorbing non-goal trap SCCs Q subseteq S1 \\ goals:
          R(s) is a sink non-goal SCC iff R(s) & goals == empty and forall u in R(s), R(u) == R(s).
        Includes 1-state point sinks (|Q| == 1) and multi-state cyclic traps (|Q| >= 2).
        """
        closures = {s: self.forward_closure(s) for s in self.states}
        found: Set[Tuple[str, ...]] = set()
        for s, reach_s in closures.items():
            if reach_s & self.goals:
                continue
            if all(closures[u] == reach_s for u in reach_s):
                found.add(tuple(sorted(reach_s)))
        return sorted(found)

    def goal_attractor(self) -> Set[str]:
        """States from which a goal is reachable under full observability (necessary for C2)."""
        attr: Set[str] = set(self.goals)
        changed = True
        while changed:
            changed = False
            for s in self.states:
                if s in attr:
                    continue
                if any(self.transition[(s, a)] in attr for a in self.actions):
                    attr.add(s)
                    changed = True
        return attr

    def one_step_win_actions(self, s: str) -> Set[str]:
        return {a for a in self.actions if self.transition[(s, a)] in self.goals}

    def to_spec(self) -> Dict[str, Any]:
        return {
            "states": list(self.states),
            "actions": list(self.actions),
            "transition": {f"{s}||{a}": nxt for (s, a), nxt in self.transition.items()},
            "goals": sorted(self.goals),
        }


@dataclass(frozen=True)
class LinearProjectionF2Model:
    """
    Linear / modular homomorphism projection over (Z / modulus Z)^dim.
    Defaults to modulus=2 (F_2^dim) for backward compatibility with X0-X3;
    supports modulus=3 (F_3^dim) and general m >= 2 in X4.
    """
    states: Tuple[str, ...]
    dim: int
    encoding: Dict[str, Tuple[int, ...]]
    matrix: Tuple[Tuple[int, ...], ...]
    modulus: int = 2

    def project(self, s: str) -> Tuple[int, ...]:
        v = self.encoding[s]
        m = self.modulus
        out = []
        for row in self.matrix:
            acc = 0
            for a, b in zip(row, v):
                acc = (acc + a * b) % m
            out.append(acc)
        return tuple(out)

    def is_linear(self) -> bool:
        m = self.modulus
        if m < 2:
            return False
        vec_to_s = {self.encoding[s]: s for s in self.states}
        if len(vec_to_s) != len(self.states):
            return False
        for v in vec_to_s:
            if len(v) != self.dim or any(x < 0 or x >= m for x in v):
                return False
        proj = {s: self.project(s) for s in self.states}
        zero_v = (0,) * self.dim
        if zero_v in vec_to_s and proj[vec_to_s[zero_v]] != (0,) * len(self.matrix):
            return False
        for s1 in self.states:
            v1 = self.encoding[s1]
            for s2 in self.states:
                v2 = self.encoding[s2]
                v_sum = tuple((a + b) % m for a, b in zip(v1, v2))
                if v_sum in vec_to_s:
                    lhs = proj[vec_to_s[v_sum]]
                    rhs = tuple((a + b) % m for a, b in zip(proj[s1], proj[s2]))
                    if lhs != rhs:
                        return False
        return True

    def collision_pairs(self) -> List[Tuple[str, str]]:
        by_out: Dict[Tuple[int, ...], List[str]] = {}
        for s in self.states:
            by_out.setdefault(self.project(s), []).append(s)
        pairs: List[Tuple[str, str]] = []
        for grp in by_out.values():
            for i in range(len(grp)):
                for j in range(i + 1, len(grp)):
                    pairs.append((grp[i], grp[j]))
        return pairs

    def to_spec(self) -> Dict[str, Any]:
        return {
            "states": list(self.states),
            "dim": self.dim,
            "modulus": self.modulus,
            "encoding": {s: list(v) for s, v in self.encoding.items()},
            "matrix": [list(r) for r in self.matrix],
        }


@dataclass(frozen=True)
class AuditBackActionModel:
    states: Tuple[str, ...]
    probe_id: str
    state_effect: Dict[str, str]
    observed: Dict[str, int]

    def deformations_to_closed_sets(self, allowed_sizes: Set[int]) -> List[Tuple[str, Tuple[str, ...]]]:
        """
        Finds all pairs (x, C) where C subseteq S3 is a non-empty U_p-closed subset
        with |C| in allowed_sizes, x not in C, and U_p(x) in C.
        For allowed_sizes == {1}, coincides with point-sink fixed-point deformations.
        """
        out: List[Tuple[str, Tuple[str, ...]]] = []
        for k in sorted(allowed_sizes):
            if k <= 0 or k >= len(self.states):
                continue
            for comb in itertools.combinations(self.states, k):
                c_set = set(comb)
                if all(self.state_effect[c] in c_set for c in comb):
                    c_sorted = tuple(sorted(comb))
                    for x in self.states:
                        if x not in c_set and self.state_effect[x] in c_set:
                            out.append((x, c_sorted))
        return out

    def to_spec(self) -> Dict[str, Any]:
        return {
            "states": list(self.states),
            "probe_id": self.probe_id,
            "state_effect": dict(self.state_effect),
            "observed": dict(self.observed),
        }


@dataclass(frozen=True)
class DomainArtifact:
    opaque_id: str
    domain: str
    native_model: Any
    content_hash: str


def make_artifact(opaque_id: str, domain: str, native_model: Any) -> DomainArtifact:
    payload = json.dumps({"id": opaque_id, "domain": domain, "spec": native_model.to_spec()}, sort_keys=True).encode("utf-8")
    return DomainArtifact(
        opaque_id=opaque_id,
        domain=domain,
        native_model=native_model,
        content_hash=hashlib.sha256(payload).hexdigest(),
    )


# ==============================================================================
# 2. A4 EXACT LEAST FIXED POINT (EMITS PLANTREE OR CLOSED LOSING REGION)
# ==============================================================================

@dataclass(frozen=True)
class ComposedWorld:
    states: Tuple[str, ...]
    actions: Tuple[str, ...]
    goals: FrozenSet[str]
    pi: Dict[str, Tuple[int, ...]]
    delta: Dict[Tuple[str, str], str]
    probe_state: Dict[str, str]
    probe_obs: Dict[str, int]


@dataclass(frozen=True)
class ReachabilityWitness:
    status: str  # "WINNING" | "LOSING" | "UNKNOWN"
    plan_map: Optional[Dict[str, Dict[str, Any]]] = None
    losing_region: Optional[List[List[str]]] = None


def fixed_point_safe_belief_reach(
    w: ComposedWorld,
    initial_belief: FrozenSet[str],
    max_iters: Optional[int] = None,
) -> ReachabilityWitness:
    init_groups: Dict[Tuple[int, ...], Set[str]] = {}
    for s in initial_belief:
        init_groups.setdefault(w.pi[s], set()).add(s)
    init_branches: Dict[str, FrozenSet[str]] = {
        ",".join(str(x) for x in obs): frozenset(s for s in grp if s not in w.goals)
        for obs, grp in init_groups.items()
    }

    reachable: Set[FrozenSet[str]] = set(init_branches.values())
    queue: List[FrozenSet[str]] = list(init_branches.values())
    while queue:
        b = queue.pop()
        if not b:
            continue
        for a in w.actions:
            by_pi: Dict[Tuple[int, ...], Set[str]] = {}
            for s in b:
                ns = w.delta[(s, a)]
                if ns not in w.goals:
                    by_pi.setdefault(w.pi[ns], set()).add(ns)
            for nxt in by_pi.values():
                fn = frozenset(nxt)
                if fn not in reachable:
                    reachable.add(fn)
                    queue.append(fn)
        by_obs: Dict[int, Set[str]] = {}
        for s in b:
            ns = w.probe_state[s]
            if ns not in w.goals:
                by_obs.setdefault(w.probe_obs[s], set()).add(ns)
        for nxt in by_obs.values():
            fn = frozenset(nxt)
            if fn not in reachable:
                reachable.add(fn)
                queue.append(fn)

    winning_node: Dict[FrozenSet[str], Dict[str, Any]] = {frozenset(): {"kind": "Stop"}}
    step = 0
    while True:
        if all(ib in winning_node for ib in init_branches.values()):
            plan_map = {k: winning_node[ib] for k, ib in init_branches.items() if ib}
            return ReachabilityWitness(status="WINNING", plan_map=plan_map)
        if max_iters is not None and step >= max_iters:
            return ReachabilityWitness(status="UNKNOWN")
        step += 1
        added: Dict[FrozenSet[str], Dict[str, Any]] = {}
        for b in reachable:
            if b in winning_node:
                continue
            found_node: Optional[Dict[str, Any]] = None
            for a in w.actions:
                by_pi_k: Dict[str, Set[str]] = {}
                for s in b:
                    ns = w.delta[(s, a)]
                    if ns not in w.goals:
                        ok = ",".join(str(x) for x in w.pi[ns])
                        by_pi_k.setdefault(ok, set()).add(ns)
                if all(frozenset(nxt) in winning_node for nxt in by_pi_k.values()):
                    found_node = {
                        "kind": "Act",
                        "action": a,
                        "branches": {ok: winning_node[frozenset(nxt)] for ok, nxt in by_pi_k.items()},
                    }
                    break
            if found_node is None:
                by_obs_k: Dict[str, Set[str]] = {}
                for s in b:
                    ns = w.probe_state[s]
                    if ns not in w.goals:
                        ok = str(w.probe_obs[s])
                        by_obs_k.setdefault(ok, set()).add(ns)
                if all(frozenset(nxt) in winning_node for nxt in by_obs_k.values()):
                    found_node = {
                        "kind": "Probe",
                        "branches": {ok: winning_node[frozenset(nxt)] for ok, nxt in by_obs_k.items()},
                    }
            if found_node is not None:
                added[b] = found_node
        if not added:
            losing = sorted((sorted(b) for b in (reachable - set(winning_node.keys())) if b))
            return ReachabilityWitness(status="LOSING", losing_region=losing)
        winning_node.update(added)


# ==============================================================================
# 3. EXPLICIT BIJECTION GLUE, EVALUATION & CERTIFICATE EMISSION
# ==============================================================================

@dataclass(frozen=True)
class GlueCandidate:
    d1_id: str
    d2_id: str
    d3_id: str
    sigma12: Tuple[Tuple[str, str], ...]   # sorted pairs (s1, s2)
    sigma13: Tuple[Tuple[str, str], ...]   # sorted pairs (s1, s3)
    trap_set_s1: Tuple[str, ...]           # sorted minimal absorbing trap SCC (size >= 1)
    pair_s1: Tuple[str, str]               # sorted (s0, s1)
    probe_target_s1: str

    def to_dict(self) -> Dict[str, Any]:
        return {
            "d1_id": self.d1_id,
            "d2_id": self.d2_id,
            "d3_id": self.d3_id,
            "sigma12": dict(self.sigma12),
            "sigma13": dict(self.sigma13),
            "trap_set_s1": list(self.trap_set_s1),
            "trap_s1": self.trap_set_s1[0],
            "pair_s1": list(self.pair_s1),
            "probe_target_s1": self.probe_target_s1,
        }


@dataclass(frozen=True)
class DiscoveryResult:
    glue: GlueCandidate
    cross_verdict: str             # INCOMPATIBLE | DEGENERATE | REFUTED | REDUCIBLE | IRREDUCIBLE | UNKNOWN
    bypass_verdict: str            # NOT_APPLICABLE | BYPASSABLE | UNBYPASSABLE | UNKNOWN
    diagnostics: Tuple[str, ...]
    certificate: Optional[Dict[str, Any]] = None


def _compose(
    g1: SinkGraphModel,
    g2: LinearProjectionF2Model,
    g3: AuditBackActionModel,
    sig12: Dict[str, str],
    sig13: Dict[str, str],
) -> ComposedWorld:
    inv13 = {v: k for k, v in sig13.items()}
    return ComposedWorld(
        states=g1.states,
        actions=g1.actions,
        goals=g1.goals,
        pi={s: g2.project(sig12[s]) for s in g1.states},
        delta=dict(g1.transition),
        probe_state={s: inv13[g3.state_effect[sig13[s]]] for s in g1.states},
        probe_obs={s: g3.observed[sig13[s]] for s in g1.states},
    )


def _find_separating_bijection_fast_d2(
    g1: SinkGraphModel,
    alt_d2: LinearProjectionF2Model,
    s0: str,
    s1: str,
) -> Optional[Dict[str, str]]:
    """Constructs a candidate separating bijection S1 -> S2' in O(|S|^2) before full permutation fallback."""
    s2_list = list(alt_d2.states)
    for i, u in enumerate(s2_list):
        for v in s2_list[i + 1:]:
            if alt_d2.project(u) != alt_d2.project(v):
                rem1 = [s for s in g1.states if s not in (s0, s1)]
                rem2 = [x for x in s2_list if x not in (u, v)]
                m = {s0: u, s1: v}
                m.update(dict(zip(rem1, rem2)))
                return m
    return None


def _check_all_bijections_d2(
    g1: SinkGraphModel,
    alt_d2: LinearProjectionF2Model,
    g3: AuditBackActionModel,
    sig13: Dict[str, str],
    s0: str,
    s1: str,
) -> Tuple[Optional[Tuple[Dict[str, str], ReachabilityWitness]], List[Dict[str, Any]]]:
    """
    Either finds a winning bijection S1 -> S2' (BYPASSABLE; O(|S|^2) fast path first!),
    or collects a complete forall-bijections family of ClosedLosingRegion certificates across ALL n! bijections.
    """
    fast_sig = _find_separating_bijection_fast_d2(g1, alt_d2, s0, s1)
    if fast_sig is not None:
        fast_res = fixed_point_safe_belief_reach(_compose(g1, alt_d2, g3, fast_sig, sig13), frozenset({s0, s1}))
        if fast_res.status == "WINNING":
            return (fast_sig, fast_res), []

    losing_family: List[Dict[str, Any]] = []
    for perm in itertools.permutations(alt_d2.states):
        alt_sig12 = dict(zip(g1.states, perm))
        rev_w = _compose(g1, alt_d2, g3, alt_sig12, sig13)
        res = fixed_point_safe_belief_reach(rev_w, frozenset({s0, s1}))
        if res.status == "WINNING":
            return (alt_sig12, res), []
        losing_family.append({"sigma12": alt_sig12, "losing_region": res.losing_region})
    return None, losing_family


def _check_all_bijections_d3(
    g1: SinkGraphModel,
    g2: LinearProjectionF2Model,
    alt_d3: AuditBackActionModel,
    sig12: Dict[str, str],
    s0: str,
    s1: str,
) -> Tuple[Optional[Tuple[Dict[str, str], ReachabilityWitness]], List[Dict[str, Any]]]:
    """
    Either finds a winning bijection S1 -> S3' (BYPASSABLE),
    or collects a complete forall-bijections family of ClosedLosingRegion certificates across ALL n! bijections.
    """
    losing_family: List[Dict[str, Any]] = []
    for perm in itertools.permutations(alt_d3.states):
        alt_sig13 = dict(zip(g1.states, perm))
        rev_w = _compose(g1, g2, alt_d3, sig12, alt_sig13)
        res = fixed_point_safe_belief_reach(rev_w, frozenset({s0, s1}))
        if res.status == "WINNING":
            return (alt_sig13, res), []
        losing_family.append({"sigma13": alt_sig13, "losing_region": res.losing_region})
    return None, losing_family


def evaluate_glue_candidate(
    a1: DomainArtifact,
    a2: DomainArtifact,
    a3: DomainArtifact,
    glue: GlueCandidate,
    alt_d2_library: Sequence[DomainArtifact],
    alt_d3_library: Sequence[DomainArtifact],
    cost: CostVector,
    budget_limit: Optional[int] = None,
) -> DiscoveryResult:
    if budget_limit is not None and cost.total() >= budget_limit:
        return DiscoveryResult(glue, "UNKNOWN", "UNKNOWN", ("BUDGET_EXHAUSTED",))

    cost.verification += 1
    g1: SinkGraphModel = a1.native_model
    g2: LinearProjectionF2Model = a2.native_model
    g3: AuditBackActionModel = a3.native_model
    sig12 = dict(glue.sigma12)
    sig13 = dict(glue.sigma13)
    s0, s1 = glue.pair_s1
    trap_set = set(glue.trap_set_s1)

    if len(g1.states) != len(g2.states) or len(g1.states) != len(g3.states):
        return DiscoveryResult(glue, "INCOMPATIBLE", "NOT_APPLICABLE", ("SIZE_MISMATCH",))
    if s0 == s1 or s0 in g1.goals or s1 in g1.goals:
        return DiscoveryResult(glue, "DEGENERATE", "NOT_APPLICABLE", ())
    if not trap_set or (trap_set & g1.goals) or glue.probe_target_s1 not in (s0, s1) or glue.probe_target_s1 in trap_set:
        return DiscoveryResult(glue, "INCOMPATIBLE", "NOT_APPLICABLE", ())

    composed = _compose(g1, g2, g3, sig12, sig13)

    sccs = set(g1.minimal_absorbing_trap_sccs())
    g1_ok = (glue.trap_set_s1 in sccs) and all(composed.probe_state[q] in trap_set for q in trap_set)
    g2_ok = g2.is_linear() and (composed.pi[s0] == composed.pi[s1])
    g4_ok = (composed.probe_state[glue.probe_target_s1] in trap_set)

    # Anti-inflation diagnostic triple (C1: trap SCC exists, C'2: colliding disjoint 1-step wins, C4_order)
    c1_diag = len(sccs) > 0
    w0, w1 = g1.one_step_win_actions(s0), g1.one_step_win_actions(s1)
    c2_diag = (composed.pi[s0] == composed.pi[s1]) and bool(w0) and bool(w1) and w0.isdisjoint(w1)
    c4_diag = any(
        composed.probe_state[composed.delta[(s, a)]] != composed.delta[(composed.probe_state[s], a)]
        for s in g1.states for a in g1.actions
    )

    if not (g1_ok and g2_ok and g4_ok):
        if g1_ok and g2_ok and c1_diag and c2_diag and c4_diag:
            cost.observations += 1
            jr = fixed_point_safe_belief_reach(composed, frozenset({s0, s1}))
            if jr.status == "WINNING":
                return DiscoveryResult(glue, "REFUTED", "NOT_APPLICABLE", ("INFLATED_CLAIM",))
        return DiscoveryResult(glue, "INCOMPATIBLE", "NOT_APPLICABLE", ())

    # Exact A4 fixed point on joint world
    cost.observations += 1
    joint_res = fixed_point_safe_belief_reach(composed, frozenset({s0, s1}))
    if joint_res.status == "WINNING":
        flags = ("INFLATED_CLAIM",) if (c1_diag and c2_diag and c4_diag) else ()
        return DiscoveryResult(glue, "REFUTED", "NOT_APPLICABLE", flags)

    # Three maximal-subset ablation countermodels (C1, C2, C4)
    # In C1 (without D1 trap closure): open a single exit from sorted(trap_set)[0] -> goal_any.
    # Because trap_set is strongly connected under delta, opening 1 exit breaks the entire SCC trap!
    goal_any = sorted(g1.goals)[0]
    q_exit = glue.trap_set_s1[0]
    c1_w = ComposedWorld(
        states=composed.states, actions=composed.actions, goals=composed.goals,
        pi=composed.pi, delta={**composed.delta, (q_exit, composed.actions[0]): goal_any},
        probe_state=composed.probe_state, probe_obs=composed.probe_obs,
    )
    c2_w = ComposedWorld(
        states=composed.states, actions=composed.actions, goals=composed.goals,
        pi={**composed.pi, s0: (0,), s1: (1,)}, delta=composed.delta,
        probe_state=composed.probe_state, probe_obs=composed.probe_obs,
    )
    c4_w = ComposedWorld(
        states=composed.states, actions=composed.actions, goals=composed.goals,
        pi=composed.pi, delta=composed.delta,
        probe_state={**composed.probe_state, glue.probe_target_s1: glue.probe_target_s1},
        probe_obs=composed.probe_obs,
    )
    cost.verification += 3
    r_c1 = fixed_point_safe_belief_reach(c1_w, frozenset({s0, s1}))
    r_c2 = fixed_point_safe_belief_reach(c2_w, frozenset({s0, s1}))
    r_c4 = fixed_point_safe_belief_reach(c4_w, frozenset({s0, s1}))
    if not (r_c1.status == "WINNING" and r_c2.status == "WINNING" and r_c4.status == "WINNING"):
        return DiscoveryResult(glue, "REDUCIBLE", "NOT_APPLICABLE", ())

    # Shift 2: DiscoverBypass strictly over licensed menu (preserving B0={s0,s1} and goals)
    bypass_verdict = "UNBYPASSABLE"
    bypass_revision: Optional[Dict[str, Any]] = None
    bypass_plan: Optional[Dict[str, Any]] = None
    unbypassable_certs: Dict[str, Any] = {}

    for alt2 in alt_d2_library:
        if alt2.opaque_id == a2.opaque_id:
            continue
        m2: LinearProjectionF2Model = alt2.native_model
        if len(m2.states) != len(g1.states) or not m2.is_linear():
            continue
        cost.port_revision += 1
        win_pair2, losing_fam2 = _check_all_bijections_d2(g1, m2, g3, sig13, s0, s1)
        if win_pair2 is not None:
            alt_sig12, res_b = win_pair2
            bypass_verdict = "BYPASSABLE"
            bypass_revision = {"kind": "RefinePort", "alt_d2_id": alt2.opaque_id, "alt_sigma12": alt_sig12}
            bypass_plan = res_b.plan_map
            break
        else:
            unbypassable_certs[f"RefinePort:{alt2.opaque_id}"] = losing_fam2

    if bypass_verdict == "UNBYPASSABLE":
        for alt3 in alt_d3_library:
            if alt3.opaque_id == a3.opaque_id:
                continue
            m3: AuditBackActionModel = alt3.native_model
            if len(m3.states) != len(g1.states):
                continue
            cost.port_revision += 1
            win_pair3, losing_fam3 = _check_all_bijections_d3(g1, g2, m3, sig12, s0, s1)
            if win_pair3 is not None:
                alt_sig13, res_b = win_pair3
                bypass_verdict = "BYPASSABLE"
                bypass_revision = {"kind": "ReplaceProbe", "alt_d3_id": alt3.opaque_id, "alt_sigma13": alt_sig13}
                bypass_plan = res_b.plan_map
                break
            else:
                unbypassable_certs[f"ReplaceProbe:{alt3.opaque_id}"] = losing_fam3

    cert: Dict[str, Any] = {
        "glue": glue.to_dict(),
        "cross_verdict": "IRREDUCIBLE",
        "joint_losing_region": joint_res.losing_region,
        "ablation_plans": {
            "C1": r_c1.plan_map,
            "C2": r_c2.plan_map,
            "C4": r_c4.plan_map,
        },
        "bypass_verdict": bypass_verdict,
        "bypass_revision": bypass_revision,
        "bypass_plan": bypass_plan,
        "unbypassable_certificates": unbypassable_certs if bypass_verdict == "UNBYPASSABLE" else {},
    }
    return DiscoveryResult(glue, "IRREDUCIBLE", bypass_verdict, (), certificate=cert)


# ==============================================================================
# 4. A0 (HONEST FULL BIJECTION ENUMERATION) vs A1 (NAME-INVARIANT SCC/MOD JOIN)
# ==============================================================================

def discover_exhaustive_a0(
    d1_lib: Sequence[DomainArtifact],
    d2_lib: Sequence[DomainArtifact],
    d3_lib: Sequence[DomainArtifact],
    budget_limit: Optional[int] = None,
) -> Tuple[List[DiscoveryResult], CostVector]:
    """
    A0 Reference Exhaustive Search:
      Enumerates ALL bijection pairs (sigma12, sigma13) in Bij(S1, S2) x Bij(S1, S3)
      for every triple (a1, a2, a3), supporting both point sinks and cyclic trap SCCs.
    """
    cost = CostVector()
    results: List[DiscoveryResult] = []
    for a1 in d1_lib:
        g1: SinkGraphModel = a1.native_model
        s1_list = list(g1.states)
        n = len(s1_list)
        trap_sccs = g1.minimal_absorbing_trap_sccs()
        for a2 in d2_lib:
            g2: LinearProjectionF2Model = a2.native_model
            if len(g2.states) != n:
                continue
            perms2 = list(itertools.permutations(g2.states))
            for a3 in d3_lib:
                g3: AuditBackActionModel = a3.native_model
                if len(g3.states) != n:
                    continue
                perms3 = list(itertools.permutations(g3.states))
                for p2 in perms2:
                    sig12_dict = dict(zip(s1_list, p2))
                    sig12_t = tuple(sorted(sig12_dict.items()))
                    for p3 in perms3:
                        sig13_dict = dict(zip(s1_list, p3))
                        sig13_t = tuple(sorted(sig13_dict.items()))
                        inv13 = {v: k for k, v in sig13_dict.items()}
                        cost.synthesis += 1
                        if not trap_sccs:
                            continue
                        for trap_tup in trap_sccs:
                            trap_set = set(trap_tup)
                            for i in range(n):
                                for j in range(i + 1, n):
                                    u, v = s1_list[i], s1_list[j]
                                    if u in g1.goals or v in g1.goals or u in trap_set or v in trap_set:
                                        continue
                                    if g2.project(sig12_dict[u]) != g2.project(sig12_dict[v]):
                                        continue
                                    pair = tuple(sorted((u, v)))
                                    for t in pair:
                                        dest = inv13[g3.state_effect[sig13_dict[t]]]
                                        if dest in trap_set or (dest != t and g3.state_effect[sig13_dict[t]] != sig13_dict[t]):
                                            gc = GlueCandidate(a1.opaque_id, a2.opaque_id, a3.opaque_id, sig12_t, sig13_t, trap_tup, pair, t)
                                            res = evaluate_glue_candidate(a1, a2, a3, gc, d2_lib, d3_lib, cost, budget_limit)
                                            results.append(res)
    return results, cost


def discover_structural_join_a1(
    d1_lib: Sequence[DomainArtifact],
    d2_lib: Sequence[DomainArtifact],
    d3_lib: Sequence[DomainArtifact],
    budget_limit: Optional[int] = None,
    canonical_tail_only: bool = False,
    point_traps_only: bool = False,
) -> Tuple[List[DiscoveryResult], CostVector]:
    """
    A1 Name-Invariant Structural Join (Unified Point-Sink & Cyclic-SCC / Quotient-Modulus Engine):
      Builds structural role indices independently on each frozen library (costed in CostVector):
        I1(D1): minimal absorbing non-goal trap SCCs Q_trap and non-goal pairs (s0, s1) in GoalAttractor(D1)
        I2(D2): modular homomorphism projections (Z/mZ^d) with kernel-coset collision pairs {u0, u1}
        I3(D3): probe deformations (x -> C) into U_p-closed subsets C matching |Q_trap|
      When canonical_tail_only=False and point_traps_only=False, provably satisfies Accepted(A1) == Accepted(A0) (H16).
    """
    cost = CostVector()

    idx_d1: Dict[str, Tuple[List[Tuple[str, ...]], List[Tuple[str, str]]]] = {}
    observed_trap_sizes: Set[int] = set()
    for a1 in d1_lib:
        g1: SinkGraphModel = a1.native_model
        cost.synthesis += len(g1.states) * len(g1.actions)
        if point_traps_only:
            trap_sccs = [(q,) for q in g1.absorbing_non_goals()]
        else:
            trap_sccs = g1.minimal_absorbing_trap_sccs()
        for ts in trap_sccs:
            observed_trap_sizes.add(len(ts))
        attr = g1.goal_attractor()
        cand_states = [s for s in g1.states if s not in g1.goals and s in attr]
        pairs = [
            tuple(sorted((cand_states[i], cand_states[j])))
            for i in range(len(cand_states))
            for j in range(i + 1, len(cand_states))
        ]
        if trap_sccs and pairs:
            idx_d1[a1.opaque_id] = (trap_sccs, pairs)
            cost.memory += len(trap_sccs) + len(pairs)

    idx_d2: Dict[str, List[Tuple[str, str]]] = {}
    for a2 in d2_lib:
        g2: LinearProjectionF2Model = a2.native_model
        cost.synthesis += len(g2.states)
        if not g2.is_linear():
            continue
        col_pairs = g2.collision_pairs()
        if col_pairs:
            idx_d2[a2.opaque_id] = col_pairs
            cost.memory += len(col_pairs)

    idx_d3: Dict[str, List[Tuple[str, Tuple[str, ...]]]] = {}
    target_sizes = {1} if point_traps_only else (observed_trap_sizes or {1})
    for a3 in d3_lib:
        g3: AuditBackActionModel = a3.native_model
        cost.synthesis += len(g3.states)
        defs = g3.deformations_to_closed_sets(target_sizes)
        if defs:
            idx_d3[a3.opaque_id] = defs
            cost.memory += len(defs)

    d1_map = {a.opaque_id: a for a in d1_lib}
    d2_map = {a.opaque_id: a for a in d2_lib}
    d3_map = {a.opaque_id: a for a in d3_lib}

    results: List[DiscoveryResult] = []
    for id1, (trap_sccs, pairs1) in idx_d1.items():
        a1 = d1_map[id1]
        g1: SinkGraphModel = a1.native_model
        n = len(g1.states)
        for id2, col_pairs2 in idx_d2.items():
            a2 = d2_map[id2]
            g2: LinearProjectionF2Model = a2.native_model
            if len(g2.states) != n:
                continue
            for id3, defs3 in idx_d3.items():
                a3 = d3_map[id3]
                g3: AuditBackActionModel = a3.native_model
                if len(g3.states) != n:
                    continue
                for trap_tup in trap_sccs:
                    trap_set = set(trap_tup)
                    k_trap = len(trap_tup)
                    defs3_k = [(x3, c3) for (x3, c3) in defs3 if len(c3) == k_trap]
                    if not defs3_k:
                        continue
                    for s0, s1 in pairs1:
                        if s0 in trap_set or s1 in trap_set:
                            continue
                        rem1_for_d2 = [s for s in g1.states if s not in (s0, s1)]
                        sig12_cands: List[Tuple[Tuple[str, str], ...]] = []
                        for u0, u1 in col_pairs2:
                            rem2 = [x for x in g2.states if x not in (u0, u1)]
                            tail_perms2 = [tuple(rem2)] if canonical_tail_only else list(itertools.permutations(rem2))
                            for o0, o1 in ((u0, u1), (u1, u0)):
                                for tp2 in tail_perms2:
                                    m12 = {s0: o0, s1: o1}
                                    m12.update(dict(zip(rem1_for_d2, tp2)))
                                    sig12_cands.append(tuple(sorted(m12.items())))

                        for t in (s0, s1):
                            rem1_for_d3 = [s for s in g1.states if s != t and s not in trap_set]
                            sig13_cands: List[Tuple[Tuple[str, str], ...]] = []
                            for x3, c3_tup in defs3_k:
                                rem3 = [x for x in g3.states if x != x3 and x not in c3_tup]
                                c3_perms = [c3_tup] if canonical_tail_only else list(itertools.permutations(c3_tup))
                                tail_perms3 = [tuple(rem3)] if canonical_tail_only else list(itertools.permutations(rem3))
                                for cp3 in c3_perms:
                                    for tp3 in tail_perms3:
                                        m13 = {t: x3}
                                        m13.update(dict(zip(trap_tup, cp3)))
                                        m13.update(dict(zip(rem1_for_d3, tp3)))
                                        sig13_cands.append(tuple(sorted(m13.items())))

                            for sig12_t in sig12_cands:
                                for sig13_t in sig13_cands:
                                    cost.synthesis += 1
                                    gc = GlueCandidate(id1, id2, id3, sig12_t, sig13_t, trap_tup, (s0, s1), t)
                                    res = evaluate_glue_candidate(a1, a2, a3, gc, d2_lib, d3_lib, cost, budget_limit)
                                    results.append(res)
    return results, cost


# ==============================================================================
# 5. DISCOVERY MEMORY, CERTIFIED METHOD TRANSFER (X4) & B6 COST ACCOUNTING
# ==============================================================================

@dataclass(frozen=True)
class MethodToken:
    schema_id: str                 # "PointSink_F2" | "QuotientSCC_ModP"
    supports_cyclic_scc: bool
    supported_moduli: Tuple[int, ...]
    schema_discovery_cost: int     # c_s: paid when inducing join schema without memory
    memory_lookup_cost: int        # c_m: paid when recovering verified MethodToken


POINT_SINK_F2_TOKEN = MethodToken(
    schema_id="PointSink_F2",
    supports_cyclic_scc=False,
    supported_moduli=(2,),
    schema_discovery_cost=24,
    memory_lookup_cost=2,
)

QUOTIENT_SCC_MOD_TOKEN = MethodToken(
    schema_id="QuotientSCC_ModP",
    supports_cyclic_scc=True,
    supported_moduli=(2, 3, 5, 7),
    schema_discovery_cost=32,
    memory_lookup_cost=2,
)


def verify_method_transfer_precond(
    token: MethodToken,
    d1_lib: Sequence[DomainArtifact],
    d2_lib: Sequence[DomainArtifact],
) -> Tuple[bool, str]:
    """
    Fail-closed transfer precondition checker (mirrors `checkMethodPrecond` in Lean Section 7):
      - Rejects `PointSink_F2` if any D1 artifact contains a multi-state cyclic trap SCC (|Q| > 1)
        or if any D2 artifact uses a non-F_2 modulus.
      - Verifies c_m < c_s amortization precondition.
    """
    if token.memory_lookup_cost >= token.schema_discovery_cost:
        return False, "PRECOND_REJECT:NON_AMORTIZED_TOKEN"

    has_cyclic_scc = any(
        len(scc) > 1
        for a1 in d1_lib
        for scc in a1.native_model.minimal_absorbing_trap_sccs()
    )
    if has_cyclic_scc and not token.supports_cyclic_scc:
        return False, "PRECOND_REJECT:TARGET_HAS_CYCLIC_TRAP_SCC"

    moduli = {a2.native_model.modulus for a2 in d2_lib}
    if not moduli.issubset(set(token.supported_moduli)):
        return False, f"PRECOND_REJECT:UNSUPPORTED_MODULUS:{sorted(moduli)}"

    return True, "OK"


def run_certified_method_transfer(
    d1_lib: Sequence[DomainArtifact],
    d2_lib: Sequence[DomainArtifact],
    d3_lib: Sequence[DomainArtifact],
    token: Optional[MethodToken],
    canonical_tail_only: bool = False,
) -> Tuple[str, List[DiscoveryResult], CostVector]:
    """
    Executes discovery on a target library either:
      - `WithMemory` (`token != None`): checks transfer preconditions fail-closed (charging
        `memory_lookup_cost`), or halts with `BLOCKED_PRECONDITION` if preconditions fail.
      - `NoMemory` (`token == None`): re-derives the generalized `QuotientSCC_ModP` join schema
        from scratch (charging `QUOTIENT_SCC_MOD_TOKEN.schema_discovery_cost` to `cost.synthesis`).
    """
    if token is not None:
        ok, reason = verify_method_transfer_precond(token, d1_lib, d2_lib)
        if not ok:
            return reason, [], CostVector(verification=1)
        res, cost = discover_structural_join_a1(
            d1_lib, d2_lib, d3_lib,
            canonical_tail_only=canonical_tail_only,
            point_traps_only=(not token.supports_cyclic_scc),
        )
        cost.memory += token.memory_lookup_cost
        return "TRANSFERRED_OK", res, cost

    # NoMemory baseline: pays schema_discovery_cost to induce the generalized SCC/Modulus join schema
    res, cost = discover_structural_join_a1(
        d1_lib, d2_lib, d3_lib,
        canonical_tail_only=canonical_tail_only,
        point_traps_only=False,
    )
    cost.synthesis += QUOTIENT_SCC_MOD_TOKEN.schema_discovery_cost
    return "REDISCOVERED_NO_MEMORY", res, cost
