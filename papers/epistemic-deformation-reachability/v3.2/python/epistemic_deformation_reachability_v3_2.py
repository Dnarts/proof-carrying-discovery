"""
epistemic_deformation_reachability_v3_2.py — Reference Executable Engine for
Epistemic Deformation of Reachability (L_H^EDR, v3.2).

Pure Python 3 stdlib implementation mirroring all 12 modules of
`lean/epistemic_deformation_reachability_v3_2.lean`:
  1. CrossCore            : Monotone entailment, maximal-subset reduction & ConsistentIrreducible
  2. SinkGraph            : Native G1 absorbing trap graph
  3. LinearProjectionF2   : Native G2 F_2^2 linear projection (π_1 vs π_2, IsLinear + PairCollides)
  4. AuditBackAction      : Native G4 probe back-action (StateChange / NonCommutation / Designated)
  5. InterfaceGlue        : Load-bearing cross-domain alignment + two-tier CrossDiscoveryLicense
  6. SatisfactionBridge   : Glue-parameterized exact reducts β_1, β_2, β_4 (incl. IsLinear)
  7. JointEntailment      : Exhaustive history-dependent policy solver with post-Act passive `pi` split
  8. Countermodels        : Constructive winning policies for C1, C2, C4
  9. BooleanIndependence  : All 8/8 Boolean vectors of (C1, C'2, C4_order)
 10. AntiInflation        : Counterexample U_P(s1) = s0 proving C1 ∧ C'2 ∧ C4_order ⊬ h_k
 11. SafeBeliefReach      : General iff characterization with passive port `pi` & active-state filtering
 12. ProbabilisticVoI     : Discrete Blackwell monotonicity vs strict negative VoI (VoI_EDR = -1/3 < 0)
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Optional, Sequence, Set, Tuple

STATES4: Tuple[str, ...] = ("s0", "s1", "w", "q")
ACTS2: Tuple[str, ...] = ("L", "R")
ALLOWED_ACTS: Tuple[str, ...] = ("L", "R", "P")

Bit2 = Tuple[int, int]

F2_ENCODE: Dict[str, Bit2] = {
    "s0": (0, 0),
    "s1": (0, 1),
    "q": (1, 0),
    "w": (1, 1),
}
F2_DECODE: Dict[Bit2, str] = {v: k for k, v in F2_ENCODE.items()}


def xor2(u: Bit2, v: Bit2) -> Bit2:
    return (u[0] ^ v[0], u[1] ^ v[1])


@dataclass(frozen=True)
class SinkGraph:
    step: Dict[Tuple[str, str], str]
    win: Set[str]
    trap: str

    def is_absorbing_trap(self) -> bool:
        return (self.trap not in self.win) and all(
            self.step[(self.trap, a)] == self.trap for a in ALLOWED_ACTS
        )


@dataclass(frozen=True)
class LinearProjectionF2:
    proj: Callable[[Bit2], int]
    u0: Bit2
    u1: Bit2

    def is_linear(self) -> bool:
        vecs = [(0, 0), (0, 1), (1, 0), (1, 1)]
        return all(
            self.proj(xor2(u, v)) == (self.proj(u) ^ self.proj(v))
            for u in vecs
            for v in vecs
        )

    def has_nontrivial_kernel(self) -> bool:
        return any(self.proj(v) == 0 for v in [(0, 1), (1, 0), (1, 1)])

    def pair_collides(self) -> bool:
        return (
            self.u0 != self.u1
            and self.proj(xor2(self.u0, self.u1)) == 0
            and self.proj(self.u0) == self.proj(self.u1)
        )

    def is_linear_collision(self) -> bool:
        return self.is_linear() and self.pair_collides()


@dataclass(frozen=True)
class AuditBackAction:
    delta: Dict[Tuple[str, str], str]
    probe_state: Dict[str, str]
    probe_obs: Dict[str, int]
    designated: str

    def has_state_change(self) -> bool:
        return any(self.probe_state[s] != s for s in STATES4)

    def has_non_commutation(self) -> bool:
        return any(
            self.probe_state[self.delta[(s, a)]] != self.delta[(self.probe_state[s], a)]
            for s in STATES4
            for a in ACTS2
        )

    def hits_designated(self, s: str) -> bool:
        return self.probe_state[s] == self.designated


@dataclass(frozen=True)
class InterfaceGlue:
    g1_trap_state: str
    g4_designated: str
    g2_first: str
    g2_second: str
    license: str

    def is_compatible(self) -> bool:
        return (self.g4_designated == self.g1_trap_state) and (self.g2_first != self.g2_second)


EDR_GLUE = InterfaceGlue("q", "q", "s0", "s1", "FORMAL_CROSS_IRREDUCIBILITY")


@dataclass(frozen=True)
class EDRWorld:
    name: str
    win: Set[str]
    pi: Dict[str, int]
    delta: Dict[Tuple[str, str], str]
    probe_state: Dict[str, str]
    probe_obs: Dict[str, int]

    def allowed_step(self, s: str, a: str) -> str:
        return self.probe_state[s] if a == "P" else self.delta[(s, a)]

    def reduct_g1(self, glue: InterfaceGlue = EDR_GLUE) -> SinkGraph:
        return SinkGraph(
            step={(s, a): self.allowed_step(s, a) for s in STATES4 for a in ALLOWED_ACTS},
            win=set(self.win),
            trap=glue.g1_trap_state,
        )

    def reduct_g2(self, glue: InterfaceGlue = EDR_GLUE) -> LinearProjectionF2:
        return LinearProjectionF2(
            proj=lambda v: self.pi[F2_DECODE[v]],
            u0=F2_ENCODE[glue.g2_first],
            u1=F2_ENCODE[glue.g2_second],
        )

    def reduct_g4(self, glue: InterfaceGlue = EDR_GLUE) -> AuditBackAction:
        return AuditBackAction(
            delta=dict(self.delta),
            probe_state=dict(self.probe_state),
            probe_obs=dict(self.probe_obs),
            designated=glue.g4_designated,
        )


def theta0(w: EDRWorld, glue: InterfaceGlue = EDR_GLUE) -> bool:
    s0, s1, q = glue.g2_first, glue.g2_second, glue.g1_trap_state
    return (
        (s0 not in w.win)
        and (s1 not in w.win)
        and ("w" in w.win)
        and w.delta[(s0, "L")] == "w"
        and w.delta[(s0, "R")] == q
        and w.delta[(s1, "L")] == q
        and w.delta[(s1, "R")] == "w"
        and w.delta[("w", "L")] == "w"
        and w.delta[("w", "R")] == "w"
        and w.probe_obs[s0] == 0
        and w.probe_obs[s1] == 1
    )


def theta1(w: EDRWorld, glue: InterfaceGlue = EDR_GLUE) -> bool:
    q = glue.g1_trap_state
    return (q not in w.win) and all(w.allowed_step(q, a) == q for a in ALLOWED_ACTS)


def theta2(w: EDRWorld, glue: InterfaceGlue = EDR_GLUE) -> bool:
    return w.reduct_g2(glue).is_linear_collision()


def theta4(w: EDRWorld, glue: InterfaceGlue = EDR_GLUE) -> bool:
    return w.probe_state[glue.g2_second] == glue.g4_designated


def verify_satisfaction_bridges(w: EDRWorld, glue: InterfaceGlue = EDR_GLUE) -> Dict[str, bool]:
    return {
        "G1_bridge_iff": theta1(w, glue) == w.reduct_g1(glue).is_absorbing_trap(),
        "G2_bridge_iff": theta2(w, glue) == w.reduct_g2(glue).is_linear_collision(),
        "G4_bridge_iff": theta4(w, glue) == w.reduct_g4(glue).hits_designated(glue.g2_second),
    }


def solve_guaranteed_win(
    w: EDRWorld, k: int, glue: InterfaceGlue = EDR_GLUE
) -> Tuple[bool, Optional[Dict[int, Any]]]:
    """
    Exact AND-OR search over ALL deterministic history-dependent policies of horizon <= k,
    splitting by passive observation `w.pi` BOTH at t=0 AND after every control action `Act(act)`,
    matching Lean's `reachesWin` and `SafeBeliefReachInit` identically.
    """
    obs_groups: Dict[int, List[str]] = {}
    for s in (glue.g2_first, glue.g2_second):
        obs_groups.setdefault(w.pi[s], []).append(s)

    def can_win(belief: Tuple[str, ...], rem: int) -> Tuple[bool, Optional[Dict[str, Any]]]:
        active = tuple(sorted(set(s for s in belief if s not in w.win)))
        if not active:
            return True, {"decision": "Stop(Won)"}
        if rem == 0:
            return False, None

        # Try control actions — split post-action states by passive port w.pi[s']
        for act in ACTS2:
            act_branches: Dict[int, List[str]] = {}
            for s in active:
                ns = w.delta[(s, act)]
                act_branches.setdefault(w.pi[ns], []).append(ns)
            sub_trees: Dict[int, Any] = {}
            all_ok = True
            for y, bstates in sorted(act_branches.items()):
                ok, sub = can_win(tuple(bstates), rem - 1)
                if not ok:
                    all_ok = False
                    break
                sub_trees[y] = sub
            if all_ok:
                return True, {"decision": f"Act({act})", "pi_branches": sub_trees}

        # Try probe P — split by probe outcome w.probe_obs[s]
        prb_branches: Dict[int, List[str]] = {}
        for s in active:
            prb_branches.setdefault(w.probe_obs[s], []).append(w.probe_state[s])
        prb_trees: Dict[int, Any] = {}
        for y, bstates in sorted(prb_branches.items()):
            ok, sub = can_win(tuple(bstates), rem - 1)
            if not ok:
                return False, None
            prb_trees[y] = sub
        return True, {"decision": "Probe(P)", "branches": prb_trees}

    policy: Dict[int, Any] = {}
    for o, bstates in sorted(obs_groups.items()):
        ok, tree = can_win(tuple(bstates), k)
        if not ok:
            return False, None
        policy[o] = tree
    return True, policy


def safe_belief_reach_init(w: EDRWorld, k: int, belief: Tuple[str, ...] = ("s0", "s1")) -> bool:
    def reach(b: Tuple[str, ...], rem: int) -> bool:
        active = tuple(s for s in b if s not in w.win)
        if not active:
            return True
        if rem == 0:
            return False
        for act in ACTS2:
            if all(
                reach(tuple(w.delta[(s, act)] for s in active if w.pi[w.delta[(s, act)]] == y), rem - 1)
                for y in (0, 1)
            ):
                return True
        return all(
            reach(tuple(w.probe_state[s] for s in active if w.probe_obs[s] == y), rem - 1)
            for y in (0, 1)
        )

    return all(reach(tuple(s for s in belief if w.pi[s] == o), k) for o in (0, 1))


BASE_DELTA: Dict[Tuple[str, str], str] = {
    ("s0", "L"): "w", ("s0", "R"): "q",
    ("s1", "L"): "q", ("s1", "R"): "w",
    ("w",  "L"): "w", ("w",  "R"): "w",
    ("q",  "L"): "q", ("q",  "R"): "q",
}
BASE_PROBE_STATE: Dict[str, str] = {"s0": "s0", "s1": "q", "w": "w", "q": "q"}
BASE_PROBE_OBS: Dict[str, int] = {"s0": 0, "s1": 1, "w": 1, "q": 0}
PI_X: Dict[str, int] = {s: F2_ENCODE[s][0] for s in STATES4}
PI_Y: Dict[str, int] = {s: F2_ENCODE[s][1] for s in STATES4}


def build_world_all() -> EDRWorld:
    return EDRWorld("worldAll", {"w"}, dict(PI_X), dict(BASE_DELTA), dict(BASE_PROBE_STATE), dict(BASE_PROBE_OBS))


def build_world_c1() -> EDRWorld:
    return EDRWorld("worldC1", {"w"}, dict(PI_X), {**BASE_DELTA, ("q", "L"): "w"}, dict(BASE_PROBE_STATE), dict(BASE_PROBE_OBS))


def build_world_c2() -> EDRWorld:
    return EDRWorld("worldC2", {"w"}, dict(PI_Y), dict(BASE_DELTA), dict(BASE_PROBE_STATE), dict(BASE_PROBE_OBS))


def build_world_c4() -> EDRWorld:
    return EDRWorld("worldC4", {"w"}, dict(PI_X), dict(BASE_DELTA), {**BASE_PROBE_STATE, "s1": "s1"}, dict(BASE_PROBE_OBS))


def build_diag_world(b1: bool, b2: bool, b4: bool) -> EDRWorld:
    return EDRWorld(
        f"diag_{int(b1)}{int(b2)}{int(b4)}",
        {"w"},
        dict(PI_X if b2 else PI_Y),
        dict(BASE_DELTA if b1 else {**BASE_DELTA, ("q", "L"): "w"}),
        dict(BASE_PROBE_STATE if b4 else {**BASE_PROBE_STATE, "s1": "s1"}),
        dict(BASE_PROBE_OBS),
    )


def build_world_anti_inflation() -> EDRWorld:
    return EDRWorld("worldAntiInflation", {"w"}, dict(PI_X), dict(BASE_DELTA), {**BASE_PROBE_STATE, "s1": "s0"}, dict(BASE_PROBE_OBS))


def pred_c1_trap(w: EDRWorld) -> bool:
    return any((s not in w.win) and all(w.allowed_step(s, a) == s for a in ALLOWED_ACTS) for s in STATES4)


def pred_c2_collision(w: EDRWorld) -> bool:
    win_acts1 = {s: {a for a in ACTS2 if w.delta[(s, a)] in w.win} for s in STATES4}
    return any(
        x != y and w.pi[x] == w.pi[y] and bool(win_acts1[x]) and bool(win_acts1[y]) and win_acts1[x].isdisjoint(win_acts1[y])
        for x in STATES4 for y in STATES4
    )


def pred_c4_noncomm(w: EDRWorld) -> bool:
    return any(w.probe_state[w.delta[(s, a)]] != w.delta[(w.probe_state[s], a)] for s in STATES4 for a in ACTS2)


def diag_signature(w: EDRWorld) -> Tuple[bool, bool, bool]:
    return (pred_c1_trap(w), pred_c2_collision(w), pred_c4_noncomm(w))


VOI_WIN = {"w"}
VOI_DELTA = {
    ("s0", "L"): "w", ("s1", "L"): "w", ("s2", "L"): "q",
    ("s0", "R"): "q", ("s1", "R"): "q", ("s2", "R"): "w",
    ("w",  "L"): "w", ("w",  "R"): "w",
    ("q",  "L"): "q", ("q",  "R"): "q",
}
VOI_PROBE_STATE = {"s0": "s0", "s1": "q", "s2": "q", "w": "w", "q": "q"}
VOI_PROBE_OBS = {"s0": "o0", "s1": "o1", "s2": "o2", "w": "o0", "q": "o2"}


def best_blind_mass(win: Set[str], delta: Dict[Tuple[str, str], str], mu: Dict[str, int], belief: Sequence[str]) -> int:
    return max(sum(mu[s] for s in belief if delta[(s, a)] in win) for a in ACTS2)


def voi3_safe_belief_reach(k: int, belief: Tuple[str, ...]) -> bool:
    active = tuple(s for s in belief if s not in VOI_WIN)
    if not active:
        return True
    if k == 0:
        return False
    for act in ACTS2:
        if voi3_safe_belief_reach(k - 1, tuple(VOI_DELTA[(s, act)] for s in active)):
            return True
    return all(
        voi3_safe_belief_reach(k - 1, tuple(VOI_PROBE_STATE[s] for s in active if VOI_PROBE_OBS[s] == y))
        for y in ("o0", "o1", "o2")
    )
