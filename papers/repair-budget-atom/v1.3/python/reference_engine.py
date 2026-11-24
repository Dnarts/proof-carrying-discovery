"""
reference_engine.py — Exact reference solver for the Repair Budget Atom (v1.3).

Implements:
  - compute_G(W)       : common safe repair set G(W) = ⋂_{ω ∈ W} R(ω)
  - compute_C(W)       : minimum immediate common repair cost C(W) ∈ Nat ∪ {+∞}
  - compute_V(W, h)    : exact minimax budget V_h(W) and optimal public PlanTree
  - emit_verdict       : exhaustive & disjoint 5-verdict classifier (Prop. 3.6)
  - generate_certificate & verify_certificate: independent fail-closed verifier

Zero external dependencies (Python 3 stdlib only).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, FrozenSet, Iterable, List, Optional, Tuple, Any

INF = None  # Extended natural infinity (+∞)


def cost_add(k: int, c: Optional[int]) -> Optional[int]:
    if c is None:
        return None
    return k + c


def cost_max(a: Optional[int], b: Optional[int]) -> Optional[int]:
    if a is None or b is None:
        return None
    return a if a >= b else b


def cost_lt(a: Optional[int], b: Optional[int]) -> bool:
    if a is None:
        return False
    if b is None:
        return True
    return a < b


def cost_le_budget(c: Optional[int], B: int) -> bool:
    return c is not None and c <= B


@dataclass(frozen=True)
class RepairInstance:
    """Finite deterministic instance (W, A, cost_a, R, Q, cost_q, f_q)."""
    worlds: Tuple[str, ...]
    actions: Tuple[str, ...]
    cost_a: Dict[str, int]
    repair_ok: Dict[Tuple[str, str], bool]
    probes: Tuple[str, ...]
    cost_q: Dict[str, int]
    obs_q: Dict[Tuple[str, str], Any]

    def __post_init__(self) -> None:
        for a in self.actions:
            if self.cost_a[a] < 0:
                raise ValueError(f"Negative action cost for {a}")
        for q in self.probes:
            if self.cost_q[q] < 0:
                raise ValueError(f"Negative probe cost for {q}")

    def safe_actions(self, w: str) -> FrozenSet[str]:
        return frozenset(a for a in self.actions if self.repair_ok.get((w, a), False))

    def branch(self, W: FrozenSet[str], q: str, y: Any) -> FrozenSet[str]:
        return frozenset(w for w in W if self.obs_q[(q, w)] == y)

    def reachable_answers(self, W: FrozenSet[str], q: str) -> Tuple[Any, ...]:
        ans = {self.obs_q[(q, w)] for w in W}
        return tuple(sorted(ans, key=lambda x: (str(type(x)), str(x))))


def compute_G(inst: RepairInstance, W: Iterable[str]) -> FrozenSet[str]:
    """Compute G(W) = ⋂_{ω ∈ W} R(ω). For empty W, returns frozenset(actions) by convention
    (empty W is handled explicitly as INCONSISTENT by emit_verdict)."""
    W_set = frozenset(W)
    if not W_set:
        return frozenset(inst.actions)
    acc: Optional[FrozenSet[str]] = None
    for w in W_set:
        rw = inst.safe_actions(w)
        acc = rw if acc is None else (acc & rw)
    return acc if acc is not None else frozenset()


def compute_C(inst: RepairInstance, W: Iterable[str]) -> Tuple[Optional[int], Optional[str]]:
    """Compute C(W) = min_{a ∈ G(W)} c(a) with deterministic tie-breaking by action order."""
    G = compute_G(inst, W)
    best_cost: Optional[int] = None
    best_action: Optional[str] = None
    for a in inst.actions:
        if a in G:
            ca = inst.cost_a[a]
            if best_cost is None or ca < best_cost:
                best_cost = ca
                best_action = a
    return best_cost, best_action


def compute_V(
    inst: RepairInstance,
    W: Iterable[str],
    h: int,
) -> Tuple[Optional[int], Optional[Dict[str, Any]]]:
    """
    Exact minimax recursion V_h(W) with memoization over (frozenset(W), h).
    Returns (V_h_cost, optimal_plan_tree_or_None).

    PlanTree nodes are strictly public (branching on public answers y, never on hidden W):
      - {"kind": "HaltRepair", "action": a, "action_cost": c(a)}
      - {"kind": "BranchProbe", "probe": q, "probe_cost": c(q), "branches": {str(y): subtree}}
    """
    if h < 0:
        raise ValueError("Horizon h must be >= 0")

    W0 = frozenset(W)
    if not W0:
        return 0, None

    memo: Dict[Tuple[FrozenSet[str], int], Tuple[Optional[int], Optional[Dict[str, Any]]]] = {}

    def solve(W_cur: FrozenSet[str], rem_h: int) -> Tuple[Optional[int], Optional[Dict[str, Any]]]:
        key = (W_cur, rem_h)
        if key in memo:
            return memo[key]

        # Option 1: immediate common repair (always available at any horizon >= 0)
        best_cost, best_act = compute_C(inst, W_cur)
        best_tree: Optional[Dict[str, Any]] = (
            {"kind": "HaltRepair", "action": best_act, "action_cost": best_cost}
            if best_cost is not None and best_act is not None
            else None
        )

        # Option 2: probe q ∈ Q and recurse with horizon rem_h - 1
        if rem_h > 0:
            for q in inst.probes:
                cq = inst.cost_q[q]
                answers = inst.reachable_answers(W_cur, q)
                worst_branch_cost: Optional[int] = 0
                branch_trees: Dict[str, Any] = {}
                feasible = True
                for y in answers:
                    Wy = inst.branch(W_cur, q, y)
                    if not Wy:
                        continue
                    sub_cost, sub_tree = solve(Wy, rem_h - 1)
                    if sub_cost is None or sub_tree is None:
                        feasible = False
                        break
                    worst_branch_cost = cost_max(worst_branch_cost, sub_cost)
                    branch_trees[repr(y)] = sub_tree
                if feasible:
                    total_cost = cost_add(cq, worst_branch_cost)
                    if cost_lt(total_cost, best_cost):
                        best_cost = total_cost
                        best_tree = {
                            "kind": "BranchProbe",
                            "probe": q,
                            "probe_cost": cq,
                            "branches": branch_trees,
                        }

        memo[key] = (best_cost, best_tree)
        return best_cost, best_tree

    return solve(W0, h)


def emit_verdict(
    inst: RepairInstance,
    B: int,
    h: int,
    W: Optional[Iterable[str]] = None,
) -> Dict[str, Any]:
    """
    Classify (W, B, h) into exactly one of the 5 deterministic verdicts (Proposition 3.6):
      - INCONSISTENT      : W = ∅
      - REPAIR            : W ≠ ∅, C(W) ≤ B
      - PROBE             : W ≠ ∅, V_h(W) ≤ B < C(W)
      - BUDGET            : W ≠ ∅, B < V_h(W) < +∞
      - NO_PLAN_IN_SCOPE  : W ≠ ∅, V_h(W) = +∞
    """
    W_set = frozenset(inst.worlds if W is None else W)
    if not W_set:
        return {
            "verdict": "INCONSISTENT",
            "W_size": 0,
            "B": B,
            "h": h,
            "C_W": None,
            "V_h_W": None,
            "action": None,
            "first_probe": None,
            "plan_tree": {"kind": "Halt", "verdict": "INCONSISTENT"},
        }

    c_w, act_w = compute_C(inst, W_set)
    v_w, plan_tree = compute_V(inst, W_set, h)

    if cost_le_budget(c_w, B):
        return {
            "verdict": "REPAIR",
            "W_size": len(W_set),
            "B": B,
            "h": h,
            "C_W": c_w,
            "V_h_W": v_w,
            "action": act_w,
            "first_probe": None,
            "plan_tree": {"kind": "HaltRepair", "action": act_w, "action_cost": c_w},
        }

    if cost_le_budget(v_w, B):
        assert plan_tree is not None and plan_tree["kind"] == "BranchProbe"
        return {
            "verdict": "PROBE",
            "W_size": len(W_set),
            "B": B,
            "h": h,
            "C_W": c_w,
            "V_h_W": v_w,
            "action": None,
            "first_probe": plan_tree["probe"],
            "plan_tree": plan_tree,
        }

    if v_w is not None:
        return {
            "verdict": "BUDGET",
            "W_size": len(W_set),
            "B": B,
            "h": h,
            "C_W": c_w,
            "V_h_W": v_w,
            "action": None,
            "first_probe": None,
            "plan_tree": {"kind": "Halt", "verdict": "BUDGET", "B": B, "h": h},
        }

    return {
        "verdict": "NO_PLAN_IN_SCOPE",
        "W_size": len(W_set),
        "B": B,
        "h": h,
        "C_W": c_w,
        "V_h_W": None,
        "action": None,
        "first_probe": None,
        "plan_tree": {"kind": "Halt", "verdict": "NO_PLAN_IN_SCOPE", "h": h},
    }


def generate_certificate(
    inst: RepairInstance,
    B: int,
    h: int,
    W: Optional[Iterable[str]] = None,
) -> Dict[str, Any]:
    """Emit a self-contained JSON-serializable certificate with per-world execution trace."""
    W_set = frozenset(inst.worlds if W is None else W)
    res = emit_verdict(inst, B, h, W_set)

    proof_trace: List[Dict[str, Any]] = []
    if res["verdict"] in ("REPAIR", "PROBE"):
        tree = res["plan_tree"]
        for w in sorted(W_set):
            node = tree
            spent = 0
            steps = 0
            path: List[Dict[str, Any]] = []
            while node["kind"] == "BranchProbe":
                q = node["probe"]
                y = inst.obs_q[(q, w)]
                cq = inst.cost_q[q]
                spent += cq
                steps += 1
                path.append({"probe": q, "answer": repr(y), "probe_cost": cq})
                node = node["branches"][repr(y)]
            act = node["action"]
            ca = inst.cost_a[act]
            spent += ca
            proof_trace.append({
                "world": w,
                "steps": steps,
                "path": path,
                "action": act,
                "action_cost": ca,
                "total_cost": spent,
                "safe": bool(inst.repair_ok.get((w, act), False)),
            })

    return {
        "schema": "repair-budget-atom/certificate/v1.3",
        "W_size": res["W_size"],
        "B": B,
        "h": h,
        "C_W": res["C_W"],
        "V_h_W": res["V_h_W"],
        "verdict": res["verdict"],
        "action": res["action"],
        "first_probe": res["first_probe"],
        "plan_tree": res["plan_tree"],
        "proof_trace": proof_trace,
    }


def verify_certificate(
    inst: RepairInstance,
    cert: Dict[str, Any],
    W: Optional[Iterable[str]] = None,
) -> Tuple[bool, str]:
    """
    Independent fail-closed verifier for a certificate.
    Checks:
      1. Guaranteed verdicts (REPAIR / PROBE) execute strictly via public answers y,
         stay within horizon h and budget B on EVERY ω ∈ W, and apply a safe action.
      2. Negative verdicts (INCONSISTENT / BUDGET / NO_PLAN_IN_SCOPE) agree with exact V_h(W).
    """
    W_set = frozenset(inst.worlds if W is None else W)
    B = cert["B"]
    h = cert["h"]
    verdict = cert["verdict"]

    if not W_set:
        return (verdict == "INCONSISTENT", "Empty W must emit INCONSISTENT")
    if verdict == "INCONSISTENT":
        return (False, "Non-empty W emitted INCONSISTENT")

    if verdict in ("REPAIR", "PROBE"):
        tree = cert["plan_tree"]
        if verdict == "REPAIR" and tree.get("kind") != "HaltRepair":
            return (False, "REPAIR certificate must have HaltRepair root")
        if verdict == "PROBE" and tree.get("kind") != "BranchProbe":
            return (False, "PROBE certificate must have BranchProbe root")

        for w in W_set:
            node = tree
            spent = 0
            depth = 0
            while node.get("kind") == "BranchProbe":
                q = node["probe"]
                if q not in inst.probes:
                    return (False, f"Probe {q} not in menu Q")
                spent += inst.cost_q[q]
                depth += 1
                if depth > h:
                    return (False, f"PlanTree exceeded horizon h={h} on world {w}")
                y_key = repr(inst.obs_q[(q, w)])
                branches = node.get("branches", {})
                if y_key not in branches:
                    return (False, f"Missing public branch {y_key} for probe {q} on world {w}")
                node = branches[y_key]
            if node.get("kind") != "HaltRepair":
                return (False, f"Leaf is not HaltRepair on world {w}")
            act = node["action"]
            if act not in inst.actions:
                return (False, f"Action {act} not in menu A")
            if not inst.repair_ok.get((w, act), False):
                return (False, f"UNSAFE repair {act} on world {w}")
            spent += inst.cost_a[act]
            if spent > B:
                return (False, f"Budget exceeded on world {w}: {spent} > {B}")
        return (True, "OK")

    # Non-guaranteed verdicts: verify against exact C(W) and V_h(W)
    c_w, _ = compute_C(inst, W_set)
    v_w, _ = compute_V(inst, W_set, h)
    if verdict == "BUDGET":
        ok = (v_w is not None) and (B < v_w) and (not cost_le_budget(c_w, B))
        return (ok, "OK" if ok else f"Invalid BUDGET verdict for C={c_w}, V={v_w}, B={B}")
    if verdict == "NO_PLAN_IN_SCOPE":
        ok = v_w is None
        return (ok, "OK" if ok else f"Invalid NO_PLAN_IN_SCOPE verdict for V={v_w}")
    return (False, f"Unknown verdict: {verdict}")
