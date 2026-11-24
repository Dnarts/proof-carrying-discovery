"""
certified_strategy_selection_v2_6.py — Reference Executable Engine for
Certified Strategy Selection under Memory, Budget, and Time Constraints (v2.6).

Pure Python 3 stdlib implementation mirroring all 7 sections (H1 through H12) of
`lean/certified_strategy_selection_v2_6.lean`:
  - Section 1 (H1)       : Unified 3-coordinate epistemic accessibility E(E) = <X_E, D_E, J_E>
  - Section 2 (H2/Gate13): Multi-symbol FIFO Queue automaton vs LIFO Stack automaton on Σ*
  - Section 3 (H3)       : Non-postulated computable detector `check_spurious_fin`
  - Section 4 (H4-H7+)   : Unified Controller `LicensedStep`, 5D `CostVec`, Ax4 privilege
                           separation, Gate 15/16 certificates, and fail-closed S0 auditor
  - Section 5 (H8)       : Algorithmic `MetaSynset` (`proj`, `find_split_axis`, `freeze`)
  - Section 6 (H9-H11)   : Typed `RevisionMemory` (`store`/`recover`), stream amortization,
                           and Rule 110 14-cell Ether Ring vs Zero-Background dichotomy
  - Section 7 (H12)      : Causal-Epistemic Horizon Synthesis (`RepairReach`, `compute_V_dyn`,
                           controller override, and `ContinuousSubject110` XOR-gate stream)
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple


# ==============================================================================
# SECTION 1: H1 — UNIFIED THREE-COORDINATE EPISTEMIC ACCESSIBILITY
# ==============================================================================

@dataclass(frozen=True)
class EpistemicEnv:
    name: str
    worlds: Tuple[Any, ...]
    hyps: Tuple[Any, ...]
    eval_h: Callable[[Any, Any], bool]
    port: Callable[[Any], Any]
    actions: Tuple[Any, ...]
    apply_action: Callable[[Any, Any], Any]
    target: Callable[[Any], bool]


def is_expressible(env: EpistemicEnv) -> bool:
    """Coordinate X_E: exists h in H_E such that eval_h(h, w) == target(w) on all w in W_E."""
    return any(
        all(env.eval_h(h, w) == env.target(w) for w in env.worlds)
        for h in env.hyps
    )


def is_distinguishable(env: EpistemicEnv) -> bool:
    """Coordinate D_E: all target-distinct world pairs (w1, w2) have port(w1) != port(w2)."""
    for w1 in env.worlds:
        for w2 in env.worlds:
            if env.target(w1) != env.target(w2) and env.port(w1) == env.port(w2):
                return False
    return True


def is_identifiable(env: EpistemicEnv) -> bool:
    """Coordinate J_E: X_E and D_E and interventional separability through port after action."""
    if not (is_expressible(env) and is_distinguishable(env)):
        return False
    for w1 in env.worlds:
        for w2 in env.worlds:
            if env.target(w1) != env.target(w2):
                if not any(
                    env.port(env.apply_action(a, w1)) != env.port(env.apply_action(a, w2))
                    for a in env.actions
                ):
                    return False
    return True


def evaluate_epistemic_coordinates(env: EpistemicEnv) -> Dict[str, bool]:
    return {
        "X_expressible": is_expressible(env),
        "D_distinguishable": is_distinguishable(env),
        "J_identifiable": is_identifiable(env),
    }


# ==============================================================================
# SECTION 2: H2 (GATE 13) — MULTI-SYMBOL FIFO QUEUE vs LIFO STACK AUTOMATA ON Σ*
# ==============================================================================

def eval_queue(inv: bool, cap: int, word: Sequence[str]) -> bool:
    """Level-4 FIFO Queue Automaton over Σ = {'0', '1', '#'}."""
    reading = True
    buf: List[bool] = []
    for sym in word:
        if reading:
            if sym in ("0", "1"):
                if len(buf) >= cap:
                    return False
                buf.append(sym == "1")
            elif sym == "#":
                reading = False
            else:
                return False
        else:
            if sym in ("0", "1"):
                if not buf:
                    return False
                head = buf.pop(0)  # FIFO dequeue from front
                bit = sym == "1"
                if bit != (head ^ inv):
                    return False
            else:
                return False
    return (not reading) and (len(buf) == 0)


def eval_stack(inv: bool, cap: int, word: Sequence[str]) -> bool:
    """Level-3 LIFO Stack Automaton over Σ = {'0', '1', '#'}."""
    reading = True
    buf: List[bool] = []
    for sym in word:
        if reading:
            if sym in ("0", "1"):
                if len(buf) >= cap:
                    return False
                buf.insert(0, sym == "1")  # LIFO push onto top
            elif sym == "#":
                reading = False
            else:
                return False
        else:
            if sym in ("0", "1"):
                if not buf:
                    return False
                head = buf.pop(0)  # LIFO pop from top
                bit = sym == "1"
                if bit != (head ^ inv):
                    return False
            else:
                return False
    return (not reading) and (len(buf) == 0)


# ==============================================================================
# SECTION 3: H3 — NON-POSTULATED COMPUTABLE DETECTOR `check_spurious_fin`
# ==============================================================================

def check_spurious_fin(
    worlds: Sequence[Any],
    queries: Sequence[Any],
    base_obs: Callable[[Any, Any], Any],
    ext_obs: Callable[[Any, Any], Tuple[Any, Any]],
) -> bool:
    """
    Computable Boolean detector verifying whether an extended port `ext_obs`
    is a spurious extension of `base_obs` over finite basis `queries` and `worlds`.
    """
    for q in queries:
        for w in worlds:
            if ext_obs(q, w)[0] != base_obs(q, w):
                return False
        for w1 in worlds:
            for w2 in worlds:
                if ext_obs(q, w1) != ext_obs(q, w2) and base_obs(q, w1) == base_obs(q, w2):
                    return False
    return True


# ==============================================================================
# SECTION 4: H4-H7+ — UNIFIED CONTROLLER, 5D COST VECTOR & FAIL-CLOSED S0 AUDITOR
# ==============================================================================

@dataclass(frozen=True)
class CostVec:
    cq: int = 0
    cs: int = 0
    cp: int = 0
    cv: int = 0
    cm: int = 0

    def add(self, other: CostVec) -> CostVec:
        return CostVec(
            self.cq + other.cq,
            self.cs + other.cs,
            self.cp + other.cp,
            self.cv + other.cv,
            self.cm + other.cm,
        )

    def le(self, budget: CostVec) -> bool:
        return (
            self.cq <= budget.cq
            and self.cs <= budget.cs
            and self.cp <= budget.cp
            and self.cv <= budget.cv
            and self.cm <= budget.cm
        )

    def to_dict(self) -> Dict[str, int]:
        return {"cq": self.cq, "cs": self.cs, "cp": self.cp, "cv": self.cv, "cm": self.cm}


@dataclass(frozen=True)
class TariffSchedule:
    probe_fee: int = 1
    lang_esc_fee: int = 4
    port_esc_fee: int = 3
    intervene_fee: int = 2
    mem_rec_fee: int = 1

    def validate_s0(self) -> bool:
        return (
            self.probe_fee > 0
            and self.lang_esc_fee > 0
            and self.port_esc_fee > 0
            and self.intervene_fee > 0
            and self.mem_rec_fee > 0
            and self.mem_rec_fee < self.lang_esc_fee
        )


@dataclass(frozen=True)
class UnifiedState:
    candidate_worlds: int
    active_hyps: int
    tier_rank: int  # 0=L0_Conj, 1=L1_DFA, 2=L2_1DCA, 3=L3_Stack, 4=L4_Queue
    port_rank: int
    int_rank: int
    knowledge_count: int
    spent: CostVec
    budget: CostVec

    def progress_score(self) -> int:
        return self.tier_rank + self.port_rank + self.int_rank + self.knowledge_count


def apply_licensed_step(
    state: UnifiedState,
    tariffs: TariffSchedule,
    step_kind: str,
    params: Dict[str, Any],
) -> Tuple[Optional[UnifiedState], str]:
    """
    Fail-closed S0 execution of a unified `LicensedStep`.
    Returns `(new_state, "OK")` if all structural certificates and vector budget constraints hold,
    or `(None, reason)` if any S0 guard fails.
    """
    if not tariffs.validate_s0():
        return None, "S0_REJECT: invalid_tariff_schedule"

    if step_kind == "probe":
        new_worlds = int(params["new_worlds"])
        if not (0 < new_worlds < state.candidate_worlds):
            return None, "S0_REJECT: probe_requires_strict_world_split"
        nxt_spent = state.spent.add(CostVec(cq=tariffs.probe_fee))
        if not nxt_spent.le(state.budget):
            return None, "S0_REJECT: vector_budget_exceeded_cq"
        return (
            UnifiedState(
                candidate_worlds=new_worlds,
                active_hyps=state.active_hyps,
                tier_rank=state.tier_rank,
                port_rank=state.port_rank,
                int_rank=state.int_rank,
                knowledge_count=state.knowledge_count + 1,
                spent=nxt_spent,
                budget=state.budget,
            ),
            "OK",
        )

    if step_kind == "escalateLang":
        signal = str(params["monitor_signal"])
        new_tier = int(params["new_tier_rank"])
        new_hyps = int(params["new_hyps"])
        if signal != "certifiedUnsat":
            return None, "S0_REJECT: Ax4_privilege_separation_blocks_non_structural_signal"
        if not (state.tier_rank < new_tier <= 4):
            return None, "S0_REJECT: escalate_lang_requires_strict_tier_increase"
        nxt_spent = state.spent.add(CostVec(cs=tariffs.lang_esc_fee))
        if not nxt_spent.le(state.budget):
            return None, "S0_REJECT: vector_budget_exceeded_cs"
        return (
            UnifiedState(
                candidate_worlds=state.candidate_worlds,
                active_hyps=new_hyps,
                tier_rank=new_tier,
                port_rank=state.port_rank,
                int_rank=state.int_rank,
                knowledge_count=state.knowledge_count + 1,
                spent=nxt_spent,
                budget=state.budget,
            ),
            "OK",
        )

    if step_kind == "escalatePort":
        signal = str(params["monitor_signal"])
        is_spurious = bool(params["is_spurious"])
        if signal != "certifiedUnsat":
            return None, "S0_REJECT: Ax4_privilege_separation_blocks_non_structural_signal"
        if is_spurious:
            return None, "S0_REJECT: H3_spurious_port_extension_blocked"
        nxt_spent = state.spent.add(CostVec(cp=tariffs.port_esc_fee))
        if not nxt_spent.le(state.budget):
            return None, "S0_REJECT: vector_budget_exceeded_cp"
        return (
            UnifiedState(
                candidate_worlds=state.candidate_worlds,
                active_hyps=state.active_hyps,
                tier_rank=state.tier_rank,
                port_rank=state.port_rank + 1,
                int_rank=state.int_rank,
                knowledge_count=state.knowledge_count + 1,
                spent=nxt_spent,
                budget=state.budget,
            ),
            "OK",
        )

    if step_kind == "intervene":
        obs_collision = bool(params["obs_collision"])
        mask_orthogonal = bool(params["control_mask_orthogonal"])
        commutator_nz = bool(params["commutator_nonzero"])
        new_worlds = int(params["new_worlds"])
        if not (obs_collision and mask_orthogonal and commutator_nz):
            return None, "S0_REJECT: Gate15_certificate_invalid"
        if not (new_worlds < state.candidate_worlds):
            return None, "S0_REJECT: intervene_requires_world_split"
        nxt_spent = state.spent.add(CostVec(cv=tariffs.intervene_fee))
        if not nxt_spent.le(state.budget):
            return None, "S0_REJECT: vector_budget_exceeded_cv"
        return (
            UnifiedState(
                candidate_worlds=new_worlds,
                active_hyps=state.active_hyps,
                tier_rank=state.tier_rank,
                port_rank=state.port_rank,
                int_rank=state.int_rank + 1,
                knowledge_count=state.knowledge_count + 1,
                spent=nxt_spent,
                budget=state.budget,
            ),
            "OK",
        )

    if step_kind == "stochasticReject":
        den = int(params["den"])
        total_mass = int(params["total_mass"])
        e_num = int(params["e_value_num"])
        e_den = int(params["e_value_den"])
        alpha_inv = int(params["alpha_inv"])
        has_gap_bound = bool(params["has_gap_bound"])
        new_hyps = int(params["new_hyps"])
        if not (den > 0 and total_mass > 0 and e_den > 0 and has_gap_bound):
            return None, "S0_REJECT: Gate16_positivity_or_gap_bound_failed"
        if not (e_num >= alpha_inv * e_den):
            return None, "S0_REJECT: Gate16_evalue_below_threshold"
        if not (new_hyps < state.active_hyps):
            return None, "S0_REJECT: Gate16_requires_hypothesis_elimination"
        nxt_spent = state.spent.add(CostVec(cq=tariffs.probe_fee))
        if not nxt_spent.le(state.budget):
            return None, "S0_REJECT: vector_budget_exceeded_cq"
        return (
            UnifiedState(
                candidate_worlds=state.candidate_worlds,
                active_hyps=new_hyps,
                tier_rank=state.tier_rank,
                port_rank=state.port_rank,
                int_rank=state.int_rank,
                knowledge_count=state.knowledge_count + 1,
                spent=nxt_spent,
                budget=state.budget,
            ),
            "OK",
        )

    if step_kind == "recoverMemory":
        precond_ok = bool(params["precond_ok"])
        new_tier = int(params["new_tier_rank"])
        if not precond_ok:
            return None, "S0_REJECT: H11_transfer_precondition_failed"
        if not (state.tier_rank < new_tier <= 4):
            return None, "S0_REJECT: recover_memory_requires_tier_gain"
        nxt_spent = state.spent.add(CostVec(cm=tariffs.mem_rec_fee))
        if not nxt_spent.le(state.budget):
            return None, "S0_REJECT: vector_budget_exceeded_cm"
        return (
            UnifiedState(
                candidate_worlds=state.candidate_worlds,
                active_hyps=state.active_hyps,
                tier_rank=new_tier,
                port_rank=state.port_rank,
                int_rank=state.int_rank,
                knowledge_count=state.knowledge_count + 1,
                spent=nxt_spent,
                budget=state.budget,
            ),
            "OK",
        )

    return None, f"S0_REJECT: unknown_step_kind_{step_kind}"


# ==============================================================================
# SECTION 5: H8 — ALGORITHMIC `MetaSynset` (`Proj`, `SplitAxis`, `Freeze`)
# ==============================================================================

@dataclass(frozen=True)
class DomainObj:
    domain_id: int
    obj_id: int
    features: Tuple[bool, ...]


def proj_feature(axis: int, obj: DomainObj) -> bool:
    return obj.features[axis]


def is_axial_split(candidates: Sequence[DomainObj], axis: int) -> bool:
    has_false = any(not proj_feature(axis, d) for d in candidates)
    has_true = any(proj_feature(axis, d) for d in candidates)
    return has_false and has_true


def freeze_axis_query(axis: int, candidates: Sequence[DomainObj], branch: bool) -> Tuple[DomainObj, ...]:
    return tuple(d for d in candidates if proj_feature(axis, d) == branch)


def minimax_gain(candidates: Sequence[DomainObj], axis: int) -> int:
    n0 = len(freeze_axis_query(axis, candidates, False))
    n1 = len(freeze_axis_query(axis, candidates, True))
    return len(candidates) - max(n0, n1)


def find_best_split_axis(candidates: Sequence[DomainObj], num_axes: int) -> Optional[Tuple[int, int]]:
    """
    Algorithmically discovers the optimal splitting feature axis without manual query menus.
    Returns `(best_axis, best_minimax_gain)` or `None` if no axis splits `candidates`.
    """
    best_axis: Optional[int] = None
    best_gain = 0
    for axis in range(num_axes):
        if is_axial_split(candidates, axis):
            g = minimax_gain(candidates, axis)
            if g > best_gain:
                best_gain = g
                best_axis = axis
    if best_axis is None:
        return None
    return best_axis, best_gain


# ==============================================================================
# SECTION 6: H9-H11 — TYPED `RevisionMemory` & RULE 110 RING AUTONOMY DICHOTOMY
# ==============================================================================

@dataclass(frozen=True)
class RevisionToken:
    token_id: int
    origin_domain: int
    port_width: int
    required_seam_inputs: int
    residual_gap_bound: int
    discover_cost: int
    transfer_cost: int


@dataclass(frozen=True)
class TargetEnv:
    env_id: int
    domain: int
    port_width: int
    is_port_autonomous: bool
    actual_seam_inputs: int
    max_allowed_gap: int


def verify_transfer_precond(tok: RevisionToken, env: TargetEnv) -> bool:
    return (
        tok.port_width == env.port_width
        and env.is_port_autonomous
        and env.actual_seam_inputs <= tok.required_seam_inputs
        and tok.residual_gap_bound <= env.max_allowed_gap
        and tok.transfer_cost < tok.discover_cost
    )


def recover_token(mem: Sequence[RevisionToken], env: TargetEnv) -> Optional[RevisionToken]:
    for tok in mem:
        if verify_transfer_precond(tok, env):
            return tok
    return None


def r110_local(left: int, center: int, right: int) -> int:
    pattern = (left << 2) | (center << 1) | right
    return (110 >> pattern) & 1


def ether_port4_automaton(bits4: Tuple[int, int, int, int]) -> Tuple[int, int, int, int]:
    """
    Autonomous 4-bit port W = {3, 4, 5, 6} transition on the 14-cell Rule 110 ether ring
    (where left boundary cell 2 is 1 and right boundary cell 7 is 0).
    """
    b3, b4, b5, b6 = bits4
    return (
        r110_local(1, b3, b4),
        r110_local(b3, b4, b5),
        r110_local(b4, b5, b6),
        r110_local(b5, b6, 0),
    )


def check_zero_bg_submask_autonomy(mask4: int) -> bool:
    """
    Checks whether a non-empty submask `mask4` (1..15) of W = {3, 4, 5, 6} is 1-step autonomous
    on the zero background when unmasked cells in W U {7} vary.
    Mirrors `Rule110RingDecoupling.zero_bg_non_autonomous_all_15`.
    """
    if mask4 <= 0 or mask4 > 15:
        return False
    seen: Dict[Tuple[int, ...], Tuple[int, ...]] = {}
    for w_bits in range(16):
        b3 = (w_bits >> 0) & 1
        b4 = (w_bits >> 1) & 1
        b5 = (w_bits >> 2) & 1
        b6 = (w_bits >> 3) & 1
        for b7 in (0, 1):
            nxt = (
                r110_local(0, b3, b4),
                r110_local(b3, b4, b5),
                r110_local(b4, b5, b6),
                r110_local(b5, b6, b7),
            )
            cur_proj = tuple(((w_bits >> i) & 1) for i in range(4) if (mask4 >> i) & 1)
            nxt_proj = tuple(nxt[i] for i in range(4) if (mask4 >> i) & 1)
            if cur_proj in seen and seen[cur_proj] != nxt_proj:
                return False
            seen[cur_proj] = nxt_proj
    return True


# ==============================================================================
# SECTION 7: H12 — CAUSAL-EPISTEMIC HORIZON SYNTHESIS & CONTINUOUS SUBJECT 110
# ==============================================================================

@dataclass(frozen=True)
class Rule110World:
    bits: Tuple[int, ...]

    def step_r110(self) -> Rule110World:
        n = len(self.bits)
        return Rule110World(
            tuple(
                r110_local(self.bits[(i - 1) % n], self.bits[i], self.bits[(i + 1) % n])
                for i in range(n)
            )
        )

    def evolve(self, steps: int) -> Rule110World:
        w = self
        for _ in range(steps):
            w = w.step_r110()
        return w


@dataclass(frozen=True)
class LocalAction:
    name: str
    indices: Tuple[int, ...]
    values: Tuple[int, ...]
    cost: int = 1

    def apply_action(self, world: Rule110World) -> Rule110World:
        arr = list(world.bits)
        for idx, val in zip(self.indices, self.values):
            arr[idx % len(arr)] = val
        return Rule110World(tuple(arr))


@dataclass(frozen=True)
class Observation:
    name: str
    window: Tuple[int, ...]
    delay: int = 1
    cost: int = 1

    def observe(self, world: Rule110World) -> Tuple[int, ...]:
        return tuple(world.bits[i % len(world.bits)] for i in self.window)


@dataclass(frozen=True)
class Invariant:
    name: str
    target_indices: Tuple[int, ...]
    expected: Tuple[int, ...]

    def holds(self, world: Rule110World) -> bool:
        return tuple(world.bits[i % len(world.bits)] for i in self.target_indices) == self.expected


def repair_reach(
    W: Iterable[Rule110World],
    t: int,
    t_star: int,
    actions: Sequence[LocalAction],
    inv: Invariant,
) -> Tuple[LocalAction, ...]:
    if t > t_star:
        return ()
    rem = t_star - t
    W_list = tuple(W)
    if not W_list:
        return ()
    return tuple(
        a for a in actions if all(inv.holds(a.apply_action(w).evolve(rem)) for w in W_list)
    )


def compute_V_dyn(
    W: Sequence[Rule110World],
    t: int,
    t_star: int,
    h: int,
    probes: Sequence[Observation],
    actions: Sequence[LocalAction],
    inv: Invariant,
) -> Tuple[Optional[int], Optional[Dict[str, Any]]]:
    if not W:
        return 0, {"kind": "Halt", "verdict": "INCONSISTENT"}

    best_cost: Optional[int] = None
    best_tree: Optional[Dict[str, Any]] = None

    for a in repair_reach(W, t, t_star, actions, inv):
        if best_cost is None or a.cost < best_cost:
            best_cost = a.cost
            best_tree = {"kind": "HaltRepair", "action": a.name, "action_cost": a.cost, "at_t": t}

    if h > 0:
        for q in probes:
            if t + q.delay > t_star:
                continue
            evolved = [w.evolve(q.delay) for w in W]
            branches_w: Dict[Tuple[int, ...], List[Rule110World]] = {}
            for ew in evolved:
                y = q.observe(ew)
                branches_w.setdefault(y, []).append(ew)

            worst_sub: Optional[int] = 0
            sub_trees: Dict[str, Any] = {}
            feasible = True
            for y, sub_w in sorted(branches_w.items()):
                sc, st = compute_V_dyn(sub_w, t + q.delay, t_star, h - 1, probes, actions, inv)
                if sc is None or st is None:
                    feasible = False
                    break
                if worst_sub is None or sc > worst_sub:
                    worst_sub = sc
                sub_trees[str(y)] = st

            if feasible and worst_sub is not None:
                total = q.cost + worst_sub
                if best_cost is None or total < best_cost:
                    best_cost = total
                    best_tree = {
                        "kind": "BranchWaitProbe",
                        "probe": q.name,
                        "delay": q.delay,
                        "probe_cost": q.cost,
                        "at_t": t,
                        "branches": sub_trees,
                    }

    return best_cost, best_tree


def select_causal_epistemic_action(
    W: Sequence[Rule110World],
    t: int,
    t_star: int,
    probe: Observation,
    actions: Sequence[LocalAction],
    inv: Invariant,
) -> Dict[str, Any]:
    """
    Unified v2.6 Causal-Epistemic Decision Operator:
    Checks whether waiting `probe.delay` preserves `RepairReach != ()` on every evolved branch.
    If waiting closes the causal repair horizon on any reachable branch, overrides passive probing
    with immediate surgical intervention from `RepairReach(W, t, t*)`.
    """
    evolved = [w.evolve(probe.delay) for w in W]
    branches: Dict[Tuple[int, ...], List[Rule110World]] = {}
    for ew in evolved:
        branches.setdefault(probe.observe(ew), []).append(ew)

    delayed_ok = (t + probe.delay <= t_star) and all(
        len(repair_reach(sub_w, t + probe.delay, t_star, actions, inv)) > 0
        for sub_w in branches.values()
    )
    if delayed_ok:
        return {"decision": "waitAndProbe", "probe": probe.name, "delay": probe.delay}

    imm = repair_reach(W, t, t_star, actions, inv)
    if imm:
        return {"decision": "immediateSurgicalRepair", "actuator": imm[0].name, "at_t": t}
    return {"decision": "failClosedUnsat", "at_t": t}
