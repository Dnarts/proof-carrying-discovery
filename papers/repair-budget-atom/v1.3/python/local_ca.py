"""
local_ca.py — Genuinely local radius-1 1D multi-track Cellular Automaton (Block D).

Implements the 4-phase local protocol for the 2-action, 1-binary-probe Repair Budget Atom:
  - Phase 1 (FOLD_G)  : left-to-right 5-state FoldAcc sweep across world cells
  - Phase 2 (PREVIEW) : simultaneous branch-conditioned FoldAcc sweeps (acc_0, acc_1)
  - Phase 3 (BUDGET)  : local latching at BOUNDARY_R upon wavefront arrival
  - Phase 4 (EMIT)    : local evaluation of the 5 exhaustive verdicts (Prop. 3.6)

Hard architectural invariant:
  `local_transition(left, center, right)` inspects ONLY the 3-cell radius-1 neighborhood.
  No global tape reads occur inside the transition rule.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from itertools import product
from typing import List, Optional, Sequence, Tuple

from fold_acc import MASKS, fold_step
from reference_engine import RepairInstance, emit_verdict


@dataclass(frozen=True)
class CellState:
    role: str          # "BOUNDARY_L" | "WORLD" | "BOUNDARY_R" | "PAD"
    mask: str = "00"   # static world track: "00" | "01" | "10" | "11"
    pred: int = 0      # static world track: 0 | 1
    acc_g: str = "EMPTY"
    acc_0: str = "EMPTY"
    acc_1: str = "EMPTY"
    token: str = "IDLE"     # "IDLE" | "SWEEP" | "DONE" | "BUDGET_EVAL" | "EMITTED"
    verdict: str = "NONE"   # "NONE" | "INCONSISTENT" | "REPAIR" | "PROBE" | "BUDGET" | "NO_PLAN_IN_SCOPE"
    # Static hardware tariff registers (only active on BOUNDARY_R)
    c_L: int = 1
    c_P: int = 2
    c_q: int = 1
    B: int = 0


def mask_min_cost(acc: str, c_L: int, c_P: int) -> Optional[int]:
    """Local combinational cost decoder at BOUNDARY_R for 2-bit FoldAcc."""
    if acc in ("EMPTY", "00"):
        return None
    if acc == "10":
        return c_L
    if acc == "01":
        return c_P
    if acc == "11":
        return c_L if c_L <= c_P else c_P
    raise ValueError(f"Invalid FoldAcc state: {acc}")


def local_transition(left: CellState, center: CellState, right: CellState) -> CellState:
    """
    Pure radius-1 local transition rule δ(left, center, right) -> next_center.
    Zero global state access.
    """
    _ = right  # Right neighbor reserved for bidirectional extensions; unused in 1-way sweep

    if center.role == "BOUNDARY_L":
        if center.token == "SWEEP":
            return replace(center, token="DONE")
        return center

    if center.role == "WORLD":
        if center.token == "IDLE" and left.token == "SWEEP":
            next_g = fold_step(left.acc_g, center.mask)
            next_0 = fold_step(left.acc_0, center.mask) if center.pred == 0 else left.acc_0
            next_1 = fold_step(left.acc_1, center.mask) if center.pred == 1 else left.acc_1
            return replace(
                center,
                acc_g=next_g,
                acc_0=next_0,
                acc_1=next_1,
                token="SWEEP",
            )
        if center.token == "SWEEP":
            return replace(center, token="DONE")
        return center

    if center.role == "BOUNDARY_R":
        # Phase 3 (BUDGET): latch folded tracks when wavefront arrives from left neighbor
        if center.token == "IDLE" and left.token == "SWEEP":
            return replace(
                center,
                acc_g=left.acc_g,
                acc_0=left.acc_0,
                acc_1=left.acc_1,
                token="BUDGET_EVAL",
            )
        # Phase 4 (EMIT): local threshold decision
        if center.token == "BUDGET_EVAL":
            if center.acc_g == "EMPTY":
                return replace(center, verdict="INCONSISTENT", token="EMITTED")

            c_g = mask_min_cost(center.acc_g, center.c_L, center.c_P)
            if c_g is not None and c_g <= center.B:
                return replace(center, verdict="REPAIR", token="EMITTED")

            # Empty branch is excluded from worst-case max (cost 0); non-empty branch uses C(acc_y)
            c0 = 0 if center.acc_0 == "EMPTY" else mask_min_cost(center.acc_0, center.c_L, center.c_P)
            c1 = 0 if center.acc_1 == "EMPTY" else mask_min_cost(center.acc_1, center.c_L, center.c_P)

            if c0 is None or c1 is None:
                return replace(center, verdict="NO_PLAN_IN_SCOPE", token="EMITTED")

            v1 = center.c_q + (c0 if c0 >= c1 else c1)
            if v1 <= center.B:
                return replace(center, verdict="PROBE", token="EMITTED")
            return replace(center, verdict="BUDGET", token="EMITTED")

        return center

    return center


def build_initial_tape(
    segment: Sequence[Tuple[str, int]],
    c_L: int,
    c_P: int,
    c_q: int,
    B: int,
) -> List[CellState]:
    """Construct the initial 1D CA tape: [BOUNDARY_L, WORLD_1, ..., WORLD_L, BOUNDARY_R]."""
    tape: List[CellState] = [
        CellState(role="BOUNDARY_L", token="SWEEP"),
    ]
    for mask, pred in segment:
        tape.append(CellState(role="WORLD", mask=mask, pred=pred, token="IDLE"))
    tape.append(
        CellState(
            role="BOUNDARY_R",
            token="IDLE",
            c_L=c_L,
            c_P=c_P,
            c_q=c_q,
            B=B,
        )
    )
    return tape


def step_tape(tape: Sequence[CellState]) -> List[CellState]:
    """Synchronous global update applying pure local_transition to every cell."""
    pad = CellState(role="PAD")
    n = len(tape)
    return [
        local_transition(
            tape[i - 1] if i > 0 else pad,
            tape[i],
            tape[i + 1] if i + 1 < n else pad,
        )
        for i in range(n)
    ]


def run_ca(
    segment: Sequence[Tuple[str, int]],
    c_L: int,
    c_P: int,
    c_q: int,
    B: int,
) -> Tuple[str, int]:
    """
    Run the local 1D multi-track CA until BOUNDARY_R emits its verdict.
    Returns (verdict, ticks_elapsed).
    Communication + evaluation latency is strictly L + 2 ticks for radius r = 1.
    """
    tape = build_initial_tape(segment, c_L=c_L, c_P=c_P, c_q=c_q, B=B)
    expected_ticks = len(segment) + 2
    for tick in range(1, expected_ticks + 1):
        tape = step_tape(tape)
        if tape[-1].token == "EMITTED":
            return tape[-1].verdict, tick
    raise RuntimeError(f"CA failed to emit within {expected_ticks} ticks")


def segment_to_instance(
    segment: Sequence[Tuple[str, int]],
    c_L: int,
    c_P: int,
    c_q: int,
) -> RepairInstance:
    """Convert a 1D CA world segment into a RepairInstance for ReferenceEngine comparison."""
    worlds = tuple(f"w{i}" for i in range(len(segment)))
    repair_ok = {}
    obs_q = {}
    for i, (mask, pred) in enumerate(segment):
        w = f"w{i}"
        repair_ok[(w, "aL")] = (mask[0] == "1")
        repair_ok[(w, "aP")] = (mask[1] == "1")
        obs_q[("q", w)] = pred
    return RepairInstance(
        worlds=worlds,
        actions=("aL", "aP"),
        cost_a={"aL": c_L, "aP": c_P},
        repair_ok=repair_ok,
        probes=("q",),
        cost_q={"q": c_q},
        obs_q=obs_q,
    )


def verify_ca_equivalence_exhaustive(max_len: int = 4) -> dict:
    """
    Exhaustive bounded-segment equivalence verification (Block D2):
      CA(segment) == ReferenceEngine(segment)
    across ALL 8^L segments for L = 0..max_len and multiple tariff/budget regimes.
    """
    cell_alphabet = [(m, p) for m in MASKS for p in (0, 1)]
    regimes = [
        (1, 2, 1, 0),
        (1, 2, 1, 1),
        (1, 2, 1, 2),
        (1, 2, 1, 3),
        (1, 2, 2, 3),
        (1, 2, 2, 4),
        (2, 1, 0, 2),
    ]
    total_checks = 0
    verdict_counts = {
        "INCONSISTENT": 0,
        "REPAIR": 0,
        "PROBE": 0,
        "BUDGET": 0,
        "NO_PLAN_IN_SCOPE": 0,
    }
    false_guaranteed = 0

    for L in range(max_len + 1):
        for seg in product(cell_alphabet, repeat=L):
            for (c_L, c_P, c_q, B) in regimes:
                ca_verdict, ticks = run_ca(seg, c_L=c_L, c_P=c_P, c_q=c_q, B=B)
                assert ticks == L + 2, f"Unexpected latency {ticks} != {L + 2}"
                inst = segment_to_instance(seg, c_L=c_L, c_P=c_P, c_q=c_q)
                ref_verdict = emit_verdict(inst, B=B, h=1)["verdict"]
                if ca_verdict in ("REPAIR", "PROBE") and ref_verdict not in ("REPAIR", "PROBE"):
                    false_guaranteed += 1
                assert ca_verdict == ref_verdict, (
                    f"CA != Reference on L={L}, seg={seg}, params={(c_L, c_P, c_q, B)}: "
                    f"CA={ca_verdict}, REF={ref_verdict}"
                )
                verdict_counts[ca_verdict] += 1
                total_checks += 1

    return {
        "max_segment_len": max_len,
        "regimes_tested": len(regimes),
        "total_exhaustive_checks": total_checks,
        "mismatches": 0,
        "false_guaranteed_verdicts": false_guaranteed,
        "verdict_distribution": verdict_counts,
    }
