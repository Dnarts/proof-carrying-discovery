"""
fold_acc.py — Executable 5-state streaming mask fold & 4-state impossibility witness (Block C).

Exact Python mirror of Lean 4.36.0 module `repair_budget_atom_v1_2.lean`:
  - Mask2       : m00, m01, m10, m11
  - FoldAcc     : EMPTY, 00, 01, 10, 11
  - FoldVerdict : INCONSISTENT, NO_COMMON, HAS_COMMON
  - Differential test against exact set-intersection over arbitrary sequences
  - Constructive 5-state Moore machine + proof-by-check that no 4-state Moore
    automaton can compute `classify_fold ∘ fold_masks`
"""

from __future__ import annotations

import random
from typing import Dict, Iterable, List, Sequence, Tuple

MASKS: Tuple[str, ...] = ("00", "01", "10", "11")
FOLD_STATES: Tuple[str, ...] = ("EMPTY", "00", "01", "10", "11")
CANONICAL_PREFIXES: Tuple[Tuple[str, ...], ...] = (
    (),
    ("00",),
    ("01",),
    ("10",),
    ("11",),
)
SEPARATING_SUFFIXES: Tuple[Tuple[str, ...], ...] = (
    (),
    ("01",),
    ("10",),
)


def mask_and(a: str, b: str) -> str:
    if a == "11":
        return b
    if b == "11":
        return a
    if a == "01" and b == "01":
        return "01"
    if a == "10" and b == "10":
        return "10"
    return "00"


def fold_step(acc: str, m: str) -> str:
    if acc == "EMPTY":
        return m
    return mask_and(acc, m)


def fold_masks(ms: Iterable[str]) -> str:
    acc = "EMPTY"
    for m in ms:
        acc = fold_step(acc, m)
    return acc


def classify_fold(acc: str) -> str:
    if acc == "EMPTY":
        return "INCONSISTENT"
    if acc == "00":
        return "NO_COMMON"
    return "HAS_COMMON"


def naive_common_repair_verdict(ms: Sequence[str]) -> str:
    """Direct set-intersection oracle over A = {L, P}."""
    if len(ms) == 0:
        return "INCONSISTENT"
    common = {"L", "P"}
    for m in ms:
        allowed = set()
        if m[0] == "1":
            allowed.add("L")
        if m[1] == "1":
            allowed.add("P")
        common &= allowed
    return "HAS_COMMON" if common else "NO_COMMON"


def run_moore(delta: Dict[Tuple[int, str], int], q0: int, ms: Sequence[str]) -> int:
    q = q0
    for m in ms:
        q = delta[(q, m)]
    return q


def build_five_state_moore() -> Tuple[int, Dict[Tuple[int, str], int], Dict[int, str]]:
    """Constructive 5-state Moore machine computing classify_fold ∘ fold_masks."""
    idx = {s: i for i, s in enumerate(FOLD_STATES)}
    delta = {(idx[s], m): idx[fold_step(s, m)] for s in FOLD_STATES for m in MASKS}
    out = {idx[s]: classify_fold(s) for s in FOLD_STATES}
    return idx["EMPTY"], delta, out


def verify_five_state_moore_and_four_state_impossibility() -> Dict[str, object]:
    """
    1. Verify the 5-state Moore machine matches naive_common_repair_verdict on ALL
       sequences of length 0..5 (1 + 4 + 16 + 64 + 256 + 1024 = 1365 sequences).
    2. Verify Myhill-Nerode separation witness: all 5 canonical prefixes have pairwise
       distinct verdict signatures over SEPARATING_SUFFIXES, so by pigeonhole any
       deterministic Moore machine with <= 4 states merges at least two prefixes and
       therefore violates `out(run(ms)) == classify_fold(fold_masks(ms))` on a word
       of length <= 2.
    """
    q0, delta, out = build_five_state_moore()
    checked_exhaustive = 0
    # Exhaustive check for lengths 0..5
    seqs: List[Tuple[str, ...]] = [()]
    for _ in range(5):
        next_seqs: List[Tuple[str, ...]] = []
        for s in seqs:
            for m in MASKS:
                next_seqs.append(s + (m,))
        seqs = seqs + next_seqs
        # deduplicate only at end; better to generate by exact length
    all_seqs: List[Tuple[str, ...]] = [()]
    layer: List[Tuple[str, ...]] = [()]
    for _ in range(5):
        layer = [s + (m,) for s in layer for m in MASKS]
        all_seqs.extend(layer)

    for seq in all_seqs:
        v_moore = out[run_moore(delta, q0, seq)]
        v_naive = naive_common_repair_verdict(seq)
        assert v_moore == v_naive, f"Mismatch on {seq}: {v_moore} != {v_naive}"
        checked_exhaustive += 1

    # Compute signature table for the 5 canonical prefixes
    signatures: Dict[Tuple[str, ...], Tuple[str, ...]] = {}
    for pref in CANONICAL_PREFIXES:
        signatures[pref] = tuple(
            classify_fold(fold_masks(pref + suf)) for suf in SEPARATING_SUFFIXES
        )
    assert len(set(signatures.values())) == 5, "Expected 5 pairwise distinct signatures!"

    # Explicit witness: every pair of canonical prefixes has a concrete separating suffix
    pair_witnesses = 0
    for i, p1 in enumerate(CANONICAL_PREFIXES):
        for j, p2 in enumerate(CANONICAL_PREFIXES):
            if i >= j:
                continue
            seps = [
                suf
                for suf in SEPARATING_SUFFIXES
                if classify_fold(fold_masks(p1 + suf)) != classify_fold(fold_masks(p2 + suf))
            ]
            assert len(seps) >= 1, f"No separating suffix for {p1} vs {p2}"
            pair_witnesses += 1

    return {
        "five_state_exhaustive_len_0_to_5": checked_exhaustive,
        "distinct_myhill_nerode_signatures": len(set(signatures.values())),
        "pairwise_separated_pairs": pair_witnesses,
        "four_state_possible": False,
    }


def differential_test_fold(num_trials: int = 200_000, max_len: int = 12, seed: int = 20261124) -> int:
    """Differential test of fold_masks vs naive_common_repair_verdict on random sequences."""
    rng = random.Random(seed)
    for _ in range(num_trials):
        k = rng.randint(0, max_len)
        seq = [rng.choice(MASKS) for _ in range(k)]
        v_fold = classify_fold(fold_masks(seq))
        v_naive = naive_common_repair_verdict(seq)
        assert v_fold == v_naive, f"Mismatch on {seq}: {v_fold} != {v_naive}"
    return num_trials
