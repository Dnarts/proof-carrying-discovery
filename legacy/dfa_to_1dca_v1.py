#!/usr/bin/env python3
"""
dfa_to_1dca_v1.py
Self-contained reproducible experiment (v1.0 release):
  1. Tier-0 (DFA(S_max)): Exact Myhill-Nerode observation table at K = 1..K_max.
     - If N_K <= S_max for all K, builds canonical quotient DFA (NO escalation).
     - If N_K > S_max, emits formal impossibility certificate for DFA(S_max)
       and escalates to Tier-1 (1-DCA).
  2. Tier-1 (1-DCA): Demand-driven backtracking synthesizer from scratch
     (12 empty cells, no A_0) with strict full-word end-marker semantics.
  3. Autonomous Linear Invariant Inference (NO external offset_for_inv):
     Derives phase-linear invariant coefficients (q0: c = a0*m + d0;
     q1: c = a1*m + b1*k + d1) directly from the synthesized transition equations,
     verifies Init / Step / Order-Rejection / Accept obligations symbolically,
     and outputs the inferred acceptance relation (m + d1 = k).
  4. Transfer (I1 -> I2): Extracts slope law (a0, b1) from I1 and reuses it
     in F on T2 = 0^n 1^(n+1) $, measuring node speedup vs no-law control.

Zero external dependencies (Python standard library only).
"""

import json
import platform
import sys
import time


# --- Oracles ---
def oracle_0plus1plus(w: str) -> bool:
    if not w.endswith("$"):
        return False
    body = w[:-1]
    if "0" not in body or "1" not in body:
        return False
    first_one = body.index("1")
    return all(c == "0" for c in body[:first_one]) and all(c == "1" for c in body[first_one:])


def oracle_0n1n_offset(offset: int):
    def oracle(w: str) -> bool:
        if not w.endswith("$"):
            return False
        body = w[:-1]
        if "0" not in body or "1" not in body:
            return False
        first_one = body.index("1")
        zeros = body[:first_one]
        ones = body[first_one:]
        if not (all(c == "0" for c in zeros) and all(c == "1" for c in ones)):
            return False
        return len(zeros) >= 1 and len(ones) >= 1 and (len(zeros) + offset == len(ones))
    return oracle


# --- Tier 0: Exact Myhill-Nerode Lower Bound & Quotient DFA ---
def myhill_nerode_table(oracle, K: int):
    prefixes = [""] + ["0" * i for i in range(1, K + 1)] + ["01", "01$", "1"]
    suffixes = ["", "$"] + ["1" * j + "$" for j in range(1, K + 1)] + ["01$"]
    rows = {}
    for p in prefixes:
        sig = tuple(oracle(p + s) for s in suffixes)
        if sig not in rows:
            rows[sig] = p
    return {
        "K": K,
        "distinct_classes": len(rows),
        "representatives": list(rows.values()),
        "suffixes": suffixes,
        "signatures": {rep: list(sig) for sig, rep in rows.items()},
    }


def build_quotient_dfa(oracle, K: int):
    tbl = myhill_nerode_table(oracle, K)
    reps = tbl["representatives"]
    suffixes = tbl["suffixes"]
    sig_to_id = {tuple(oracle(rep + s) for s in suffixes): idx for idx, rep in enumerate(reps)}
    start_state = sig_to_id[tuple(oracle("" + s) for s in suffixes)]
    accept_states = {sig_to_id[tuple(oracle(rep + s) for s in suffixes)] for rep in reps if oracle(rep)}
    transitions = {}
    for rep in reps:
        src = sig_to_id[tuple(oracle(rep + s) for s in suffixes)]
        for ch in ("0", "1", "$"):
            nxt_sig = tuple(oracle(rep + ch + s) for s in suffixes)
            if nxt_sig not in sig_to_id:
                return None
            transitions[(src, ch)] = sig_to_id[nxt_sig]
    return {
        "num_states": len(reps),
        "start": start_state,
        "accept": sorted(accept_states),
        "transitions": {f"{k[0]},{k[1]}": v for k, v in sorted(transitions.items())},
        "_raw": (start_state, accept_states, transitions),
    }


def run_dfa(dfa_raw, w: str) -> bool:
    q, accept_states, transitions = dfa_raw
    for ch in w:
        q = transitions[(q, ch)]
    return q in accept_states


# --- Tier 1: 1-DCA with strict full-word end-marker semantics ---
Q0, Q1, ACC, REJ = "q0", "q1", "acc", "rej"
S0, S1, SEND = "0", "1", "$"


def apply_delta(c: int, d: int):
    return None if c + d < 0 else c + d


def run_dca(table: dict, w: str) -> bool:
    q, c = Q0, 0
    for ch in w:
        if q in (ACC, REJ):
            return False  # Strict full-word semantics: trailing symbols after ACC/REJ are rejected
        z = 1 if c > 0 else 0
        nq, dc = table[(q, ch, z)]
        nc = apply_delta(c, dc)
        if nc is None:
            q, c = REJ, 0
        else:
            q, c = nq, nc
    return q == ACC


def infer_and_verify_linear_invariant(table: dict) -> dict:
    """
    Autonomous phase-linear invariant inference WITHOUT any external `offset_for_inv`.
    Derives (a0, b0, d0) for q0 and (a1, b1, d1) for q1 directly from the transition equations:
      1. Base (m=0, k=0, c=0 in q0) => d0 = 0, b0 = 0.
      2. q0 self-loop on '0' (z=0 and z=1) must agree => a0 = dc(q0, '0', 0) = dc(q0, '0', 1) > 0.
      3. Bridge (q0, '1', z=1) -> (q1, dc_bridge):
         At m >= 1, k = 1: c = a0*m + d0 + dc_bridge = a1*m + b1*1 + d1.
         Hence a1 = a0 and d1 = d0 + dc_bridge - b1.
      4. q1 self-loop on '1' (z=1) => b1 = dc(q1, '1', 1) < 0.
      5. Symbolic obligations:
         - q0 on '1' (z=0) -> REJ; q0 on '$' (z=0,1) -> REJ
         - q1 on '0' (z=0,1) -> REJ (strict 0*1* order)
         - q1 on '1' (z=0) -> REJ (no underflow)
         - q1 on '$' (z=0) -> (ACC, 0); q1 on '$' (z=1) -> REJ
         - Non-negativity at bridge for m=1: a0*1 + d0 + dc_bridge >= 0.
    """
    # Step 1: Base
    d0, b0 = 0, 0

    # Step 2: q0 on '0'
    nq0_0, dc0_0 = table[(Q0, S0, 0)]
    nq0_1, dc0_1 = table[(Q0, S0, 1)]
    if not (nq0_0 == Q0 and nq0_1 == Q0 and dc0_0 == dc0_1 and dc0_0 > 0):
        return {"found": False, "reason": "q0 self-loop on '0' is not a positive linear increment"}
    a0 = dc0_0

    # Step 3: q1 on '1' (z=1)
    nq1_1, dc1_1 = table[(Q1, S1, 1)]
    if not (nq1_1 == Q1 and dc1_1 < 0):
        return {"found": False, "reason": "q1 self-loop on '1' (z=1) is not a negative linear decrement"}
    b1 = dc1_1

    # Step 4: Bridge (q0, '1', z=1) -> q1
    nq_br, dc_br = table[(Q0, S1, 1)]
    if nq_br != Q1 or (a0 * 1 + d0 + dc_br < 0):
        return {"found": False, "reason": "bridge transition (q0, '1', z=1) invalid"}
    a1 = a0
    d1 = d0 + dc_br - b1

    # Step 5: Verify remaining symbolic obligations (Init / Step / Order / Accept)
    obligations = {
        "q0_s1_z0_rej": table[(Q0, S1, 0)][0] == REJ,
        "q0_end_z0_rej": table[(Q0, SEND, 0)][0] == REJ,
        "q0_end_z1_rej": table[(Q0, SEND, 1)][0] == REJ,
        "q1_s0_z0_rej": table[(Q1, S0, 0)][0] == REJ,
        "q1_s0_z1_rej": table[(Q1, S0, 1)][0] == REJ,
        "q1_s1_z0_rej": table[(Q1, S1, 0)][0] == REJ,
        "q1_end_z0_acc": table[(Q1, SEND, 0)] == (ACC, 0),
        "q1_end_z1_rej": table[(Q1, SEND, 1)][0] == REJ,
    }
    if not all(obligations.values()):
        return {"found": False, "reason": "symbolic safety/acceptance obligation failed", "obligations": obligations}

    return {
        "found": True,
        "method": "direct_equation_inference_no_offset_hint",
        "inv": {
            "q0_phase": f"c = {a0}*m + {d0}",
            "q1_phase": f"c = {a1}*m + ({b1})*k + ({d1})",
            "a0": a0, "b0": b0, "d0": d0,
            "a1": a1, "b1": b1, "d1": d1,
            "inferred_acceptance_relation": f"{a1}*m + ({b1})*k + ({d1}) = 0",
        },
        "obligations_verified": obligations,
    }


def legal_actions(sym: str, z: int):
    if sym == SEND:
        return [(REJ, 0), (ACC, 0)]
    dcs = (-1, 0, 1) if z == 1 else (0, 1)
    return [(REJ, 0)] + [(nq, dc) for nq in (Q0, Q1) for dc in dcs]


def actions_with_law(law, q: str, sym: str, z: int):
    base = legal_actions(sym, z)
    if law is None:
        return base
    a0, b1 = law
    if q == Q0 and sym == S0:
        return [tr for tr in base if tr == (Q0, a0)]
    if q == Q1 and sym == S1 and z == 1:
        return [tr for tr in base if tr == (Q1, b1)]
    return base


def eval_word_partial(pt: dict, w: str, lbl: bool):
    q, c = Q0, 0
    for ch in w:
        if q == ACC:
            return "ok" if not lbl else "mismatch"  # Strict full-word semantics
        if q == REJ:
            return "ok" if not lbl else "mismatch"
        z = 1 if c > 0 else 0
        key = (q, ch, z)
        if key not in pt:
            return ("missing", key)
        nq, dc = pt[key]
        nc = apply_delta(c, dc)
        if nc is None:
            q, c = REJ, 0
        else:
            q, c = nq, nc
    return "ok" if (q == ACC) == lbl else "mismatch"


def synthesize_1dca_from_scratch(dataset: list, law=None) -> dict:
    t0 = time.perf_counter()
    nodes = 0

    def bt(pt: dict):
        nonlocal nodes
        for w, lbl in dataset:
            st = eval_word_partial(pt, w, lbl)
            if st == "mismatch":
                return None
            if isinstance(st, tuple) and st[0] == "missing":
                cell = st[1]
                for act in actions_with_law(law, *cell):
                    nodes += 1
                    pt[cell] = act
                    res = bt(pt)
                    if res is not None:
                        return res
                    del pt[cell]
                return None
        full = dict(pt)
        for q in (Q0, Q1):
            for s in (S0, S1, SEND):
                for z in (0, 1):
                    full.setdefault((q, s, z), (REJ, 0))
        return full

    sol = bt({})
    return {
        "found": sol is not None,
        "nodes": nodes,
        "time_s": round(time.perf_counter() - t0, 6),
        "table": {f"{k[0]},{k[1]},{k[2]}": list(v) for k, v in sorted(sol.items())} if sol else None,
        "_raw_table": sol,
    }


def make_dataset(oracle):
    ds = []
    for m in range(5):
        for k in range(6):
            w = "0" * m + "1" * k + "$"
            ds.append((w, oracle(w)))
    for w in ["10$", "010$", "0101$", "00101$", "101$", "0110$"]:
        ds.append((w, oracle(w)))
    return ds


def check_ood(runner, oracle, offset_hint=0):
    ok, total = 0, 0
    for n in [10, 50, 100, 500]:
        for dm, dk in [(0, 0), (1, 0), (0, 1), (0, 2)]:
            w = "0" * (n + dm) + "1" * (n + offset_hint + dk) + "$"
            if runner(w) == oracle(w):
                ok += 1
            total += 1
    # Strict end-marker & order-violation checks
    for w in ["10$", "010$", "00101$", "0" * 50 + "1" * 50 + "0$", "01$$", "01$0", "01$1"]:
        if runner(w) == oracle(w):
            ok += 1
        total += 1
    return {"passed": ok, "total": total}


def fixed_engine_F(task_name: str, oracle, S_max: int = 5, K_max: int = 5, slope_law=None, ood_offset_hint: int = 0):
    mn_trace = []
    escalated = False
    trigger_K, trigger_N = None, None

    for K in range(1, K_max + 1):
        tbl = myhill_nerode_table(oracle, K)
        N_K = tbl["distinct_classes"]
        mn_trace.append({"K": K, "N_K": N_K, "representatives": tbl["representatives"]})
        if N_K > S_max:
            escalated = True
            trigger_K, trigger_N = K, N_K
            break

    if not escalated:
        dfa = build_quotient_dfa(oracle, K_max)
        if dfa is None:
            return {"task": task_name, "status": "UNCLOSED_TABLE", "mn_trace": mn_trace}
        ood = check_ood(lambda w: run_dfa(dfa["_raw"], w), oracle, 0)
        dfa.pop("_raw", None)
        return {
            "task": task_name,
            "S_max": S_max,
            "mn_trace": mn_trace,
            "escalated_to_1dca": False,
            "resolved_tier": "Tier-0 (DFA)",
            "dfa_solution": dfa,
            "ood_check_up_to_500_incl_end_markers": ood,
        }

    ds = make_dataset(oracle)
    synth = synthesize_1dca_from_scratch(ds, law=slope_law)
    raw_table = synth.pop("_raw_table", None)
    inv_res = infer_and_verify_linear_invariant(raw_table) if raw_table else {"found": False}
    ood = check_ood(lambda w: run_dca(raw_table, w), oracle, ood_offset_hint) if raw_table else {"passed": 0, "total": 0}
    return {
        "task": task_name,
        "S_max": S_max,
        "mn_trace": mn_trace,
        "escalated_to_1dca": True,
        "escalation_certificate": {
            "trigger_K": trigger_K,
            "observed_classes_N_K": trigger_N,
            "exceeds_S_max": f"{trigger_N} > {S_max}",
        },
        "resolved_tier": "Tier-1 (1-DCA)",
        "used_slope_law": list(slope_law) if slope_law else None,
        "dca_synthesis": synth,
        "inferred_invariant": inv_res,
        "ood_check_up_to_500_incl_end_markers": ood,
    }


def main():
    S_max, K_max = 5, 5
    res_neg = fixed_engine_F("T_neg_0plus1plus", oracle_0plus1plus, S_max=S_max, K_max=K_max, ood_offset_hint=0)
    res_t1 = fixed_engine_F("T1_0n1n", oracle_0n1n_offset(0), S_max=S_max, K_max=K_max, ood_offset_hint=0)
    inv1 = res_t1["inferred_invariant"]["inv"]
    slope_law = (inv1["a0"], inv1["b1"])

    res_t2_no_law = fixed_engine_F("T2_0n1n_plus_1_no_I1", oracle_0n1n_offset(1), S_max=S_max, K_max=K_max, slope_law=None, ood_offset_hint=1)
    res_t2_with_law = fixed_engine_F("T2_0n1n_plus_1_with_I1", oracle_0n1n_offset(1), S_max=S_max, K_max=K_max, slope_law=slope_law, ood_offset_hint=1)

    report = {
        "meta": {"python_version": sys.version.split()[0], "platform": platform.platform(), "S_max": S_max, "K_max": K_max},
        "T_neg_0plus1plus": res_neg,
        "T1_0n1n": res_t1,
        "T2_0n1n_plus_1": {
            "without_I1": res_t2_no_law,
            "with_I1": res_t2_with_law,
            "transfer_node_speedup": round(res_t2_no_law["dca_synthesis"]["nodes"] / res_t2_with_law["dca_synthesis"]["nodes"], 4),
        },
    }
    text = json.dumps(report, indent=2, ensure_ascii=False)
    with open("dfa_to_1dca_v1_results.json", "w", encoding="utf-8") as f:
        f.write(text)
    print(text)


if __name__ == "__main__":
    main()
