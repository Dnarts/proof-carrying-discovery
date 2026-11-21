#!/usr/bin/env python3
"""
abc_shapley_v1.py
Self-contained reproducible experiment (v1.0 release):
  1. Separates Macro Abstraction (B - A) from Discovered Algebraic Laws as Search Methods (C - B_nand_law)
     under a fixed BFS straight-line Boolean DAG synthesizer F.
  2. Computes exact 8-coalition interventional Shapley values W(e1), W(e2), W(e3) with B_max = 200,000
     for the 3 discovery events:
       - e1: NAND_law  (autonomously discovered commutativity of NAND)
       - e2: XOR_macro (synthesized XOR operator from NAND)
       - e3: XOR_laws  (autonomously discovered laws of XOR; active iff e2 in S)
     using bounded log-speedup v_tau(S) = ln(min(C_empty, B_max)) - ln(min(C_S, B_max)).

Zero external dependencies (Python standard library only).
"""

import json
import math
import platform
import sys
import time
from itertools import combinations, product

NAND_TT = 0b0111
B_MAX = 200_000


def eval_op_bit(tt: int, a: int, b: int) -> int:
    return (tt >> ((a << 1) | b)) & 1


def eval_op_vec(tt: int, va: int, vb: int, mask: int) -> int:
    na = (~va) & mask
    nb = (~vb) & mask
    res = 0
    if tt & 1:
        res |= na & nb
    if tt & 2:
        res |= na & vb
    if tt & 4:
        res |= va & nb
    if tt & 8:
        res |= va & vb
    return res


def make_input_vecs(n_inputs: int):
    n_rows = 1 << n_inputs
    mask = (1 << n_rows) - 1
    vecs = []
    for var in range(n_inputs):
        v = 0
        for row in range(n_rows):
            if (row >> var) & 1:
                v |= 1 << row
        vecs.append(v)
    return vecs, mask


def eval_dag(gates, n_inputs: int, op_map: dict) -> int:
    vecs, mask = make_input_vecs(n_inputs)
    wires = list(vecs)
    for op_name, i, j in gates:
        wires.append(eval_op_vec(op_map[op_name], wires[i], wires[j], mask))
    return wires[-1]


def discover_laws(op_name: str, tt: int) -> dict:
    checks = 0
    counterexamples = {}
    comm = True
    for a, b in product((0, 1), repeat=2):
        checks += 1
        if eval_op_bit(tt, a, b) != eval_op_bit(tt, b, a):
            comm = False
            counterexamples["commutative"] = {"a": a, "b": b}
            break
    assoc = True
    for a, b, c in product((0, 1), repeat=3):
        checks += 1
        lhs = eval_op_bit(tt, eval_op_bit(tt, a, b), c)
        rhs = eval_op_bit(tt, a, eval_op_bit(tt, b, c))
        if lhs != rhs:
            assoc = False
            counterexamples["associative"] = {"a": a, "b": b, "c": c, "lhs": lhs, "rhs": rhs}
            break
    idemp = True
    for a in (0, 1):
        checks += 1
        if eval_op_bit(tt, a, a) != a:
            idemp = False
            counterexamples["idempotent"] = {"a": a, "val": eval_op_bit(tt, a, a)}
            break
    c0, c1 = eval_op_bit(tt, 0, 0), eval_op_bit(tt, 1, 1)
    checks += 2
    self_const = c0 if c0 == c1 else None
    if self_const is None:
        counterexamples["self_const"] = {"op(0,0)": c0, "op(1,1)": c1}
    ident = None
    for e in (0, 1):
        ok = True
        for a in (0, 1):
            checks += 2
            if eval_op_bit(tt, a, e) != a or eval_op_bit(tt, e, a) != a:
                ok = False
                break
        if ok:
            ident = e
            break
    if ident is None:
        counterexamples["identity"] = "neither 0 nor 1 is a two-sided identity"
    return {
        "op": op_name, "tt": tt, "commutative": comm, "associative": assoc,
        "idempotent": idemp, "self_const": self_const, "identity": ident,
        "law_checks": checks, "counterexamples": counterexamples,
    }


def normalize_nf(op_name: str, nf_a, nf_b, law: dict):
    if law is None:
        return (op_name, (nf_a, nf_b))
    if nf_a == nf_b:
        if law["self_const"] is not None:
            return ("CONST", law["self_const"])
        if law["idempotent"]:
            return nf_a
    ident = law["identity"]
    if ident is not None:
        if nf_a == ("CONST", ident):
            return nf_b
        if nf_b == ("CONST", ident):
            return nf_a
    if law["associative"] and law["commutative"]:
        args = []
        for x in (nf_a, nf_b):
            if isinstance(x, tuple) and x[0] == op_name:
                args.extend(x[1])
            else:
                args.append(x)
        if ident is not None:
            args = [x for x in args if x != ("CONST", ident)]
        args.sort()
        if law["self_const"] is not None:
            new_args, idx = [], 0
            while idx < len(args):
                if idx + 1 < len(args) and args[idx] == args[idx + 1]:
                    if law["self_const"] != ident:
                        new_args.append(("CONST", law["self_const"]))
                    idx += 2
                else:
                    new_args.append(args[idx])
                    idx += 1
            args = sorted(new_args)
        elif law["idempotent"]:
            args = sorted(set(args))
        if len(args) == 0 and ident is not None:
            return ("CONST", ident)
        if len(args) == 1:
            return args[0]
        return (op_name, tuple(args))
    if law["commutative"]:
        return (op_name, (nf_a, nf_b) if nf_a <= nf_b else (nf_b, nf_a))
    return (op_name, (nf_a, nf_b))


def synthesize(target_tt: int, n_inputs: int, ops: list, laws: dict, max_gates: int, budget: int) -> dict:
    t0 = time.perf_counter()
    in_vecs, mask = make_input_vecs(n_inputs)
    op_map = dict(ops)
    init_nfs = tuple(("VAR", i) for i in range(n_inputs))
    init_state = (tuple(in_vecs), init_nfs, ())
    for i, v in enumerate(in_vecs):
        if v == target_tt:
            return {"found": True, "verified": True, "gates": [], "depth": 0, "evals": 1, "time_s": round(time.perf_counter() - t0, 6)}
    evals = 0
    frontier = [init_state]
    for depth in range(1, max_gates + 1):
        next_frontier = []
        seen_states = set()
        for vecs, nfs, gates in frontier:
            n_wires = len(vecs)
            nf_set = set(nfs)
            for op_name, op_tt in ops:
                law = laws.get(op_name)
                comm = bool(law and law["commutative"])
                for i in range(n_wires):
                    j_start = i if comm else 0
                    for j in range(j_start, n_wires):
                        nf = normalize_nf(op_name, nfs[i], nfs[j], law)
                        if nf in nf_set:
                            continue
                        new_nfs = nfs + (nf,)
                        state_key = frozenset(new_nfs)
                        if state_key in seen_states:
                            continue
                        seen_states.add(state_key)
                        evals += 1
                        new_vec = eval_op_vec(op_tt, vecs[i], vecs[j], mask)
                        new_gates = gates + ((op_name, i, j),)
                        if new_vec == target_tt:
                            verified = eval_dag(new_gates, n_inputs, op_map) == target_tt
                            return {"found": True, "verified": verified, "gates": [list(g) for g in new_gates], "depth": depth, "evals": evals, "time_s": round(time.perf_counter() - t0, 6)}
                        if evals >= budget:
                            return {"found": False, "verified": False, "gates": None, "depth": depth, "evals": evals, "time_s": round(time.perf_counter() - t0, 6)}
                        if depth < max_gates:
                            next_frontier.append((vecs + (new_vec,), new_nfs, new_gates))
        frontier = next_frontier
    return {"found": False, "verified": False, "gates": None, "depth": max_gates, "evals": evals, "time_s": round(time.perf_counter() - t0, 6)}


def compute_shapley(players: list, v_map: dict) -> dict:
    n = len(players)
    fact = [math.factorial(k) for k in range(n + 1)]
    shapley = {}
    for p in players:
        others = [x for x in players if x != p]
        val = 0.0
        for r in range(len(others) + 1):
            w = fact[r] * fact[n - r - 1] / fact[n]
            for sub in combinations(others, r):
                s_key = tuple(sorted(sub))
                sp_key = tuple(sorted(sub + (p,)))
                val += w * (v_map[sp_key] - v_map[s_key])
        shapley[p] = round(val, 6)
    return shapley


def run_all():
    nand_law = discover_laws("NAND", NAND_TT)
    v2, _ = make_input_vecs(2)
    t1_res = synthesize(v2[0] ^ v2[1], 2, [("NAND", NAND_TT)], {}, 4, B_MAX)
    xor_tt = eval_dag(t1_res["gates"], 2, {"NAND": NAND_TT})
    xor_law = discover_laws("XOR", xor_tt)

    v3, _ = make_input_vecs(3)
    v4, _ = make_input_vecs(4)
    tasks = [
        ("T2_parity3", v3[0] ^ v3[1] ^ v3[2], 3, 4),
        ("T3_parity4", v4[0] ^ v4[1] ^ v4[2] ^ v4[3], 4, 3),
        ("T_neg_and3", v3[0] & v3[1] & v3[2], 3, 4),
    ]

    players = ["e1_NAND_law", "e2_XOR_macro", "e3_XOR_laws"]
    all_coalitions = [tuple(sorted(c)) for r in range(len(players) + 1) for c in combinations(players, r)]

    shapley_report = {}
    for task_name, target_tt, n_in, max_g in tasks:
        coalition_costs = {}
        for S in all_coalitions:
            s_set = set(S)
            ops = [("NAND", NAND_TT)]
            if "e2_XOR_macro" in s_set:
                ops.append(("XOR", xor_tt))
            laws = {}
            if "e1_NAND_law" in s_set:
                laws["NAND"] = nand_law
            # Interventional semantics: e3_XOR_laws acts iff e2_XOR_macro is present in S
            if "e3_XOR_laws" in s_set and "e2_XOR_macro" in s_set:
                laws["XOR"] = xor_law
            res = synthesize(target_tt, n_in, ops, laws, max_g, B_MAX)
            eff_cost = res["evals"] if res["found"] else B_MAX
            coalition_costs[S] = {"found": res["found"], "evals": res["evals"], "capped_cost": eff_cost}

        c_empty = coalition_costs[()]["capped_cost"]
        v_map = {S: math.log(c_empty) - math.log(coalition_costs[S]["capped_cost"]) for S in all_coalitions}
        sh = compute_shapley(players, v_map)
        v_full = round(v_map[tuple(sorted(players))], 6)
        shapley_report[task_name] = {
            "coalitions": {
                ",".join(S) if S else "EMPTY": {
                    "found": coalition_costs[S]["found"],
                    "capped_cost": coalition_costs[S]["capped_cost"],
                    "v_nats": round(v_map[S], 6),
                }
                for S in all_coalitions
            },
            "shapley_W_nats": sh,
            "efficiency_check_sum_W": round(sum(sh.values()), 6),
            "v_full_nats": v_full,
        }

    # Uniform mixture mu = (1/3, 1/3, 1/3)
    mu_shapley = {
        p: round(sum(shapley_report[t]["shapley_W_nats"][p] for t, _, _, _ in tasks) / len(tasks), 6)
        for p in players
    }

    report = {
        "meta": {"python_version": sys.version.split()[0], "platform": platform.platform(), "B_max": B_MAX},
        "discovered_laws": {"NAND": nand_law, "XOR": xor_law},
        "shapley_8_coalitions": shapley_report,
        "uniform_mixture_W_nats": mu_shapley,
    }
    text = json.dumps(report, indent=2, ensure_ascii=False)
    with open("abc_shapley_v1_results.json", "w", encoding="utf-8") as f:
        f.write(text)
    print(text)


if __name__ == "__main__":
    run_all()
