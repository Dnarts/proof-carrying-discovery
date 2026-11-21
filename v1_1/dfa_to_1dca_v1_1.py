#!/usr/bin/env python3
"""
dfa_to_1dca_v1_1.py
Self-contained reproducible experiment (v1.1; v1.0 preserved in legacy/):
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
import hashlib
from itertools import combinations
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
    oracle._known_family_offset=offset
    return oracle


# --- Tier 0: Exact Myhill-Nerode Lower Bound & Quotient DFA ---
def myhill_nerode_table(oracle, K: int):
    """Finite pairwise distinguishing witnesses, not global identification."""
    prefixes = list(dict.fromkeys([""] + ["0" * i for i in range(1, K + 1)] + ["01", "01$", "1"]))
    suffixes = list(dict.fromkeys(["", "$"] + ["1" * j + "$" for j in range(1, K + 1)] + ["01$"]))
    rows = {}
    for p in prefixes:
        sig = tuple(oracle(p + s) for s in suffixes)
        if sig not in rows:
            rows[sig] = p
    reps = list(rows.values())
    witnesses = []
    for p, q in combinations(reps, 2):
        witness = next((suffix for suffix in suffixes if oracle(p + suffix) != oracle(q + suffix)), None)
        assert witness is not None
        witnesses.append({"p": p, "q": q, "suffix": witness, "p_answer": oracle(p + witness), "q_answer": oracle(q + witness)})
    return {"K": K, "distinct_classes": len(rows), "representatives": reps,
            "prefixes": prefixes, "suffixes": suffixes,
            "signatures": {rep: list(sig) for sig, rep in rows.items()},
            "pair_witnesses": witnesses,
            "scope": "finite trusted membership responses; lower bound on DFA states only"}


def build_quotient_dfa(oracle, K: int):
    tbl = myhill_nerode_table(oracle, K)
    reps, suffixes = tbl["representatives"], tbl["suffixes"]
    signature = lambda p: tuple(oracle(p + s) for s in suffixes)
    sig_to_id = {signature(rep): idx for idx, rep in enumerate(reps)}
    transitions = {}
    for p in tbl["prefixes"]:
        src = sig_to_id[signature(p)]
        for ch in ("0", "1", "$"):
            target = sig_to_id.get(signature(p + ch))
            if target is None or ((src, ch) in transitions and transitions[(src,ch)] != target):
                return None
            transitions[(src, ch)] = target
    for rep in reps:
        for ch in ("0", "1", "$"):
            if (sig_to_id[signature(rep)], ch) not in transitions:
                return None
    start_state = sig_to_id[signature("")]
    accept_states = {sig_to_id[signature(rep)] for rep in reps if oracle(rep)}
    return {"num_states": len(reps), "start": start_state,
            "accept": sorted(accept_states),
            "transitions": {f"{k[0]},{k[1]}": v for k,v in sorted(transitions.items())},
            "finite_observation_closed_and_consistent": True,
            "teacher_global_equivalence": "UNKNOWN unless verified against a known formal reference",
            "_raw": (start_state, accept_states, transitions)}


def canonical_regex_reference():
    """Five-state DFA for 0+1+$; reference correctness follows by phase induction."""
    t = {}
    rows = {
        0: (1, 4, 4),  # start
        1: (1, 2, 4),  # zeros
        2: (4, 2, 3),  # ones
        3: (4, 4, 4),  # accepted after one end marker
        4: (4, 4, 4),  # dead
    }
    for st, targets in rows.items():
        for ch, dest in zip(("0","1","$"),targets):
            t[(st,ch)] = dest
    return (0, {3}, t)


def product_equivalence_certificate(a, b):
    """Exact product DFA emptiness: full language equality for TWO specified DFAs."""
    qa, aa, ta = a; qb, ab, tb = b
    frontier=[(qa,qb)]; visited={(qa,qb)}
    for pair in frontier:
        x,y=pair
        if (x in aa) != (y in ab):
            return {"equivalent": False, "counterexample_state_pair":list(pair)}
        for ch in ("0","1","$"):
            nxt=(ta[(x,ch)],tb[(y,ch)])
            if nxt not in visited:
                visited.add(nxt);frontier.append(nxt)
    return {"equivalent": True, "checked_product_pairs":len(visited),
            "scope":"finite reference DFA for the declared 0+1+$ regex; not an arbitrary oracle"}


def run_dfa(dfa_raw, w: str) -> bool:
    if not framed(w):
        return False
    q, accept_states, transitions = dfa_raw
    for ch in w:
        q = transitions[(q, ch)]
    return q in accept_states


# --- Tier 1: 1-DCA with strict full-word end-marker semantics ---
Q0, Q1, ACC, REJ = "q0", "q1", "acc", "rej"
S0, S1, SEND = "0", "1", "$"


def apply_delta(c: int, d: int):
    return None if c + d < 0 else c + d


def framed(w: str) -> bool:
    """Accepted input protocol, shared by all candidate interpreters."""
    return isinstance(w, str) and w.endswith("$") and w.count("$") == 1 and all(ch in "01" for ch in w[:-1])


def run_dca(table: dict, w: str) -> bool:
    if not framed(w):
        return False
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


def certify_phase_linear_relation(table: dict, inferred: dict, contract: dict | None = None):
    """Recompute the template's inductive obligations from the exported table.

    The known-language contract is separate from inference: nothing is passed
    to infer_and_verify_linear_invariant beyond the candidate table.
    """
    if not inferred.get("found"):
        return {"status":"UNPROVED_TEMPLATE", "reason":inferred.get("reason")}
    v=inferred["inv"]
    a0,a1,b1,d1=(v[x] for x in ("a0","a1","b1","d1"))
    # Recheck the phase structure from the exported table. A valid invariant
    # from an earlier table must not certify changed transition destinations
    # or unequal zero increments in the two counter guards.
    phase_structure=(
        table[(Q0,S0,0)] == (Q0,a0)
        and table[(Q0,S0,1)] == (Q0,a0)
        and table[(Q0,S1,1)][0] == Q1
        and table[(Q1,S1,1)] == (Q1,b1)
    )
    if not phase_structure:
        return {"status":"INVALID_CERTIFICATE","reason":"phase transition structure mismatch"}
    expected={"a0": table[(Q0,S0,0)][1], "a1":table[(Q0,S0,0)][1],
              "b1":table[(Q1,S1,1)][1],
              "d1":table[(Q0,S1,1)][1]-table[(Q1,S1,1)][1]}
    required={
        "q0_s1_z0_rej":table[(Q0,S1,0)][0]==REJ,
        "q0_end_z0_rej":table[(Q0,SEND,0)][0]==REJ,
        "q0_end_z1_rej":table[(Q0,SEND,1)][0]==REJ,
        "q1_s0_z0_rej":table[(Q1,S0,0)][0]==REJ,
        "q1_s0_z1_rej":table[(Q1,S0,1)][0]==REJ,
        "q1_s1_z0_rej":table[(Q1,S1,0)][0]==REJ,
        "q1_end_z0_acc":table[(Q1,SEND,0)]==(ACC,0),
        "q1_end_z1_rej":table[(Q1,SEND,1)][0]==REJ}
    labels={"q0_phase":f"c = {a0}*m + 0",
            "q1_phase":f"c = {a1}*m + ({b1})*k + ({d1})",
            "inferred_acceptance_relation":f"{a1}*m + ({b1})*k + ({d1}) = 0"}
    if (any(v[key]!=val for key,val in expected.items()) or v.get("d0")!=0 or v.get("b0")!=0 or
            inferred.get("obligations_verified")!=required or not all(required.values()) or
            any(v.get(k)!=s for k,s in labels.items())):
        return {"status":"INVALID_CERTIFICATE","reason":"transition/formula/obligation mismatch"}
    if not (a0>0 and b1<0 and a0==a1 and a0 + table[(Q0,S1,1)][1]>=0):
        return {"status":"INVALID_CERTIFICATE","reason":"phase and bridge preconditions"}
    semantic={"coefficients":[a1,b1,d1],"variables":["m","k","one"],
              "relation":f"{a1}*m + ({b1})*k + ({d1}) = 0",
              "domain":"0^m1^k$ with m>=1,k>=1; strict complete-input framing",
              "phases":{"q0":f"c={a0}*m", "q1":f"c={a1}*m+({b1})*k+({d1})"}}
    proof={"init": "q0 begins c=m=0", "q0_step": "reading a zero increases c and m by a0 and 1 respectively",
           "bridge": "the first one sends q0 to q1, preserving the computed affine equality",
           "q1_step": "each further one with c>0 adds b1 to c and 1 to k; c=0 rejects further ones",
           "order_rejection": "q1 rejects any zero; q0 rejects early end and missing zeros",
           "accept": "at terminal $ exactly q1,c=0 accepts; negative counter transitions reject"}
    status="PROVED_PROGRAM_LANGUAGE_ONLY"
    if contract is not None and contract.get("kind")=="offset":
        off=contract["offset"]
        if (a1,b1,d1)!=(1,-1,off):
            return {"status":"CONTRACT_MISMATCH","program_semantics":semantic,
                    "expected_relation":[1,-1,off]}
        status="PROVED_RELATIVE_TO_KNOWN_OFFSET_FAMILY"
    return {"status":status,"semantic":semantic,"proof":proof,
            "semantic_sha256":hashlib.sha256(json.dumps(semantic,sort_keys=True).encode()).hexdigest()}


def legal_actions(sym: str, z: int):
    if sym == SEND:
        return [(REJ, 0), (ACC, 0)]
    dcs = (-1, 0, 1) if z == 1 else (0, 1)
    return [(REJ, 0)] + [(nq, dc) for nq in (Q0, Q1) for dc in dcs]


def actions_with_law(law, q: str, sym: str, z: int):
    """Provisional hard pruning, guarded by explicit certificate + fallback.

    A failed or invalid transfer triggers an unrestricted re-search in F.
    """
    base = legal_actions(sym, z)
    if law is None:
        return base
    a0, b1 = law
    preferred = None
    if q == Q0 and sym == S0:
        preferred = (Q0, a0)
    elif q == Q1 and sym == S1 and z == 1:
        preferred = (Q1, b1)
    if preferred is not None:
        return [preferred] if preferred in base else []
    return base


def eval_word_partial(pt: dict, w: str, lbl: bool):
    if not framed(w):
        return "ok" if not lbl else "mismatch"
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


def fixed_engine_F(task_name: str, oracle, S_max: int = 5, K_max: int = 5,
                   slope_law=None, ood_offset_hint: int = 0, teacher_contract=None):
    mn_trace=[]; trigger=None; trigger_witnesses=[]
    for K in range(1,K_max+1):
        tbl=myhill_nerode_table(oracle,K)
        mn_trace.append({"K":K,"N_K":tbl["distinct_classes"],"representatives":tbl["representatives"]})
        if tbl["distinct_classes"]>S_max:
            trigger={"K":K,"N_K":tbl["distinct_classes"],"max_dfa_states":S_max,
                     "scope":"DFA with <= S_max states; NOT all DFAs"}
            trigger_witnesses=tbl["pair_witnesses"]
            break
    if trigger is None:
        dfa=build_quotient_dfa(oracle,K_max)
        if dfa is None:
            return {"task":task_name,"status":"UNKNOWN_UNCLOSED_TABLE","mn_trace":mn_trace,
                    "oracle_global_equivalence":"UNKNOWN"}
        ood=check_ood(lambda w:run_dfa(dfa["_raw"],w),oracle,0)
        proof=None
        if teacher_contract and teacher_contract.get("kind")=="regex_0plus1plus" and oracle is oracle_0plus1plus:
            proof=product_equivalence_certificate(dfa["_raw"],canonical_regex_reference())
        dfa.pop("_raw",None)
        return {"task":task_name,"S_max":S_max,"mn_trace":mn_trace,"escalated_to_1dca":False,
                "resolved_tier":"Tier-0 (DFA)","dfa_solution":dfa,
                "formal_reference_equivalence":proof or {"status":"UNKNOWN"},
                "oracle_global_equivalence": "PROVED_RELATIVE_TO_PROMISED_REGEX" if proof and proof["equivalent"] else "UNKNOWN",
                "ood_check_up_to_500_incl_end_markers":ood}
    ds=make_dataset(oracle)
    verified_contract = teacher_contract if (teacher_contract and teacher_contract.get("kind")=="offset" and getattr(oracle,"_known_family_offset",None)==teacher_contract.get("offset")) else None
    attempts=[]
    for mode in (["guarded_transfer","unrestricted_fallback"] if slope_law is not None else ["unrestricted"]):
        law=slope_law if mode=="guarded_transfer" else None
        synth=synthesize_1dca_from_scratch(ds,law=law)
        raw=synth.pop("_raw_table",None)
        inferred=infer_and_verify_linear_invariant(raw) if raw else {"found":False,"reason":"synthesis failure"}
        cert=certify_phase_linear_relation(raw,inferred,verified_contract) if raw else {"status":"NO_PROGRAM"}
        attempts.append({"mode":mode,"nodes":synth["nodes"],"found":synth["found"],
                         "certificate_status":cert["status"]})
        if cert["status"] in ("PROVED_PROGRAM_LANGUAGE_ONLY","PROVED_RELATIVE_TO_KNOWN_OFFSET_FAMILY"):
            break
    else:
        return {"task":task_name,"status":"UNKNOWN_NO_CERTIFIED_PROGRAM","mn_trace":mn_trace,
                "escalation_certificate":trigger,"pair_witnesses":trigger_witnesses,
                "attempts":attempts,"oracle_global_equivalence":"UNKNOWN"}
    ood=check_ood(lambda w:run_dca(raw,w),oracle,ood_offset_hint)
    return {"task":task_name,"S_max":S_max,"mn_trace":mn_trace,
            "escalated_to_1dca":True,"escalation_certificate":trigger,
            "pair_witnesses":trigger_witnesses,"resolved_tier":"Tier-1 (1-DCA)",
            "used_slope_law":list(slope_law) if slope_law else None,
            "transfer_policy":"provisional hard pruning; on no certified result rerun unrestricted",
            "fallback_used":len(attempts)>1,
            "attempts":attempts,"dca_synthesis":synth,"inferred_invariant":inferred,
            "phase_certificate":cert,
            "oracle_global_equivalence":"PROVED_RELATIVE_TO_KNOWN_FAMILY" if verified_contract else "UNKNOWN",
            "ood_check_up_to_500_incl_end_markers":ood}


def main():
    S_max,K_max=5,5
    res_neg=fixed_engine_F("T_neg_0plus1plus",oracle_0plus1plus,S_max,K_max,
                           ood_offset_hint=0,teacher_contract={"kind":"regex_0plus1plus"})
    res_t1=fixed_engine_F("T1_0n1n",oracle_0n1n_offset(0),S_max,K_max,
                          ood_offset_hint=0,teacher_contract={"kind":"offset","offset":0})
    assert res_t1["phase_certificate"]["status"]=="PROVED_RELATIVE_TO_KNOWN_OFFSET_FAMILY"
    inv1=res_t1["inferred_invariant"]["inv"]
    law=(inv1["a0"],inv1["b1"])
    no_law=fixed_engine_F("T2_0n1n_plus_1_no_I1",oracle_0n1n_offset(1),S_max,K_max,
                          ood_offset_hint=1,teacher_contract={"kind":"offset","offset":1})
    with_law=fixed_engine_F("T2_0n1n_plus_1_with_I1",oracle_0n1n_offset(1),S_max,K_max,
                            slope_law=law,ood_offset_hint=1,teacher_contract={"kind":"offset","offset":1})
    bad_law=fixed_engine_F("T2_wrong_law_control",oracle_0n1n_offset(1),S_max,K_max,
                          slope_law=(1,1),ood_offset_hint=1,teacher_contract={"kind":"offset","offset":1})
    report={"meta":{"python_version":sys.version.split()[0],"platform":platform.platform(),
                    "S_max":S_max,"K_max":K_max,"release":"1.1.1",
                    "scope":"bounded DFA lower bound; known formal teacher families; phase-linear invariant template"},
            "T_neg_0plus1plus":res_neg,"T1_0n1n":res_t1,
            "T2_0n1n_plus_1":{"without_I1":no_law,"with_I1":with_law,
                               "transfer_node_speedup":round(no_law["dca_synthesis"]["nodes"] / with_law["dca_synthesis"]["nodes"],6)},
            "wrong_transfer_control":bad_law}
    print(json.dumps(report,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
