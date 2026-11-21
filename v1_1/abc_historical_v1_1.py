#!/usr/bin/env python3
"""Cost-accounted, replayed 3-event histories for bounded Boolean synthesis.

Every coalition starts from NAND-only K0 and a fresh search state; requested
acquisition events are executed in canonical order e1 -> e2 -> e3. Unlike v1.0,
this is not just static activation of resources computed once outside coalitions.

W remains conditional on the fixed task curriculum, language, budget, and
declared surrogate cost; no general historical-causal invariant is claimed.
"""
from __future__ import annotations

import hashlib
import json
import math
import platform
import sys
import time
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from legacy import abc_shapley_v1 as kernel  # immutable, hashed legacy source

B_MAX = 200_000
PLAYERS = ("e1_NAND_law", "e2_XOR_macro", "e3_XOR_laws")
TASKS = ("T2_parity3", "T3_parity4", "Tneg_AND3")


def sha(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, ensure_ascii=False,
                                     separators=(",", ":")).encode("utf-8")).hexdigest()


def all_coalitions():
    return [tuple(sorted(s)) for i in range(len(PLAYERS) + 1)
            for s in combinations(PLAYERS, i)]


def accounted_synthesize(target_tt, n_inputs, ops, laws, max_gates):
    """Instrument unchanged legacy enumeration; wrapper cannot modify NF result."""
    calls = 0
    original = kernel.normalize_nf

    def count_then_forward(op_name, nf_a, nf_b, law):
        nonlocal calls
        calls += 1
        return original(op_name, nf_a, nf_b, law)

    kernel.normalize_nf = count_then_forward
    try:
        result = kernel.synthesize(target_tt, n_inputs, ops, laws, max_gates, B_MAX)
    finally:
        kernel.normalize_nf = original
    # Re-execution in synthesize's verified field is not part of evals.
    proof_gate_evals = len(result["gates"]) if result["found"] else 0
    return {
        **result,
        "normalizer_calls": calls,
        "gate_replay_checks": proof_gate_evals,
        "target_table_check": bool(result["verified"]) if result["found"] else False,
    }


def law_signature(law):
    return {key: law[key] for key in ("op", "tt", "commutative", "associative",
                                      "idempotent", "self_const", "identity", "law_checks")}


def certified_law(op, tt):
    law = kernel.discover_laws(op, tt)
    # Use a second, direct total-table certificate, independent of early breaks.
    def f(a, b):
        return (tt >> (2*a+b)) & 1

    comm_probe=[f(a,b)==f(b,a) for a in (0,1) for b in (0,1)]
    assoc_probe=[f(f(a,b),c)==f(a,f(b,c))
                 for a in (0,1) for b in (0,1) for c in (0,1)]
    idemp_probe=[f(a,a)==a for a in (0,1)]
    equal_self_probe=[f(0,0)==f(1,1)]
    identity_probe={e:[f(a,e)==a and f(e,a)==a for a in (0,1)] for e in (0,1)}
    comm=all(comm_probe)
    assoc=all(assoc_probe)
    idemp=all(idemp_probe)
    self_const=f(0,0) if equal_self_probe[0] else None
    identity=next((e for e in (0,1) if all(identity_probe[e])),None)
    witness = {"commutative":comm,"associative":assoc,"idempotent":idemp,
               "self_const":self_const,"identity":identity}
    assert all(law[key]==value for key,value in witness.items())
    # The verification probes are additional to discovery's short-circuiting probes.
    proof_probes = sum(map(len, (comm_probe,assoc_probe,idemp_probe,equal_self_probe))) + sum(len(x) for x in identity_probe.values())
    return law, {"truth_table":tt,"claims":witness,"proof_comparisons":proof_probes}


def target_specs():
    vs3,_ = kernel.make_input_vecs(3)
    vs4,_ = kernel.make_input_vecs(4)
    return {
        "T2_parity3":{"target":vs3[0]^vs3[1]^vs3[2],"n_inputs":3,"max_gates":4},
        "T3_parity4":{"target":vs4[0]^vs4[1]^vs4[2]^vs4[3],"n_inputs":4,"max_gates":3},
        "Tneg_AND3":{"target":vs3[0]&vs3[1]&vs3[2],"n_inputs":3,"max_gates":4},
    }


def discover_history(coalition):
    """Fresh replay: no acquired resources are copied between coalitions."""
    allowed = set(coalition)
    library = {"NAND":{"truth_table":kernel.NAND_TT,"source":"axiom of environment"}}
    ops = [("NAND",kernel.NAND_TT)]
    laws = {}
    ledger={"candidate_evals":0,"law_probes":0,"law_verification_probes":0,
            "normalizer_calls":0,"gate_replay_checks":0}
    records=[]

    def log(event, status, witness=None):
        records.append({"event":event,"status":status,"witness":witness,
                        "library_sha256_after":sha(library)})

    if "e1_NAND_law" in allowed:
        law,proof=certified_law("NAND",kernel.NAND_TT)
        ledger["law_probes"] += law["law_checks"]
        ledger["law_verification_probes"] += proof["proof_comparisons"]
        laws["NAND"]=law
        library["NAND_law"]={"laws":law_signature(law),"proof":proof}
        log("e1_NAND_law","CERTIFIED",library["NAND_law"])
    else:
        log("e1_NAND_law","DISABLED")

    if "e2_XOR_macro" in allowed:
        inputs,_=kernel.make_input_vecs(2)
        target=inputs[0]^inputs[1]  # T1 is part of the declared task stream
        result=accounted_synthesize(target,2,ops,laws,4)
        ledger["candidate_evals"] += result["evals"]
        ledger["normalizer_calls"] += result["normalizer_calls"]
        ledger["gate_replay_checks"] += result["gate_replay_checks"]
        if not result["found"] or not result["target_table_check"]:
            log("e2_XOR_macro","FAILED_TO_ACQUIRE",{"result":result})
        else:
            tt=kernel.eval_dag(result["gates"],2,dict(ops))
            ledger["gate_replay_checks"] += len(result["gates"])
            assert tt==target
            ops.append(("XOR",tt))
            library["XOR_macro"]={"truth_table":tt,"dag":result["gates"],
                                  "origin": "T1 target table + NAND synthesis", "depends_on":["NAND"]}
            log("e2_XOR_macro","CERTIFIED",{"program":library["XOR_macro"],
                                             "candidate_evals":result["evals"]})
    else:
        log("e2_XOR_macro","DISABLED")

    if "e3_XOR_laws" in allowed:
        if "XOR_macro" not in library:
            log("e3_XOR_laws","BLOCKED_BY_MISSING_MACRO")
        else:
            law,proof=certified_law("XOR",library["XOR_macro"]["truth_table"])
            ledger["law_probes"] += law["law_checks"]
            ledger["law_verification_probes"] += proof["proof_comparisons"]
            laws["XOR"]=law
            library["XOR_laws"]={"laws":law_signature(law),"proof":proof,
                                 "depends_on":["XOR_macro"]}
            log("e3_XOR_laws","CERTIFIED",library["XOR_laws"])
    else:
        log("e3_XOR_laws","DISABLED")

    return {"library":library,"ops":ops,"laws":laws,"acquisition":ledger,"history":records,
            "history_sha256":sha(records)}


def coalition_replay(coalition):
    replay=discover_history(coalition)
    tasks={}
    for name,spec in target_specs().items():
        outcome=accounted_synthesize(spec["target"],spec["n_inputs"],replay["ops"],
                                     replay["laws"],spec["max_gates"])
        assert (not outcome["found"]) or outcome["verified"]
        tasks[name]={"found":outcome["found"],"evals":outcome["evals"],
                     "normalizer_calls":outcome["normalizer_calls"],
                     "gate_replay_checks":outcome["gate_replay_checks"],
                     "max_gates":spec["max_gates"], "gates":outcome["gates"],
                     "bounded_grammar":True}
    return {"coalition":list(coalition),"history":replay["history"],
            "history_sha256":replay["history_sha256"],
            "acquisition":replay["acquisition"],"tasks":tasks,
            "acquired_library_sha256":sha(replay["library"])}


def metered_cost(replay, selected_tasks, lambda_nf=0):
    """Explicit surrogate: assessed candidate circuits + law probes + recert.

    Acquisition charged once for the selected task bundle. Normalization
    is reported in the ledger, with sensitivity weight lambda_nf. Failure to
    find a solution within the declared grammar gets cost B_MAX per task.
    """
    a=replay["acquisition"]
    acquire=a["candidate_evals"]+a["law_probes"]+a["law_verification_probes"]+a["gate_replay_checks"]
    nf=a["normalizer_calls"]
    for name in selected_tasks:
        r=replay["tasks"][name]
        acquire += r["evals"]+r["gate_replay_checks"] if r["found"] else B_MAX
        nf += r["normalizer_calls"]
    return acquire+lambda_nf*nf


def exact_shapley(replays, selected_tasks, lambda_nf=0):
    players=PLAYERS
    v={}
    costs={}
    for c,r in replays.items():
        costs[c]=metered_cost(r,selected_tasks,lambda_nf)
    base=costs[()]
    assert base>0
    # finite ceiling prevents undefined effect of noncompletion
    ceiling=len(selected_tasks)*B_MAX+1_000_000
    for c,cost in costs.items():
        v[c]=math.log(min(base,ceiling))-math.log(min(cost,ceiling))
    factor=math.factorial
    w={}
    for player in players:
        others=[p for p in players if p!=player]
        contrib=0.
        for k in range(len(others)+1):
            weight=factor(k)*factor(len(players)-k-1)/factor(len(players))
            for subset in combinations(others,k):
                before=tuple(sorted(subset)); after=tuple(sorted(subset+(player,)))
                contrib += weight*(v[after]-v[before])
        w[player]=contrib
    assert abs(math.fsum(w.values())-v[tuple(sorted(players))]) < 1e-10
    return {"coalition_values":{"EMPTY" if not c else ",".join(c):{
                 "work_units": costs[c],"v_nats":v[c]} for c in replays},
            "shapley":w,"sum_W":math.fsum(w.values()),
            "v_full":v[tuple(sorted(players))], "unit":"surrogate units, not time",
            "normalization_weight":lambda_nf,
            "acquisition_paid_once":True,
            "failure_censored_at":"B_MAX per task if no solution under gate bound"}


def run_all():
    start=time.perf_counter()
    replays={c:coalition_replay(c) for c in all_coalitions()}
    # Cross-check that the macro and law libraries were actually acquired in each history.
    for c,replay in replays.items():
        states={r["event"]:r["status"] for r in replay["history"]}
        assert states["e1_NAND_law"]==("CERTIFIED" if "e1_NAND_law" in c else "DISABLED")
        assert states["e2_XOR_macro"]==("CERTIFIED" if "e2_XOR_macro" in c else "DISABLED")
        assert states["e3_XOR_laws"]==("CERTIFIED" if "e3_XOR_laws" in c and "e2_XOR_macro" in c else
                                       "BLOCKED_BY_MISSING_MACRO" if "e3_XOR_laws" in c else "DISABLED")
    scopes={name:exact_shapley(replays,[name],lambda_nf=1) for name in TASKS}
    scopes["SUITE_ACQUISITION_ONCE"]=exact_shapley(replays,list(TASKS),lambda_nf=1)
    weights={str(x):exact_shapley(replays,list(TASKS),lambda_nf=x) for x in (0, 0.05, 0.2, 1, 5)}
    result={"release":"1.1.1","engine":"legacy frozen BFS + instrumentation",
            "cost_contract":{"default":"candidate evaluations + discovered-law property probes + independent total law certificate comparisons + successful gate replay checks + normalizer calls; acquisition once per coalition history",
                             "not_in_default":"physical time, garbage collection, state allocation overhead and library/curriculum encoding excluded; normalizer calls included as one proxy unit and sensitivity varied",
                             "B_MAX":B_MAX,"ceiling_is_right_censoring_not_observed_solution_time":True},
            "players":list(PLAYERS),"tasks":target_specs(),"replays":{
                "EMPTY" if not c else ",".join(c):r for c,r in replays.items()},
            "shapley_replayed_histories":scopes,"sensitivity_suite":weights,
            "wall_seconds":time.perf_counter()-start}
    return result


if __name__=="__main__":
    print(json.dumps(run_all(),ensure_ascii=False,indent=2))
