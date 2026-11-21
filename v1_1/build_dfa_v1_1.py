"""Generate the v1.1 DCA release from immutable v1.0 source.

The original is never overwritten; this script records transformations in text.
"""
from pathlib import Path
root=Path(__file__).resolve().parents[1]
s=(root/'legacy/dfa_to_1dca_v1.py').read_text()
s=s.replace('dfa_to_1dca_v1.py','dfa_to_1dca_v1_1.py').replace('dfa_to_1dca_v1_results.json','dfa_to_1dca_v1_1_results.json')
s=s.replace('Self-contained reproducible experiment (v1.0 release):','Self-contained reproducible experiment (v1.1; v1.0 preserved in legacy/):')
s=s.replace('import json\n', 'import json\nimport hashlib\nfrom itertools import combinations\n')
needle='''def run_dca(table: dict, w: str) -> bool:
    q, c = Q0, 0
'''
repl='''def framed(w: str) -> bool:
    """Accepted input protocol, shared by all candidate interpreters."""
    return isinstance(w, str) and w.endswith("$") and w.count("$") == 1 and all(ch in "01" for ch in w[:-1])


def run_dca(table: dict, w: str) -> bool:
    if not framed(w):
        return False
    q, c = Q0, 0
'''
assert needle in s;s=s.replace(needle,repl)
needle='''def eval_word_partial(pt: dict, w: str, lbl: bool):
    q, c = Q0, 0
'''
repl='''def eval_word_partial(pt: dict, w: str, lbl: bool):
    if not framed(w):
        return "ok" if not lbl else "mismatch"
    q, c = Q0, 0
'''
assert needle in s;s=s.replace(needle,repl)
start=s.index('def actions_with_law(')
end=s.index('\n\ndef eval_word_partial',start)
s=s[:start]+'''def actions_with_law(law, q: str, sym: str, z: int):
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
''' + s[end:]
start=s.index('def myhill_nerode_table(')
end=s.index('\n\ndef build_quotient_dfa',start)
s=s[:start]+'''def myhill_nerode_table(oracle, K: int):
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
''' + s[end:]
# New full finite-table consistency/closure obligations; if not met status unknown, not claim success.
start=s.index('def build_quotient_dfa(')
end=s.index('\n\ndef run_dfa',start)
s=s[:start]+'''def build_quotient_dfa(oracle, K: int):
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
''' + s[end:]
# Add non-guessable machine check of the inferred phase-template certificate.
needle='''def legal_actions(sym: str, z: int):'''
insert='''def certify_phase_linear_relation(table: dict, inferred: dict, contract: dict | None = None):
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
    if any(v[key]!=val for key,val in expected.items()) or not all(inferred.get("obligations_verified",{}).values()):
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


'''
assert needle in s;s=s.replace(needle,insert+needle)
start=s.index('def fixed_engine_F(')
end=s.index('\n\ndef main():', start)
s=s[:start]+'''def fixed_engine_F(task_name: str, oracle, S_max: int = 5, K_max: int = 5,
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
        if teacher_contract and teacher_contract.get("kind")=="regex_0plus1plus":
            proof=product_equivalence_certificate(dfa["_raw"],canonical_regex_reference())
        dfa.pop("_raw",None)
        return {"task":task_name,"S_max":S_max,"mn_trace":mn_trace,"escalated_to_1dca":False,
                "resolved_tier":"Tier-0 (DFA)","dfa_solution":dfa,
                "formal_reference_equivalence":proof or {"status":"UNKNOWN"},
                "oracle_global_equivalence": "PROVED_RELATIVE_TO_PROMISED_REGEX" if proof and proof["equivalent"] else "UNKNOWN",
                "ood_check_up_to_500_incl_end_markers":ood}
    ds=make_dataset(oracle)
    attempts=[]
    for mode in (["soft_transfer","unrestricted_fallback"] if slope_law is not None else ["unrestricted"]):
        law=slope_law if mode=="soft_transfer" else None
        synth=synthesize_1dca_from_scratch(ds,law=law)
        raw=synth.pop("_raw_table",None)
        inferred=infer_and_verify_linear_invariant(raw) if raw else {"found":False,"reason":"synthesis failure"}
        cert=certify_phase_linear_relation(raw,inferred,teacher_contract) if raw else {"status":"NO_PROGRAM"}
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
            "oracle_global_equivalence":"PROVED_RELATIVE_TO_KNOWN_FAMILY" if teacher_contract else "UNKNOWN",
            "ood_check_up_to_500_incl_end_markers":ood}
''' + s[end:]
start=s.index('def main():')
s=s[:start]+'''def main():
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
'''
# A declared teacher family is recognized only for a built-in explicitly registered oracle.
s=s.replace('    return oracle\n\n\n# --- Tier 0', '    oracle._known_family_offset=offset\n    return oracle\n\n\n# --- Tier 0', 1)
s=s.replace('if teacher_contract and teacher_contract.get("kind")=="regex_0plus1plus":',
            'if teacher_contract and teacher_contract.get("kind")=="regex_0plus1plus" and oracle is oracle_0plus1plus:')
s=s.replace('    ds=make_dataset(oracle)\n    attempts=[]',
            '    ds=make_dataset(oracle)\n    verified_contract = teacher_contract if (teacher_contract and teacher_contract.get("kind")=="offset" and getattr(oracle,"_known_family_offset",None)==teacher_contract.get("offset")) else None\n    attempts=[]')
s=s.replace('certify_phase_linear_relation(raw,inferred,teacher_contract)',
            'certify_phase_linear_relation(raw,inferred,verified_contract)')
s=s.replace('"PROVED_RELATIVE_TO_KNOWN_FAMILY" if teacher_contract else "UNKNOWN"',
            '"PROVED_RELATIVE_TO_KNOWN_FAMILY" if verified_contract else "UNKNOWN"')
s=s.replace('"soft_transfer"','"guarded_transfer"')
s=s.replace('def run_dfa(dfa_raw, w: str) -> bool:\n    q, accept_states, transitions = dfa_raw',
            'def run_dfa(dfa_raw, w: str) -> bool:\n    if not framed(w):\n        return False\n    q, accept_states, transitions = dfa_raw')
# Validate every certificate field against the table; reject missing obligations or changed labels.
old='    if any(v[key]!=val for key,val in expected.items()) or not all(inferred.get("obligations_verified",{}).values()):\n        return {"status":"INVALID_CERTIFICATE","reason":"transition/formula/obligation mismatch"}'
new='    required={\n        "q0_s1_z0_rej":table[(Q0,S1,0)][0]==REJ,\n        "q0_end_z0_rej":table[(Q0,SEND,0)][0]==REJ,\n        "q0_end_z1_rej":table[(Q0,SEND,1)][0]==REJ,\n        "q1_s0_z0_rej":table[(Q1,S0,0)][0]==REJ,\n        "q1_s0_z1_rej":table[(Q1,S0,1)][0]==REJ,\n        "q1_s1_z0_rej":table[(Q1,S1,0)][0]==REJ,\n        "q1_end_z0_acc":table[(Q1,SEND,0)]==(ACC,0),\n        "q1_end_z1_rej":table[(Q1,SEND,1)][0]==REJ}\n    labels={"q0_phase":f"c = {a0}*m + 0",\n            "q1_phase":f"c = {a1}*m + ({b1})*k + ({d1})",\n            "inferred_acceptance_relation":f"{a1}*m + ({b1})*k + ({d1}) = 0"}\n    if (any(v[key]!=val for key,val in expected.items()) or v.get("d0")!=0 or v.get("b0")!=0 or\n            inferred.get("obligations_verified")!=required or not all(required.values()) or\n            any(v.get(k)!=s for k,s in labels.items())):\n        return {"status":"INVALID_CERTIFICATE","reason":"transition/formula/obligation mismatch"}'
assert old in s
s=s.replace(old,new)
(root/'v1_1/dfa_to_1dca_v1_1.py').write_text(s)
print('wrote',len(s),'characters')
