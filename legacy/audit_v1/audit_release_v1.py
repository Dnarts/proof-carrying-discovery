#!/usr/bin/env python3
"""Independent checks and deliberately scoped counterexamples for InvariantNet v1.0.

Does not modify the four uploaded release files. Standard-library only.
"""
import hashlib
import importlib.util
import itertools
import json
import math
import re
import subprocess
import sys
import tempfile
from pathlib import Path

DEST = Path(__file__).resolve().parent
INPUT = DEST / 'original' if (DEST / 'original').is_dir() else Path('/mnt/data')
HASHES = {
 'abc_shapley_v1.py': '90edaa1d3e9b9ddbccee07bd3893562054aabf5ae899013388a5419c6bf828fc',
 'abc_shapley_v1_results.json': '13d3eedccdfe6df9ec8ec4a0e0eb1734a0a8559627d10b69ee7d6475025c4958',
 'dfa_to_1dca_v1.py': '4975381c4ed98e8db13be24029fb6c6d21a49dffea1851b258a00d9066b8d9ba',
 'dfa_to_1dca_v1_results.json': '6b4bac1a9937cae3e0e5f1d8791f0af07cac5346e2712618099f86976ccae459',
}

def sha(b): return hashlib.sha256(b).hexdigest()
def loadmod(name, path):
    s = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(s)
    s.loader.exec_module(mod)
    return mod

def cleaned(x):
    if isinstance(x,dict): return {k:cleaned(v) for k,v in x.items() if k not in ('python_version','platform','time_s')}
    if isinstance(x,list): return [cleaned(v) for v in x]
    return x

def independent_boolean_eval(gates, xs):
    wires=list(xs)
    for g in gates:
        op,i,j=g
        a,b=wires[i],wires[j]
        if op=='NAND': wires.append(1-(a&b))
        elif op=='XOR': wires.append(a ^ b)
        else: raise AssertionError('unknown primitive')
    return wires[-1]

def independent_dca(table, w):
    state='q0'; count=0
    for ch in w:
        if state in ('acc','rej'): return False
        sgn=int(count>0)
        nxt,delta=table[(state,ch,sgn)]
        count+=delta
        if count<0: return False
        state=nxt
    return state=='acc'

def independent_dfa(result, w):
    q=result['start'];f=set(result['accept'])
    for ch in w: q=result['transitions'][f'{q},{ch}']
    return q in f

def source_table_to_tuples(r):
    return {tuple([parts[0],parts[1],int(parts[2])]):tuple(v) for k,v in r.items() for parts in [k.split(',')]}

def true_language(name, w):
    match=re.fullmatch(r'(0+)(1+)\$',w)
    if not match:return False
    n0,n1=map(len,match.groups())
    return (name=='regular' or (name=='balance' and n0==n1) or (name=='offset' and n1==n0+1))


def independent_phase_certificate(t):
    """Checks sufficient structural obligations without calling the supplied invariant detector.

    A mathematical induction is still needed to obtain an all-length theorem from
    these checked local identities; this function is not a proof assistant.
    """
    q0,q1,acc,rej='q0','q1','acc','rej'
    a=t[(q0,'0',0)][1]
    assert a>0 and t[(q0,'0',0)]==(q0,a) and t[(q0,'0',1)]==(q0,a)
    b=-t[(q1,'1',1)][1]
    assert b>0 and t[(q1,'1',1)]==(q1,-b)
    nxt,bridge=t[(q0,'1',1)]
    assert nxt==q1 and a+bridge>=0
    for (q,ch,z) in ((q0,'1',0),(q0,'$',0),(q0,'$',1),(q1,'0',0),(q1,'0',1),(q1,'1',0),(q1,'$',1)):
        assert t[(q,ch,z)][0]==rej
    assert t[(q1,'$',0)]==(acc,0)
    phase_offset=bridge+b
    return {'initial_phase':'q0: c=a*m','second_phase':'q1: c=a*m-b*k+offset',
            'a':a,'b':b,'bridge_delta':bridge,'offset':phase_offset,
            'phase_transition_valid_at_m_1':True,
            'acceptance_formula':'a*m-b*k+offset=0 under domain 0+1+$',
            'proof_status':'all local checks pass; soundness/completeness by ordinary induction, not kernel checked'}

def independent_shapley(coalitions,players):
    def cost(s):return coalitions[','.join(sorted(s)) if s else 'EMPTY']['capped_cost']
    c0=cost(())
    n=len(players)
    v=lambda s:math.log(c0/cost(s))
    result={}
    for p in players:
        rest=[q for q in players if q!=p]
        result[p]=sum((math.factorial(k)*math.factorial(n-k-1)/math.factorial(n))*(v(S+(p,))-v(S))
         for k in range(len(rest)+1) for S in itertools.combinations(rest,k))
    return result, v(tuple(players))

def main():
    report={'hashes':{},'rerun':{},'abc':{},'dfa':{},'bounds':{},'issues':[]}
    for name,expected in HASHES.items():
        p=INPUT/name
        actual=sha(p.read_bytes())
        assert actual==expected,(name,actual,expected)
        report['hashes'][name]={'sha256':actual,'matches_user_claim':True}

    with tempfile.TemporaryDirectory() as tmp:
        for stem in ['abc_shapley_v1','dfa_to_1dca_v1']:
            p=INPUT/(stem+'.py')
            run=subprocess.run([sys.executable,str(p)],cwd=tmp,capture_output=True,text=True,check=True)
            data=json.loads(run.stdout)
            baseline=json.loads((INPUT/(stem+'_results.json')).read_text())
            assert cleaned(data)==cleaned(baseline),stem
            report['rerun'][stem]={'deterministic_readback':True,'runtime_fields_differ':data!=baseline}

    a=loadmod('uploaded_abc_shapley_v1',INPUT/'abc_shapley_v1.py')
    d=loadmod('uploaded_dfa_to_1dca_v1',INPUT/'dfa_to_1dca_v1.py')
    abc=json.loads((INPUT/'abc_shapley_v1_results.json').read_text())
    dfa=json.loads((INPUT/'dfa_to_1dca_v1_results.json').read_text())

    players=['e1_NAND_law','e2_XOR_macro','e3_XOR_laws']
    macro=a.synthesize(0b0110,2,[('NAND',a.NAND_TT)],{},4,a.B_MAX)
    macro_with_nand=a.synthesize(0b0110,2,[('NAND',a.NAND_TT)],{'NAND':a.discover_laws('NAND',a.NAND_TT)},4,a.B_MAX)
    assert macro['found'] and macro['evals']==1535
    assert macro_with_nand['found'] and macro_with_nand['evals']==341
    for xs in itertools.product((0,1),repeat=2): assert independent_boolean_eval(macro['gates'],xs)==xs[0]^xs[1]
    report['abc']['xor_acquisition_nodes_without_nand_law']=1535
    report['abc']['xor_acquisition_nodes_with_nand_law']=341
    report['abc']['law_checks']={'NAND':13,'XOR':20}

    gate_log={}; comparisons={}; budget=a.B_MAX
    for task,source in abc['shapley_8_coalitions'].items():
        n=4 if task=='T3_parity4' else 3
        xs=a.make_input_vecs(n)[0]
        target=(xs[0]^xs[1]^xs[2]^xs[3] if n==4 else (xs[0]&xs[1]&xs[2] if task=='T_neg_and3' else xs[0]^xs[1]^xs[2]))
        source_coals=source['coalitions']
        exactW,total=independent_shapley(source_coals,players)
        report['abc'].setdefault('unrounded_shapley',{})[task]={**exactW,'total_full':total,'sum_minus_total':sum(exactW.values())-total}
        for p in players:
            assert abs(exactW[p]-source['shapley_W_nats'][p]) < 5.1e-7
        assert abs(total-source['v_full_nats'])<5.1e-7
        gate_log[task]={}
        for mask in range(8):
            coalition=tuple(sorted(players[i] for i in range(3) if mask>>i&1))
            key=','.join(coalition) if coalition else 'EMPTY'
            laws={}
            ops=[('NAND',a.NAND_TT)]
            if players[0] in coalition:laws['NAND']=a.discover_laws('NAND',a.NAND_TT)
            if players[1] in coalition: ops.append(('XOR',0b0110))
            if players[1] in coalition and players[2] in coalition:laws['XOR']=a.discover_laws('XOR',0b0110)
            res=a.synthesize(target,n,ops,laws,3 if n==4 else 4,budget)
            archived=source_coals[key]
            assert res['found']==archived['found']
            assert (res['evals'] if res['found'] else budget)==archived['capped_cost']
            g=res['gates']
            if g is not None:
                for row in itertools.product((0,1),repeat=n):
                    should=all(row) if task=='T_neg_and3' else sum(row)%2
                    assert independent_boolean_eval(g,row)==should,(task,key,row,g)
            gate_log[task][key]={'found':res['found'],'evaluated_nodes':res['evals'], 'output_gates':g,'independent_truth_table':'PASS' if g is not None else 'not_applicable'}
        # Demonstrate a more complete but *different* cost convention.
        alt={}
        for coalition_str, entry in source_coals.items():
            cs=set(coalition_str.split(',')) if coalition_str!='EMPTY' else set()
            acq=13*(players[0] in cs)
            if players[1] in cs:
                acq+=341 if players[0] in cs else 1535
                acq+=20*(players[2] in cs)
            alt[coalition_str]={'capped_cost': min(budget,entry['capped_cost']+acq) if entry['found'] else budget}
        w_alt, full_alt=independent_shapley(alt,players)
        comparisons[task]={'published_search_only_shapley_nats':source['shapley_W_nats'], 'alternative_acquisition_plus_search_shapley_nats':w_alt,'alternative_total_nats':full_alt,'cost_policy_note':'alternative counts 13/20 law checks and 1535/341 XOR acquisition nodes; still excludes normalization and wall-clock cost'}
    report['abc']['coalition_gate_witnesses_independently_checked']=sum(v['found'] for t in gate_log.values() for v in t.values())
    report['abc']['coalition_count']=sum(len(t) for t in gate_log.values())
    report['abc']['reported_W_is_rounded']=True
    report['abc']['acquisition_sensitivity']=comparisons
    (DEST/'gate_witnesses.json').write_text(json.dumps(gate_log,ensure_ascii=False,indent=2)+'\n')

    data_to_tables={
       'regular': dfa['T_neg_0plus1plus']['dfa_solution'],
       'balance': dfa['T1_0n1n']['dca_synthesis']['table'],
       'offset_without': dfa['T2_0n1n_plus_1']['without_I1']['dca_synthesis']['table'],
       'offset_with': dfa['T2_0n1n_plus_1']['with_I1']['dca_synthesis']['table']}
    exhaustive={}
    for label,raw in data_to_tables.items():
        table = source_table_to_tuples(raw) if label != 'regular' else None
        count=0
        for length in range(9):
            for s in itertools.product('01$',repeat=length):
                w=''.join(s)
                expected=true_language('offset' if label.startswith('offset') else label,w)
                actual=independent_dca(table,w) if table is not None else independent_dfa(raw,w)
                assert actual==expected,(label,w,actual,expected)
                count+=1
        exhaustive[label]=count
    report['dfa']['independent_ternary_strings_checked']=exhaustive
    report['dfa']['independent_phase_certificates']={label:independent_phase_certificate(source_table_to_tuples(raw)) for label,raw in data_to_tables.items() if label!='regular'}
    assert report['dfa']['independent_phase_certificates']['balance']['offset']==0
    assert report['dfa']['independent_phase_certificates']['offset_without']['offset']==1
    assert report['dfa']['independent_phase_certificates']['offset_with']['offset']==1
    assert dfa['T1_0n1n']['dca_synthesis']['nodes']==26
    assert dfa['T2_0n1n_plus_1']['without_I1']['dca_synthesis']['nodes']==57
    assert dfa['T2_0n1n_plus_1']['with_I1']['dca_synthesis']['nodes']==28
    report['dfa']['published_node_counts_confirmed']=True
    wrong=d.synthesize_1dca_from_scratch(d.make_dataset(d.oracle_0n1n_offset(1)),law=(1,1))
    assert not wrong['found']
    report['dfa']['wrong_transferred_slope']={'slope':[1,1],'found_solution':wrong['found'],'nodes':wrong['nodes'],'fallback_to_unconstrained_search':False}

    # Reconstruct a concrete distinguishing-suffix witness for every pair of MN classes.
    mn_certificates={}
    for name, oracle, K in [('regular',d.oracle_0plus1plus,5),('balance',d.oracle_0n1n_offset(0),2),('offset',d.oracle_0n1n_offset(1),5)]:
        obs=d.myhill_nerode_table(oracle,K)
        cert=[]
        for p,q in itertools.combinations(obs['representatives'],2):
            witness=next((s for s in obs['suffixes'] if oracle(p+s)!=oracle(q+s)),None)
            assert witness is not None
            cert.append({'prefix_a':p,'prefix_b':q,'separating_suffix':witness,'answer_a':oracle(p+witness),'answer_b':oracle(q+witness)})
        assert len(cert)==math.comb(obs['distinct_classes'],2)
        mn_certificates[name]={'K':K,'lower_bound_states':obs['distinct_classes'],'distinguished_pairs':cert}
    (DEST/'mn_pair_witnesses.json').write_text(json.dumps(mn_certificates,ensure_ascii=False,indent=2)+'\n')
    report['dfa']['mn_distinguishers_by_language']={k:len(v['distinguished_pairs']) for k,v in mn_certificates.items()}

    # A finite teacher matching every question asked in the whole full run but not the inferred infinite target.
    fin_oracles={}
    for name,known in [('regular',d.oracle_0plus1plus),('balance',d.oracle_0n1n_offset(0))]:
        asked=set()
        def queried(word):
            asked.add(word)
            return known(word)
        first=d.fixed_engine_F(name,queried,5,5,None,0)
        answers={x:known(x) for x in asked}
        def finite_teacher(word):return answers.get(word,False)
        second=d.fixed_engine_F(name,finite_teacher,5,5,None,0)
        assert cleaned(first)==cleaned(second)
        counterword='0'*6+'1'*6+'$'
        assert counterword not in asked
        if name=='regular': hypothesis=independent_dfa(first['dfa_solution'],counterword)
        else: hypothesis=independent_dca(source_table_to_tuples(first['dca_synthesis']['table']),counterword)
        assert hypothesis and known(counterword) and not finite_teacher(counterword)
        fin_oracles[name]={'queries_observed':len(asked),'finite_teacher_agrees_on_all_queries':True,'returned_program_unchanged':True,
                            'unqueried_counterexample':counterword,'hypothesis_answer':True,'finite_teacher_answer':False}
    report['bounds']['finite_oracle_counterexamples']=fin_oracles
    report['bounds']['mn_certificate_scope']='N_K is only a lower bound on DFA states; finite tables do not prove nonregularity or global teacher equivalence'
    report['bounds']['invariant_inference_scope']='phase-linear template and accept/reject structure hard-coded; coefficients computed from selected transition increments; no proof object or general invariant language search'
    report['bounds']['shapley_scope']='eight coalitions toggle pre-acquired component availability, not full replay of discovery/history; scoring excludes macro acquisition, law checks, normalization work and wall time'
    report['status']='PASS for byte integrity and declared finite computations; release-level causal and global claims require scoped correction'
    (DEST/'audit_checks.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'hashes':len(report['hashes']),'reruns':report['rerun'],
                      'abc_verified_gate_witnesses':report['abc']['coalition_gate_witnesses_independently_checked'],
                      'dfa_exhaustive':exhaustive,'mn_pairs':report['dfa']['mn_distinguishers_by_language'],
                      'finite_oracle_counterexamples':fin_oracles,
                      'wrong_law':report['dfa']['wrong_transferred_slope']},ensure_ascii=False,indent=2))

if __name__=='__main__':main()
