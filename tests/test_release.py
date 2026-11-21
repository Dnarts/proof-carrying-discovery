#!/usr/bin/env python3
"""Independent protocol checks. Only Python's standard library is used."""
import copy
import itertools
import json
import math
import pathlib
import sys
import unittest

ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'v1_1'))
from dfa_to_1dca_v1_1 import (oracle_0n1n_offset,oracle_0plus1plus,fixed_engine_F,
   myhill_nerode_table,run_dca,infer_and_verify_linear_invariant,certify_phase_linear_relation,
   Q1,S1,framed,build_quotient_dfa,product_equivalence_certificate,canonical_regex_reference)
from abc_historical_v1_1 import (run_all as replay_history, exact_shapley, all_coalitions,
    discover_history,PLAYERS,B_MAX,target_specs,kernel,sha)


def independent_oracle(word,offset=None):
    if not isinstance(word,str) or len(word)<3 or word.count('$')!=1 or not word.endswith('$'):
        return False
    body=word[:-1]
    if any(ch not in '01' for ch in body):return False
    nz=len(body)-len(body.lstrip('0'))
    ones=body[nz:]
    if nz<1 or len(ones)<1 or any(x!='1' for x in ones):return False
    if offset is None:return True
    return nz+offset==len(ones)


def independent_run(table,word):
    if not word.endswith('$') or word.count('$')!=1 or any(x not in '01' for x in word[:-1]):return False
    q='q0';counter=0
    for i,letter in enumerate(word):
        if q in ('acc','rej'):return False
        key=(q,letter,1 if counter>0 else 0)
        if key not in table:return False
        nq,delta=table[key]
        counter+=delta
        if counter<0:return False
        q=nq
    return q=='acc'


def independent_circuit(bits,number_inputs,dag):
    def evaluate(row):
        wires=[(row>>i)&1 for i in range(number_inputs)]
        for g,i,j in dag:
            a,b=wires[i],wires[j]
            if g=='NAND':wires.append(1-(a&b))
            elif g=='XOR':wires.append(a^b)
            else:raise AssertionError(g)
        return wires[-1]
    return sum(evaluate(row)<<row for row in range(1<<number_inputs))==bits


class IndependentReleaseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dca=json.loads((ROOT/'v1_1/dfa_to_1dca_v1_1_results.json').read_text())
        cls.abc=json.loads((ROOT/'v1_1/abc_historical_v1_1_results.json').read_text())

    def table(self,raw):
        return {(q,s,int(z)):tuple(action) for key,action in raw.items() for q,s,z in [key.split(',')]}

    def test_dca_full_short_language(self):
        d=self.dca
        cases=[(d['T1_0n1n'],0),
               (d['T2_0n1n_plus_1']['without_I1'],1),
               (d['T2_0n1n_plus_1']['with_I1'],1),
               (d['wrong_transfer_control'],1)]
        checked=0
        for item,offset in cases:
            t=self.table(item['dca_synthesis']['table'])
            for n in range(0,9):
                for symbols in itertools.product('01$',repeat=n):
                    word=''.join(symbols)
                    expected=independent_oracle(word,offset)
                    self.assertEqual(independent_run(t,word),expected,(offset,word))
                    self.assertEqual(run_dca(t,word),expected,(offset,word))
                    checked+=1
        self.assertEqual(checked,4*9841)
        for word in ('01$$','01$0','01$1','01','01x$','$',''):
            self.assertFalse(independent_run(self.table(cases[0][0]['dca_synthesis']['table']),word))

    def test_nondegenerate_mn_witnesses(self):
        cases=[(oracle_0n1n_offset(0),2,6),(oracle_0n1n_offset(1),5,6)]
        for oracle,K,N in cases:
            tbl=myhill_nerode_table(oracle,K)
            self.assertEqual(tbl['distinct_classes'],N)
            self.assertEqual(len(tbl['pair_witnesses']),N*(N-1)//2)
            for w in tbl['pair_witnesses']:
                self.assertNotEqual(independent_oracle(w['p']+w['suffix'],0 if K==2 else 1),
                                    independent_oracle(w['q']+w['suffix'],0 if K==2 else 1))

    def test_semantic_invariant_certificate_and_mutation(self):
        for task,offset in [(self.dca['T1_0n1n'],0),
                            (self.dca['T2_0n1n_plus_1']['with_I1'],1)]:
            table=self.table(task['dca_synthesis']['table'])
            i=infer_and_verify_linear_invariant(table)
            cert=certify_phase_linear_relation(table,i,{'kind':'offset','offset':offset})
            self.assertEqual(cert['status'],'PROVED_RELATIVE_TO_KNOWN_OFFSET_FAMILY')
            self.assertEqual(cert['semantic']['coefficients'],[1,-1,offset])
            tampered=copy.deepcopy(i);tampered['inv']['a0']=10
            self.assertEqual(certify_phase_linear_relation(table,tampered,{'kind':'offset','offset':offset})['status'],'INVALID_CERTIFICATE')
            bad=copy.deepcopy(table);bad[(Q1,S1,1)]=('q1',0)
            self.assertFalse(infer_and_verify_linear_invariant(bad)['found'])
            # The exported-certificate checker must reject a stale invariant
            # after any of the four phase-building destinations changes.
            # These are semantically different machines even when their
            # counter deltas and previously recorded flags remain unchanged.
            for cell in [('q0','0',0),('q0','0',1),('q0','1',1),('q1','1',1)]:
                with self.subTest(offset=offset,mutation='phase destination',cell=cell):
                    changed=copy.deepcopy(table)
                    changed[cell]=('rej',changed[cell][1])
                    self.assertEqual(certify_phase_linear_relation(
                        changed,i,{'kind':'offset','offset':offset})['status'],
                        'INVALID_CERTIFICATE')
            with self.subTest(offset=offset,mutation='unequal zero increments'):
                changed=copy.deepcopy(table)
                changed[('q0','0',1)]=('q0',0)
                self.assertEqual(certify_phase_linear_relation(
                    changed,i,{'kind':'offset','offset':offset})['status'],
                    'INVALID_CERTIFICATE')

    def test_wrong_law_fallback_is_certified(self):
        d=self.dca
        self.assertEqual(d['T1_0n1n']['dca_synthesis']['nodes'],26)
        self.assertEqual(d['T2_0n1n_plus_1']['without_I1']['dca_synthesis']['nodes'],57)
        self.assertEqual(d['T2_0n1n_plus_1']['with_I1']['dca_synthesis']['nodes'],28)
        self.assertTrue(d['wrong_transfer_control']['fallback_used'])
        self.assertEqual(d['wrong_transfer_control']['attempts'][0]['certificate_status'],'NO_PROGRAM')
        self.assertEqual(d['wrong_transfer_control']['attempts'][1]['nodes'],57)

    def test_regex_dfa_is_proved_against_explicit_reference(self):
        p=self.dca['T_neg_0plus1plus']['formal_reference_equivalence']
        self.assertTrue(p['equivalent'])
        self.assertEqual(p['checked_product_pairs'],5)
        ref=canonical_regex_reference()
        finite=build_quotient_dfa(oracle_0plus1plus,5)
        self.assertTrue(product_equivalence_certificate(finite['_raw'],ref)['equivalent'])

    def test_finite_teacher_indistinguishability_is_not_a_global_certificate(self):
        queries={}
        def logger(w):
            a=oracle_0plus1plus(w)
            queries[w]=a
            return a
        preliminary=fixed_engine_F('test',logger,teacher_contract={'kind':'regex_0plus1plus'})
        self.assertEqual(preliminary['oracle_global_equivalence'],'UNKNOWN')
        finite_positive={w for w,out in queries.items() if out}
        finite_teacher=lambda w:w in finite_positive
        replay=fixed_engine_F('test',finite_teacher,teacher_contract={'kind':'regex_0plus1plus'})
        self.assertEqual(replay['oracle_global_equivalence'],'UNKNOWN')
        unknown='000000111111$'
        self.assertNotIn(unknown,queries)
        self.assertTrue(oracle_0plus1plus(unknown))
        self.assertFalse(finite_teacher(unknown))
        self.assertEqual(preliminary['dfa_solution']['transitions'],replay['dfa_solution']['transitions'])

    def test_abc_coalition_replays_cost_and_circuits(self):
        a=self.abc
        self.assertEqual(len(a['replays']),8)
        self.assertEqual(len(a['shapley_replayed_histories']),4)
        specs=target_specs()
        for key,run in a['replays'].items():
            c=() if key=='EMPTY' else tuple(key.split(','))
            self.assertEqual(run['coalition'],list(c))
            self.assertEqual(len(run['history']),3)
            self.assertEqual(sha(run['history']),run['history_sha256'])
            for name,result in run['tasks'].items():
                if result['found']:
                    self.assertTrue(independent_circuit(specs[name]['target'],specs[name]['n_inputs'],result['gates']))
                    self.assertLessEqual(result['evals'],B_MAX)
        for name,result in a['shapley_replayed_histories'].items():
            self.assertAlmostEqual(sum(result['shapley'].values()),result['v_full'],places=10)
            for v in result['coalition_values'].values():
                self.assertGreater(v['work_units'],0)
        self.assertLess(a['shapley_replayed_histories']['Tneg_AND3']['shapley']['e2_XOR_macro'],0)
        # Event e2 genuinely has a different acquisition cost with e1 present.
        self.assertEqual(a['replays']['e2_XOR_macro']['acquisition']['candidate_evals'],1535)
        self.assertEqual(a['replays']['e1_NAND_law,e2_XOR_macro']['acquisition']['candidate_evals'],341)
        for lam,metric in a['sensitivity_suite'].items():
            self.assertAlmostEqual(sum(metric['shapley'].values()),metric['v_full'],places=10)

    def test_no_global_equivalence_claim_for_unknown_offset_teacher(self):
        oracle=oracle_0n1n_offset(0)
        wrapped=lambda w:oracle(w)
        r=fixed_engine_F('unknown',wrapped,teacher_contract={'kind':'offset','offset':0})
        self.assertEqual(r['oracle_global_equivalence'],'UNKNOWN')
        self.assertEqual(r['phase_certificate']['status'],'PROVED_PROGRAM_LANGUAGE_ONLY')

    def test_original_legacy_sources_immutable(self):
        import hashlib
        hashes={
          'abc_shapley_v1.py':'90edaa1d3e9b9ddbccee07bd3893562054aabf5ae899013388a5419c6bf828fc',
          'dfa_to_1dca_v1.py':'4975381c4ed98e8db13be24029fb6c6d21a49dffea1851b258a00d9066b8d9ba',
          'abc_shapley_v1_results.json':'13d3eedccdfe6df9ec8ec4a0e0eb1734a0a8559627d10b69ee7d6475025c4958',
          'dfa_to_1dca_v1_results.json':'6b4bac1a9937cae3e0e5f1d8791f0af07cac5346e2712618099f86976ccae459'}
        for name,h in hashes.items():
            self.assertEqual(hashlib.sha256((ROOT/'legacy'/name).read_bytes()).hexdigest(),h)


if __name__=='__main__':
    unittest.main(verbosity=2)
