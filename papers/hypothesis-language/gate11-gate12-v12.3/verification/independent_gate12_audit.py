#!/usr/bin/env python3
"""Finite independent replay for Gate 12 v12.3 archive.

Source-preserving. No Lean compiler is invoked. This auditor validates the
package, reconstructs the two learned programs, checks their finite behavior,
and distinguishes selected-evidence indices from actual oracle queries.
"""
import hashlib, itertools, json, pathlib, sys, importlib.machinery, importlib.util, subprocess
ROOT=pathlib.Path(__file__).resolve().parent.parent / "gate12"
loader=importlib.machinery.SourceFileLoader('gate12_supplied',(ROOT/'gate12_blind_chomsky_escalation.py').as_posix())
spec=importlib.util.spec_from_loader(loader.name,loader)
g=importlib.util.module_from_spec(spec);sys.modules[spec.name]=g;spec.loader.exec_module(g)

def local_stack_eval(prog,w):
    # Independent interpreter, not calling StackProgram.eval.
    phase=int(prog.start_phase)
    stack=[]
    for symbol in w:
        action=prog.table[phase][symbol]
        if action is None:return 0
        next_phase,op=action
        if op=='push':stack.append(symbol)
        elif op=='pushFlip':stack.append(1-symbol if symbol in (0,1) else symbol)
        elif op=='popMatch':
            if not stack or stack[-1]!=symbol:return 0
            stack.pop()
        elif op=='keep':pass
        else:raise ValueError(op)
        phase=next_phase
    return int(not stack and phase in prog.accept_phases)

def replay_one(tag,oracle,expected_transform):
    seen=[]
    dca_markers=[]
    old_mn=g.build_mn_certificate
    old_dca=g.build_1dca_impossibility_certificate
    def tracer_mn(*args,**kwargs):
        result=old_mn(*args,**kwargs)
        dca_markers.append({'stage':'MN_witness_discovery','oracle_queries_seen_so_far':len(seen)})
        return result
    def tracer_dca(*args,**kwargs):
        result=old_dca(*args,**kwargs)
        dca_markers.append({'stage':'DCA_witness_discovery','oracle_queries_seen_so_far':len(seen)})
        return result
    g.build_mn_certificate=tracer_mn
    g.build_1dca_impossibility_certificate=tracer_dca
    try:
        def logging_oracle(w):
            seen.append(w);return oracle(w)
        run=g.run_blind_causal_escalation(logging_oracle)
    finally:
        g.build_mn_certificate=old_mn
        g.build_1dca_impossibility_certificate=old_dca
    assert run.stack_prog.inferred_binary_transform()==expected_transform
    assert (run.t1_dfa_refuted,run.t2_dca_refuted)==(9,54)
    assert len(seen)==run.total_oracle_queries
    errors=[];checks=0
    for n in range(10):
        for w in itertools.product((0,1,2),repeat=n):
            a=local_stack_eval(run.stack_prog,w)
            b=oracle(w)
            checks+=1
            if a!=b:errors.append([w,a,b])
    assert not errors,errors[:2]
    return {'label':tag,'checked_all_words_length_0_through_9':checks,
            'errors':len(errors),'all_actual_oracle_calls':len(seen),
            'stored_witness_observations':len(run.obs),'t1_stored_prefix_index':run.t1_dfa_refuted,
            't2_stored_prefix_index':run.t2_dca_refuted,'oracle_queries_before_witness_recording':dca_markers,
            'program_transition_table':run.stack_prog.table,
            'retained_observations_not_proof_of_original_oracle_time_order':True}

manifest=json.loads((ROOT/'gate12_final_manifest.json').read_text())
sha_checks={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==expect for name,expect in manifest['output_files_sha256'].items()}
assert all(sha_checks.values())
regen_path=ROOT/'independent_regenerated.lean'
if not regen_path.exists():
    subprocess.run([sys.executable,(ROOT/'gate12_blind_chomsky_escalation.py').as_posix(),'--export-lean',regen_path.as_posix()],cwd=ROOT,check=True,capture_output=True,text=True,timeout=60)
regen=regen_path.read_bytes()
orig=(ROOT/'gate12_exported_pal_mid.lean').read_bytes()
result={'abi':'gate12-v12.3-independent-finite-audit/1','source_archive':'bundled Gate 12 v12.3 verified sources',
        'manifest_hashes_matched':len(sha_checks),'manifest_hashes_all_pass':True,
        'export_exact_byte_match':regen==orig if regen is not None else None,
        'lean_recompiled_here':False,
        'declared_formal_toolchain':'Lean 4.36.0, as supplied in included verification log',
        'pal':replay_one('pal',g.oracle_pal_mid,(0,1)),
        'antipal':replay_one('antipal',g.oracle_antipal_mid,(1,0)),
        'limitations':[
          'The theorem is relative to Gate12Hierarchy.CounterProgram and the canonical StackProgram family; not arbitrary machine implementations.',
          'The master checker proves selected evidence prefix order and refutability; it does not validate actual oracle call timestamps or prevent lookahead in Python.',
          'The canonical recognizer accepts a fixed two-phase push-then-pop grammar with a binary f; it is not synthesis of arbitrary DPDA semantics.',
          'The archive includes a Lean log, but the local environment lacks lean. No fresh Lean kernel run was performed.',
          'The archive does not contain run_gate12_verification.sh; that script was uploaded separately.',
          'Finite oracle sample compatibility does not itself prove the oracle equals the formal target on all words.'
        ]}
assert result['pal']['checked_all_words_length_0_through_9']==29524
assert result['antipal']['checked_all_words_length_0_through_9']==29524
path=pathlib.Path(__file__).resolve().parent/'independent_audit_replay.json';path.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print('RESULT',path)
print('HASHES',len(sha_checks),'EXPORTED_BYTE_EQUAL',result['export_exact_byte_match'])
for key in ('pal','antipal'):
 x=result[key];print(key,'checks',x['checked_all_words_length_0_through_9'],'errors',x['errors'],'oracle',x['all_actual_oracle_calls'],'recorded',x['stored_witness_observations'],'trace_markers',x['oracle_queries_before_witness_recording'])
