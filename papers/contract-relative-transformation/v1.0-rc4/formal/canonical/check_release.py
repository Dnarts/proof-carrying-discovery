#!/usr/bin/env python3
"""Independent T32 reference and runtime-projection cross-check.
No generated data are a Lean kernel log. --lean-log must name actual CLI output.
The reference runs the finite T23/T29/T30 model; witness bounds are supplied
explicitly, or prepared offline for the non-improving control. No timing claim.
"""
import argparse, json, re
from pathlib import Path
from collections import defaultdict, Counter
from dataclasses import replace
import check_policy as P
import check_admission as A
import check_replacement as R
import check_trace as T
from check_pruning import task, brute

HERE=Path(__file__).resolve().parent

def qchain(n):
    out=P.ATTEMPT
    for _ in range(n):out=('obs',0,P.KEEP,out)
    return out

def as_map(c):
    p,a,h=c
    return [list(h),list(p),list(a)]

def fixture(s,t,m,provider,plans):
    initial=m.s; vs=[]; fees=[]
    for base,cand,lo,hi in plans:
        old=m
        # Check supplied bounds independently BEFORE calling the live gate.
        if P.affordable(m.s,base):
            new=P.allin(s,t,provider,cand,A.record(m.s,base))
            assert lo<=P.allin(s,t,provider,m.active,m.s) and new<=hi
        calls=[]
        def make():
            calls.append(True)
            return P.Proposal(cand,lo,hi)
        m,v=P.upgrade(m,base,make)
        assert len(calls)==int(v!='deferred')
        vs.append(v);fees.append(0 if v=='deferred' else base+1)
        T.preserve(old.s,m.s)
    episode,events,status=P.interpret(provider,m.active,m.s)
    final=T.finish(s,t,episode)
    T.preserve(initial,final)
    certs=final.live.current.certs;prior=initial.live.current.certs
    assert not final.live.current.jobs
    assert {(p,a):h for p,a,h in certs}==brute(s,t)
    assert len(certs)==len(brute(s,t))
    assert certs[:len(prior)]==prior
    assert final.spent()==P.allin(s,t,provider,m.active,m.s)
    assert sum(fees)==m.s.spent()-initial.spent()
    ledger=[]
    for ev in reversed(final.journal):
        if ev.kind=='evidence':ledger.append(['evidence',ev.fee])
        else:ledger.append(['attempt',ev.fee,ev.status,ev.charge()])
    search=[[str(k),fee] for k,fee in reversed(final.live.current.receipts)]
    assert sum(f for _,f in search)+sum(e[-1] for e in ledger)==final.spent()
    evs=[]
    for e in events:
        if e[0]=='observed':evs.append(['observed',bool(e[1]),e[2]])
        elif e[0]=='prepared':evs.append(['prepared',e[1],e[2].migration,[list(r) for r in e[2].rows]])
        else:evs.append(['attempted',e[1]])
    return {'metrics':['impossible' if not certs else 'complete',final.spent(),final.live.balance,final.funds(),len(final.live.current.jobs),len(vs),sum(v!='deferred' for v in vs),vs.count('accepted'),len(certs),final.spent()-episode.spent(),len(events)],'status':status,'upgrades':vs,'events':evs,'journal':ledger,'search':search,'prior':[as_map(c) for c in prior],'certificates':[as_map(c) for c in certs]}

def reference():
    s=task(1,2,1,price=(0,0),depth=1);t=task(1,2,1,price=(0,0),depth=0)
    static=R.Controller((),(0,0,0));depth=R.Controller((('depth',0,()),),(0,0,0))
    old=replace(R.root(s,t,static),reserve=100);new=replace(R.rebase(s,t,old,depth),reserve=100)
    o=A.Offer(old,new,1,((7,1),),'closed depth-obstruction example');p=P.Provider(lambda:bool(old.jobs),lambda:o)
    def state(B,tree):return P.Machine(A.Session(R.Live(old,B)),tree)
    m=state(110,P.KEEP);lo=state(103,P.ATTEMPT);tight=state(100,P.QUERY)
    result={}
    result['baseline']=fixture(s,t,m,p,[])
    result['single']=fixture(s,t,m,p,[(0,P.QUERY,7,6)])
    result['mixed']=fixture(s,t,m,p,[(0,P.QUERY,7,6),(0,P.QUERY,6,7)])
    result['double']=fixture(s,t,state(110,qchain(4)),p,[(0,qchain(2),8,7),(0,P.ATTEMPT,7,6)])
    result['fallback']=fixture(s,t,tight,p,[(0,P.QUERY,0,100)]*2)
    result['liquidity-baseline']=fixture(s,t,lo,p,[])
    result['liquidity-rejected']=fixture(s,t,lo,p,[(0,P.ATTEMPT,0,103)])
    pos=replace(R.root(s,s,static),reserve=100)
    for name,n in [('nonempty',0),('predecessor',5)]:
        live=R.prefix(s,s,R.Live(pos,100),n);c=live.current
        offer=A.Offer(c,c,0,((0,100),),'positive fixture');q=P.Provider(lambda:True,lambda:offer)
        result[name]=fixture(s,s,P.Machine(A.Session(live),P.KEEP),q,[])
    assert [result[k]['metrics'][1] for k in result]==[7,6,7,6,7,4,10,11,11]
    assert result['predecessor']['prior'] and len(result['predecessor']['certificates'])==2
    assert result['fallback']['upgrades']==['deferred','deferred'] and result['fallback']['status']=='blocked'
    assert result['liquidity-rejected']['status']=='rejectLiquidity'
    return result

def status(s):
    # Lean Repr of enums is allowed to use a fully qualified constructor.
    for v in ('rejectLiquidity','rejectGain','accepted','rejected','deferred','blocked','kept'):
        if re.search(r'\b'+v+r'\b',s):return v
    raise AssertionError('unrecognized status '+s)

def fields(s):
    return dict(part.split('=',1) for part in s.split(';')[1:] if '=' in part)

def compare(log,ref):
    actual=defaultdict(lambda:defaultdict(list));counts=Counter()
    for line in Path(log).read_text().splitlines():
        if not line.startswith('T32'):continue
        parts=line.split('|');tag,name,*v=parts
        assert name in ref,name
        a=actual[name]
        if tag=='T32':
            assert not a.get('metrics'),name
            a['metrics']=[v[0],*map(int,v[1:])]
        elif tag=='T32STATUS':a['status'].append(status(v[0]))
        elif tag=='T32UPGRADE':a['upgrades'].append(status(v[0]))
        elif tag=='T32SEARCH':a['search'].append([v[0].split('.')[-1],int(v[1])])
        elif tag in ('T32CERT','T32PRIOR'):
            a['certificates' if tag=='T32CERT' else 'prior'].append([list(map(int,z.split(','))) if z else [] for z in v])
        elif tag=='T32EVENT':
            f=fields(v[0]);kind=v[0].split(';')[0]
            if kind=='observed':a['events'].append([kind,f['answer']=='true',int(f['fee'])])
            elif kind=='prepared':
                rows=[[int(x),int(y)] for x,y in re.findall(r'\((\d+),\s*(\d+)\)',f['rows'])]
                a['events'].append([kind,int(f['fee']),int(f['migration']),rows])
            elif kind=='attempted':a['events'].append([kind,status(f['verdict'])])
            else:raise AssertionError(kind)
        elif tag=='T32JOURNAL':
            f=fields(v[0]);kind=v[0].split(';')[0]
            if kind=='evidence':a['journal'].append([kind,int(f['fee'])])
            elif kind=='attempt':a['journal'].append([kind,int(f['checkFee']),status(f['verdict']),int(f['debit'])])
            else:raise AssertionError(kind)
        else:raise AssertionError(tag)
        counts[tag]+=1
    assert set(actual)==set(ref)
    for name,r in ref.items():
        a=actual[name];assert a['metrics']==r['metrics'],(name,a['metrics'],r['metrics'])
        assert a['status']==[r['status']],name
        for k in ('upgrades','events','journal','prior','certificates'):
            assert a[k]==r[k],(name,k,a[k],r[k])
        assert a['search']==r['search'],(name,'search',a['search'],r['search'])
    print('PASS actual Lean runtime projection against independent finite reference:',dict(sorted(counts.items())))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--lean-log');ap.add_argument('--write-reference',action='store_true');args=ap.parse_args()
    ref=reference();p=HERE/'FINITE_RELEASE.json'
    if args.write_reference:p.write_text(json.dumps(ref,indent=2,sort_keys=True)+'\n')
    else:assert json.loads(p.read_text())==ref,'reference mismatch'
    for k,r in ref.items():print(k,':',r['metrics'],'status',r['status'],'upgrades',r['upgrades'])
    print('PASS 9 independent release fixtures, complete canonical membership, predecessor preservation and ordered paid ledgers. Not Lean execution.')
    if args.lean_log:compare(args.lean_log,ref)
