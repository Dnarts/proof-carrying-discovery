#!/usr/bin/env python3
"""Independent finite T25 model. Does not execute or compile Lean.
Cost tables are built offline, and charged separately from selected execution.
No sensor is allowed to read the selected world-dependent payoff table.
"""
from itertools import product
from collections import Counter
from random import Random
from typing import NamedTuple
from check_pruning import task, rand_task, brute
import check_impasse as B
import check_learning as L

class Plan(NamedTuple):
    rules: tuple
    learning: int
    setup: int

HANDOFF=Counter()

FEES=L.Fees(base=(1,1,1),lookup=0,perCore=1,probe=9,compile=10)
PLANS=(Plan((),0,0),Plan((('read',0,None),),0,0),
       Plan((('price',0,None),),0,0),Plan((('injective',0,None),),0,0),
       Plan((),12,2),Plan((),50,2))

def initial_reserve(s,t,p):
    return B.potential(s,t,p.rules,FEES.base,B.initial(s,p.rules))

def perform(s,t,p,reserve,ref):
    start=L.topup(L.initial(s,p.rules),p.learning)
    cap=initial_reserve(s,t,p)
    def verify(old,new):
        assert B.potential(s,t,p.rules,FEES.base,new.state.frontier) <= B.potential(s,t,p.rules,FEES.base,old.state.frontier)
        assert new.spent+new.remaining==p.learning
    mid=L.run(s,t,p.rules,FEES,start,inv=verify)
    f=mid.state.frontier
    HANDOFF["prefix_paid"]+=int(mid.spent>0)
    HANDOFF["prefix_with_compiled_core"]+=int(bool(mid.state.history))
    HANDOFF["prefix_with_certificates"]+=int(bool(f.certs))
    HANDOFF["handoff_pending_compilation"]+=int(mid.state.pending is not None)
    HANDOFF["handoff_remaining_jobs"]+=int(bool(f.jobs))
    assert B.potential(s,t,p.rules,FEES.base,f)<=cap<=reserve
    inp=f._replace(remaining=mid.remaining+reserve,spent=mid.spent)
    done=B.execute(s,t,p.rules,FEES.base,inp)
    assert not done.jobs
    assert {(x,a):h for x,a,h in done.certs}==ref
    assert done.spent+done.remaining==p.learning+reserve
    assert done.spent+sum(v for _,v in f.receipts)==sum(v for _,v in mid.state.feesPaid)+sum(v for _,v in done.receipts)
    if p.learning==0:
        assert done==B.execute(s,t,p.rules,FEES.base,B.initial(s,p.rules,reserve))
    return p.setup+done.spent

# Trees contain only plan IDs or sensor labels, never hidden-world IDs.
def walk(tree,observations,prices):
    paid=0
    while tree[0]=='obs':
        _,q,l,r=tree; paid+=prices[q];tree=r if observations[q] else l
    return tree[1],paid

def bill(tree,w,table,bits,prices):
    a,c=walk(tree,bits[w],prices)
    return c+table[w][a]

def worst(tree,ws,table,bits,prices):
    return max((bill(tree,w,table,bits,prices) for w in ws),default=0)

def solve(ws,ports,depth,table,bits,prices,na):
    leaf=[('act',a) for a in range(na)]
    candidates=list(leaf)
    if depth:
        for q in ports:
            rest=tuple(p for p in ports if p!=q)
            l=solve(tuple(w for w in ws if not bits[w][q]),rest,depth-1,table,bits,prices,na)
            r=solve(tuple(w for w in ws if bits[w][q]),rest,depth-1,table,bits,prices,na)
            candidates.append(('obs',q,l,r))
    return min(candidates,key=lambda t:worst(t,ws,table,bits,prices))

def trees(ports,depth,na):
    yield from (('act',a) for a in range(na))
    if depth:
        for q in ports:
            rest=tuple(p for p in ports if p!=q)
            children=list(trees(rest,depth-1,na))
            for l,r in product(children,repeat=2):yield ('obs',q,l,r)

def table_for(family,plans,count):
    # A fixed reserve per plan, independent of the unknown meta world.
    reserves=[max(initial_reserve(s,t,p) for s,t in family) for p in plans]
    table=[]
    for s,t in family:
        ref=brute(s,t);row=[]
        count["nonempty_reference_worlds"]+=int(bool(ref))
        count["empty_reference_worlds"]+=int(not ref)
        for p,r in zip(plans,reserves):
            row.append(perform(s,t,p,r,ref));count['complete_plans']+=1
        table.append(tuple(row))
    return tuple(table)

def main():
    rng=Random(2501); count=Counter()
    # Three possible task pairs with the same carrier sizes. Actual cost table
    # comes from paid executions, not fabricated performance labels.
    for k in range(128):
        sw,tw,sp,tp,sa,ta=(rng.randrange(3),rng.randrange(3),rng.randrange(3),rng.randrange(3),rng.randrange(1,3),rng.randrange(1,3))
        family=[(rand_task(rng,sw,sp,sa),rand_task(rng,tw,tp,ta)) for _ in range(3)]
        table=table_for(family,PLANS,count); na=len(PLANS)
        # Sensor 0: depth compatibility. Sensor 1: a specified read-bit comparison
        # (false if one of the relevant carriers is empty). These do not use table.
        bits=tuple((s.depth<=t.depth, bool(sw and tw and sp and tp and s.read[0][0]==t.read[0][0])) for s,t in family)
        prices=(rng.randrange(4),rng.randrange(4)); ws=tuple(range(3)); fee=rng.randrange(5)
        ts=list(trees((0,1),2,na))
        for exact in (True,False):
            bound=table if exact else tuple(tuple(v+rng.randrange(8) for v in row) for row in table)
            opt=solve(ws,(0,1),2,bound,bits,prices,na)
            predicted=fee+worst(opt,ws,bound,bits,prices)
            actual=fee+worst(opt,ws,table,bits,prices)
            assert actual<=predicted
            assert predicted==min(fee+worst(t,ws,bound,bits,prices) for t in ts)
            if exact:assert actual==predicted==min(fee+worst(t,ws,table,bits,prices) for t in ts)
            for w in ws:
                a,c=walk(opt,bits[w],prices)
                assert fee+c+table[w][a]<=predicted
                s,t=family[w];ref=brute(s,t);r=max(initial_reserve(ss,tt,PLANS[a]) for ss,tt in family)
                assert fee+c+perform(s,t,PLANS[a],r,ref)==fee+c+table[w][a]
                count['selected_reruns']+=1
            count['meta_cases']+=1;count['tree_comparisons']+=len(ts)
            count['actual_optimality_checks']+=len(ts) if exact else 0
    # Explicit positive and empty-carrier controls, separate from random panels.
    for source in (task(2,2,2,((0,1),(1,0))),task(1,0,1),task(0,0,1)):
        assert brute(source,source)
        table_for(((source,source),),PLANS,count)
    # Concrete same-shape witness from reference-model search. The sole sensor
    # reads the first source task bit. It is not an oracle for the best plan.
    family=(
      (task(2,3,2,((0,0),(1,1),(1,0)),(1,0,1),((2,2),(1,0)),3),
       task(2,3,2,((0,0),(0,0),(0,0)),(0,1,0),((0,2),(2,2)),3)),
      (task(2,3,2,((1,0),(0,1),(1,0)),(1,0,1),((2,1),(0,2)),3),
       task(2,3,2,((0,1),(0,1),(1,0)),(2,2,0),((2,2),(1,1)),3)))
    table=table_for(family,PLANS[:4],count); assert table==((80,21,87,63),(80,53,18,63)),table
    bits=tuple((bool(s.read[0][0]),) for s,t in family);prices=(1,);ws=(0,1)
    opt=solve(ws,(0,),1,table,bits,prices,4)
    fixed=min(worst(('act',a),ws,table,bits,prices) for a in range(4))
    mediated=3+worst(opt,ws,table,bits,prices)
    assert (fixed,mediated)==(53,25)
    acquisition=sum(map(sum,table)); n=acquisition//(fixed-mediated)+1
    assert acquisition+(n-1)*mediated >= (n-1)*fixed
    assert acquisition+n*mediated < n*fixed
    assert 40+worst(opt,ws,table,bits,prices)>fixed # high controller fee negates advantage
    # Sound but loose table need not select an actual optimum.
    assert solve((0,),(),0,((10,2),), ((),),(),2)==('act',1)
    assert worst(('act',1),(0,),((1,2),),((),),())>worst(('act',0),(0,),((1,2),),((),),())
    # Empty meta-world set: the fixed controller overhead is still specified.
    assert worst(solve((),(0,),1,(),(),(1,),2),(),(),(),(1,))==0
    for setup,nuse,old,new in product(range(10),repeat=4):
        if new<=old:
            assert (setup+nuse*new<nuse*old)==(setup<nuse*(old-new));count['amortization_cases']+=1
    for k,v in sorted(count.items()):print(f'{k}: {v}')
    for k,v in sorted(HANDOFF.items()):print(f'{k}: {v}')
    print('Witness table:',table,'tree:',opt,'fixed worst:',fixed,'meta worst incl. fee:',mediated)
    print('Offline table acquisition (sum of the eight modeled runs):',acquisition,'strict amortization at uses:',n)
    print('PASS exact/bounded tables, selected reruns, frontier handoff, no-learning control, paid trace, fixed uniform reserves, finite minimax, costly-controller and loose-bound counterexamples. Not Lean execution.')

if __name__=='__main__':main()
