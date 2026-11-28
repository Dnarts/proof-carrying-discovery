#!/usr/bin/env python3
"""Independent T30 finite reference; not Lean execution or measured runtime.
All future bill bounds are prepared OFFLINE for this finite fixture. Runtime
selection invokes the solver and the provider only after the declared charges.
"""
from dataclasses import dataclass, replace
from itertools import product
from collections import Counter
from random import Random
from functools import lru_cache
import check_admission as A
import check_replacement as R
import check_trace as T
from check_pruning import task, rand_task, brute
from check_decision import solve, objective as tree_objective, trees, regret_table

KEEP=('act',0); ATTEMPT=('act',1); QUERY=('obs',0,KEEP,ATTEMPT)

@dataclass(frozen=True)
class Provider:
    probe:object
    prepare:object
    query_base:int=0
    prep_base:int=0
    check_base:int=0


def affordable(s,base):return base+1+s.live.current.reserve<=s.live.balance

def interpret(p,t,s):
    if t[0]=='act':
        if not t[1]:return s,(), 'kept'
        if not affordable(s,p.prep_base):return s,(),'blocked'
        g=A.record(s,p.prep_base);o=p.prepare();v,x=A.attempt(g,o,p.check_base)
        T.preserve(s,x)
        return x,(('prepared',p.prep_base+1,o),('attempted',v)),v
    if not affordable(s,p.query_base):return s,(),'blocked'
    g=A.record(s,p.query_base);b=p.probe()
    x,events,v=interpret(p,t[3] if b else t[2],g)
    T.preserve(s,x)
    return x,(('observed',b,p.query_base+1),)+events,v

@dataclass(frozen=True)
class Machine:
    s:A.Session
    active:tuple
    history:tuple=()

@dataclass(frozen=True)
class Proposal:
    tree:tuple
    old_lower:int
    new_upper:int


def upgrade(m,base,make):
    if not affordable(m.s,base):return m,'deferred'
    g=A.record(m.s,base);o=make()
    status='accepted' if o.new_upper<o.old_lower else 'rejected'
    next=Machine(g,o.tree if status=='accepted' else m.active,((base+1,status,m.active,o.tree,m.s.live.balance,o.old_lower,o.new_upper),)+m.history)
    T.preserve(m.s,g);assert g.spent()==m.s.spent()+base+1
    assert next.history[1:]==m.history
    return next,status


def allin(s,t,p,tree,x):return T.objective(s,t,interpret(p,tree,x)[0])

def offer(s,t,old,ctrl,slack=0):
    new=R.rebase(s,t,old,ctrl,slack=slack)
    a,b=T.bill(s,t,old),T.bill(s,t,new)
    return A.Offer(old,new,1,((a,b),(a+100,b+100)),'offline fixed witness')


def fixture(c):
    s=task(1,2,1,depth=1);t=task(1,2,1,depth=0)
    static=R.Controller((),(0,0,0));depth=R.Controller((('depth',0,()),),(0,0,0))
    old=replace(R.root(s,t,static),reserve=100);new=replace(R.rebase(s,t,old,depth),reserve=100)
    initial=A.Session(R.Live(old,110));empty=T.finish(s,t,initial)
    a=A.Offer(old,new,1,((7,1),),'closed root bound');b=offer(s,t,empty.live.current,static)
    # Real runtime observation on the remaining frontier. Both offers are fixed
    # pre-certified fixtures, not free live completion evaluations.
    calls=Counter()
    def provider(x,o):
        def probe():calls['query']+=1;return bool(x.live.current.jobs)
        def prep():calls['prepare']+=1;return o
        return Provider(probe,prep)
    good,bad=provider(initial,a),provider(empty,b)
    # Offline verify both declared terminal-action rows against actual runner.
    cost=((0,2),(7,4));regret,_=regret_table(cost);read=((False,True),);fee=(1,)
    for h,x,p in ((0,empty,bad),(1,initial,good)):
        for act in (0,1):
            assert allin(s,t,p,('act',act),x)-x.spent()==cost[h][act];c['terminal_table_checks']+=1
    value,tree=solve(regret,(0,1),read,fee,(0,),1)
    assert value==min(tree_objective(u,regret,(0,1),read,fee) for u in trees(2,(0,),1))==1
    assert tree==QUERY
    assert allin(s,t,good,tree,initial)==5 and allin(s,t,bad,tree,empty)==8
    m=Machine(initial,KEEP);g=A.record(initial,0)
    # Bounds certified offline against these exact before/after states.
    assert allin(s,t,good,KEEP,initial)==7 and allin(s,t,good,tree,g)==6
    calls.clear()
    def synthesize():
        calls['synthesis']+=1
        _,selected=solve(regret,(0,1),read,fee,(0,),1)
        return Proposal(selected,7,6)
    n,v=upgrade(m,0,synthesize);assert v=='accepted' and calls=={'synthesis':1}
    out,events,verdict=interpret(good,n.active,n.s)
    assert verdict=='accepted' and calls=={'synthesis':1,'query':1,'prepare':1}
    assert events==( ('observed',True,1),('prepared',1,a),('attempted','accepted') )
    done=T.finish(s,t,out);assert done.spent()==6
    assert done.spent()<T.finish(s,t,initial).spent()==7
    assert done.live.current.certs==()
    c['closed_switches']+=1
    def poison():raise AssertionError('unpaid computation forced')
    tight=A.Session(R.Live(old,100));calls.clear()
    poison_p=Provider(poison,poison)
    assert interpret(poison_p,QUERY,tight)==(tight,(),'blocked')
    assert interpret(poison_p,ATTEMPT,tight)==(tight,(),'blocked')
    tightm=Machine(tight,KEEP);assert upgrade(tightm,0,poison)==(tightm,'deferred')
    c['poison_guards']+=3
    # Paying for an unprofitable policy upgrade can increase total expense.
    r,v=upgrade(m,0,lambda:Proposal(KEEP,7,8));assert v=='rejected' and r.active==m.active
    assert allin(s,t,good,r.active,r.s)==8
    c['negative_upgrade']+=1
    print('Closed terminal incremental bills: exhausted=(0,2), pending=(7,4).')
    print('T27 synthesized query: regret value 1; pending bill 5, exhausted incremental bill 1.')
    print('Installed policy: original completion 7; new all-in completion 6 (synthesis/admission, query, preparation, root check, migration, execution: 1 each).')
    print('Negative control: rejected policy synthesis/check costs 1; unchanged completion rises 7 -> 8.')


def finite(c):
    rng=Random(301128)
    controllers=[R.Controller((),(0,0,0)),R.Controller((('depth',0,()),),(0,0,0)),R.Controller((('read',0,()),),(0,0,0))]
    models=[(task(2,2,1,mat[:2]),task(2,2,1,mat[2:])) for mat in list(product(product((0,1),repeat=2),repeat=4))[::8]]
    models += [(rand_task(rng,rng.randrange(3),rng.randrange(3),1),rand_task(rng,rng.randrange(3),rng.randrange(3),1)) for _ in range(16)]
    policies=trees(2,(0,),1)
    for s,t in models:
        ref=brute(s,t);c['task_pairs']+=1
        root=R.root(s,t,rng.choice(controllers));base=A.Session(R.Live(root,root.reserve+20))
        for n in (0,3,root.reserve):
            x=T.advance(s,t,base,n);old=x.live.current
            o=offer(s,t,old,rng.choice(controllers))
            for surplus,query_base,prep_base in product((0,1,2,5,20),(0,1),(0,1)):
                f=replace(x,live=replace(x.live,balance=old.reserve+surplus))
                for tree in policies:
                    calls=Counter()
                    def probe():calls['observed']+=1;return bool(old.jobs)
                    def prep():calls['prepared']+=1;return o
                    p=Provider(probe,prep,query_base,prep_base,0)
                    out,events,v=interpret(p,tree,f);T.preserve(f,out)
                    assert calls['observed']==sum(ev[0]=='observed' for ev in events)
                    assert calls['prepared']==sum(ev[0]=='prepared' for ev in events)
                    # Every paid operation has a corresponding authoritative debit.
                    expected=0
                    for ev in events:
                        if ev[0]=='observed':expected+=ev[2]
                        elif ev[0]=='prepared':
                            expected+=ev[1];assert ev[2]==o
                        else:expected+=A.debit(1,o.migration,ev[1])
                    assert out.spent()-f.spent()==expected
                    done=T.finish(s,t,out);T.preserve(f,done)
                    assert {(p,a):h for p,a,h in done.live.current.certs}==ref
                    assert done.spent()==T.objective(s,t,out)
                    c['executed_policies']+=1;c['outcome_'+v]+=1
    return c

if __name__=='__main__':
    c=Counter();fixture(c);finite(c)
    for k,v in sorted(c.items()):print(f'{k}: {v}')
    print('PASS actual finite T23 runner, paid policy thunks, protected fallback, synthesis/installation and complete reference membership. Not Lean execution.')
