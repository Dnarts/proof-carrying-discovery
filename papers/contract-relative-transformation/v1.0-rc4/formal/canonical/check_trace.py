#!/usr/bin/env python3
"""Independent finite checks for T29c; NOT execution of the Lean module.
Reuse the T29b numeric gate and actual T23 finite reference execution.
Prospective cost evidence is constructed OFFLINE for the test fixtures.
"""
from collections import Counter
from dataclasses import dataclass, replace
from functools import lru_cache
from itertools import product
from random import Random
import check_admission as A
import check_replacement as R
from check_pruning import task, rand_task, brute


def generic_checks(c):
    def run(q,n,x):
        pos,b,spent=x
        for _ in range(n):
            step=q[pos]
            if step is None or step[0]>b:break
            fee,pos=step;b-=fee;spent+=fee
        return pos,b,spent
    for q in product([None,*product(range(1,4),range(2))],repeat=2):
        for pos,b,n in product(range(2),range(10),range(12)):
            p=run(q,n,(pos,b,0));tail=run(q,p[1],(p[0],p[1],0));whole=run(q,b,(pos,b,0))
            assert whole==(tail[0],tail[1],p[2]+tail[2]);c['prefix_bill']+=1
            for k in (0,1,7):
                assert run(q,n,(pos,b,k))==(p[0],p[1],p[2]+k);c['spent_shift']+=1

@lru_cache(maxsize=4096)
def bill(s,t,cont):return R.remaining_bill(s,t,cont)
def objective(s,t,x):return x.spent()+bill(s,t,x.live.current)
def advance(s,t,x,n):return replace(x,live=R.prefix(s,t,x.live,n))
def finish(s,t,x):return advance(s,t,x,x.live.current.reserve)

@dataclass(frozen=True)
class Transition:
    before:A.Session
    action:tuple


def perform(s,t,x):
    b=x.before;op,*args=x.action
    if op=='advance': return advance(s,t,b,*args),(0,0,0,0)
    if op=='evidence':
        base,=args;return A.record(b,base),(0,base+1,0,0)
    o,base=args;v,after=A.attempt(b,o,base)
    g=objective(s,t,b)-objective(s,t,after) if v=='accepted' else 0
    h=base+1 if v in ('rejectGain','rejectLiquidity') else 0
    if v=='accepted':assert g>=1
    return after,(g,h,int(v!='deferred'),int(v=='accepted'))


def valid_trace(s,t,x,ts,end):
    for tr in ts:
        if tr.before!=x:return False
        x,_=perform(s,t,tr)
    return x==end


def preserve(a,b):
    assert a.funds()==b.funds()
    assert b.live.current.reserve<=b.live.balance
    assert a.live.current.controller.fees==b.live.current.controller.fees
    assert a.live.history==b.live.history
    assert b.live.current.certs[:len(a.live.current.certs)]==a.live.current.certs
    assert not a.live.current.receipts or b.live.current.receipts[-len(a.live.current.receipts):]==a.live.current.receipts
    assert not a.journal or b.journal[-len(a.journal):]==a.journal


def build(s,t,old,new,migration):
    candidate=R.rebase(s,t,old,new)
    a,b=bill(s,t,old),bill(s,t,candidate)
    return A.Offer(old,candidate,migration,((a,b),(a+100,b+100)),'offline joint enclosure')


def append(s,t,ts,x,action,c):
    tr=Transition(x,action);y,d=perform(s,t,tr);preserve(x,y)
    g,h,p,a=d
    assert objective(s,t,y)+g==objective(s,t,x)+h
    assert x.spent()+p<=y.spent() and a<=g
    ts.append(tr);c['transition_laws']+=1;c[action[0]]+=1
    if action[0]=='attempt':c['accepted']+=a;c['paid_attempts']+=p
    return y,d


def check_chain(s,t,initial,ts,end,ref,c):
    assert valid_trace(s,t,initial,ts,end)
    # Sum statistics of actual operations, not guessed endpoint differences.
    ds=[perform(s,t,tr)[1] for tr in ts]
    g,h,p,a=map(sum,zip(*ds)) if ds else (0,0,0,0)
    assert objective(s,t,end)+g==objective(s,t,initial)+h
    preserve(initial,end)
    assert p+end.live.balance<=initial.live.balance
    assert a<=g<=objective(s,t,initial)+h
    done=finish(s,t,end);baseline=finish(s,t,initial)
    assert done.spent()==objective(s,t,end)
    assert baseline.spent()==objective(s,t,initial)
    assert (done.spent()<baseline.spent())==(h<g)
    assert {(p,a):w for p,a,w in done.live.current.certs}==ref
    assert len(done.live.current.certs)==len(ref)
    preserve(initial,done);c['connected_chains']+=1;c['net_gain_chains']+=int(g>h)
    # Endpoint and predecessor are part of the contract: do not accept a
    # disconnected history just because every listed action is individually legal.
    if end!=initial:
        assert not valid_trace(s,t,end,ts,end);c['disconnected_rejections']+=1
        assert not valid_trace(s,t,initial,ts,initial);c['forged_end_rejections']+=1
    return g,h,done.spent()


def main():
    c=Counter();generic_checks(c);rng=Random(291130)
    controllers=[R.Controller((),(0,0,0)),R.Controller((('depth',0,()),),(0,0,0)),R.Controller((('read',0,()),),(0,0,0)),R.Controller((('noop',3,()),('noop',3,())),(0,0,0))]
    models=[(task(1,2,1,depth=1),task(1,2,1,depth=0))]
    # Small explicit suite, not a duplicate of the expensive parent stand.
    models += [(task(2,2,1,mat[:2]),task(2,2,1,mat[2:])) for mat in list(product(product((0,1),repeat=2),repeat=4))[::8]]
    models += [(rand_task(rng,rng.randrange(3),rng.randrange(3),1),rand_task(rng,rng.randrange(3),rng.randrange(3),1)) for _ in range(16)]
    for s,t in models:
        ref=brute(s,t);c['task_pairs']+=1
        for extra in (0,5,100):
            cont=R.root(s,t,rng.choice(controllers));initial=A.Session(R.Live(cont,cont.reserve+extra));x=initial;ts=[]
            for j in range(6):
                if j%3==0:act=('advance',rng.randrange(4))
                elif j%3==1 and x.live.balance>=x.live.current.reserve+1:act=('evidence',0)
                else:act=('attempt',build(s,t,x.live.current,rng.choice(controllers),1),rng.randrange(3))
                x,_=append(s,t,ts,x,act,c)
            check_chain(s,t,initial,ts,x,ref,c)
    # Same closed witness as T29a/b, with fixed base and rule prices.
    s,t=models[0];ref=brute(s,t);old=replace(R.root(s,t,controllers[0]),reserve=100);new=replace(R.rebase(s,t,old,controllers[1]),reserve=100)
    o=A.Offer(old,new,1,((7,1),(70,64)),'closed paired witness')
    initial=A.Session(R.Live(old,110));assert objective(s,t,initial)==7
    x=initial;ts=[]
    for act in (('evidence',0),('attempt',o,0),('advance',100)):
        x,_=append(s,t,ts,x,act,c)
    assert check_chain(s,t,initial,ts,x,ref,c)==(4,1,4)
    print('Positive mixed trace: baseline 7, accepted gain 4, evidence overhead 1, final bill 4.')
    x=initial;ts=[]
    for act in (('attempt',o,4),('attempt',o,0)):
        x,_=append(s,t,ts,x,act,c)
    assert check_chain(s,t,initial,ts,x,ref,c)==(4,5,8)
    print('Negative mixed trace: baseline 7, accepted gain 4, rejected check 5, final bill 8.')
    for k,v in sorted(c.items()):print(f'{k}: {v}')
    print('PASS deterministic prefix bills, connected finite histories, exact cumulative ledger, provenance and root completion. Not Lean execution.')

if __name__=='__main__':main()
