#!/usr/bin/env python3
"""Independent finite reference models, not execution of Lean or timing.
Brute h,p,a enumeration is inherited unchanged from the verified T23 stand.
"""
from itertools import product, combinations
from collections import Counter
from typing import NamedTuple
from random import Random
from check_pruning import task, rand_task, brute, rows, port_ok, loss_ok, rules, maps


def shrink(bad, todo):
    todo=list(todo); kept=[]
    for i,e in enumerate(todo):
        if not bad(kept+todo[i+1:]): kept.insert(0,e)
    return tuple(kept)


def rule_keep(s,t,rho,rule):
    name,cost,core=rule
    return not set(core)<=set(rho) if name=='core' else rules(s,t,rho,name)


def port_job(qs,rho,rs):return ('ports',tuple(qs),tuple(rho),tuple(rs))
def act_job(p,acts):return ('actions',tuple(p),tuple(acts))

class Account(NamedTuple):
    jobs: tuple
    certs: tuple
    receipts: tuple
    remaining: int
    spent: int


def initial(s,policy,budget=0):return Account((port_job(range(s.q),(),policy),),(),(),budget,0)


def quote(s,t,policy,fees,acc):
    if not acc.jobs:return None
    j,*rest=acc.jobs
    def apply(kind,fee,new,emit=()):
        return Account(tuple(new)+tuple(rest),acc.certs+tuple(emit),((kind,fee),)+acc.receipts,acc.remaining-fee,acc.spent+fee)
    if j[0]=='ports':
        _,qs,rho,rs=j
        if rs:
            r,*tail=rs; fee=r[1]+1
            return fee,lambda:apply('rule',fee,(port_job(qs,rho,tail),) if rule_keep(s,t,rho,r) else ())
        if qs:
            fee=fees[0]+1
            return fee,lambda:apply('split',fee,[port_job(qs[1:],((qs[0],v),)+rho,policy) for v in range(t.q)])
        fee=fees[1]+1
        def prepare():
            if set(q for q,v in rho)!=set(range(s.q)):return apply('prepare',fee,())
            p=tuple(next(v for u,v in rho if u==q) for q in range(s.q))
            if s.depth>t.depth or not port_ok(s,t,p) or not all(rows(s,t,rho)):
                return apply('prepare',fee,())
            return apply('prepare',fee,(act_job(p,maps(s.a,t.a)),))
        return fee,prepare
    _,p,acts=j; fee=fees[2]+1
    def action():
        if not acts:return apply('action',fee,())
        a,*tail=acts
        rr=rows(s,t,tuple(enumerate(p)))
        h=tuple(next((y for y in r if loss_ok(s,t,a,x,y)),None) for x,r in enumerate(rr))
        emit=() if None in h else ((p,a,h),)
        return apply('action',fee,(act_job(p,tail),),emit)
    return fee,action


def execute(s,t,policy,fees,acc):
    for _ in range(acc.remaining):
        q=quote(s,t,policy,fees,acc)
        if q is None or q[0]>acc.remaining:break
        acc=q[1]()
    return acc


def topup(a,b):return a._replace(remaining=a.remaining+b)


def potential(s,t,policy,fees,acc):
    rs_cost=lambda rs:sum(r[1]+1 for r in rs)
    port=fees[1]+1+(t.a**s.a+1)*(fees[2]+1)
    vals=[port]
    for _ in range(s.q):vals.append(fees[0]+1+t.q*(rs_cost(policy)+vals[-1]))
    return sum(rs_cost(j[3])+vals[len(j[1])] if j[0]=='ports' else (len(j[2])+1)*(fees[2]+1) for j in acc.jobs)


def covered(j,p,a):
    if j[0]=='actions':return j[1]==p and a in j[2]
    _,qs,rho,_=j
    return all(p[q]==v for q,v in rho) and all(q in qs or (q,p[q]) in rho for q in range(len(p)))


def inv(acc,ref):
    found={(p,a):h for p,a,h in acc.certs}
    assert len(found)==len(acc.certs)
    assert all(ref[k]==v for k,v in found.items())
    assert all(k in found or any(covered(j,*k) for j in acc.jobs) for k in ref)
    assert acc.spent==sum(fee for _,fee in acc.receipts)
    if not acc.jobs:assert found==ref


def main():
    count=Counter()
    # Exact set-cover semantics, including repeated constraints and empty carriers.
    for nw in range(4):
        full=(1<<nw)-1
        for nc in range(5):
            for masks in product(range(1<<nw),repeat=nc):
                def bad(xs):
                    u=0
                    for e in xs:u|=masks[e]
                    return u==full
                rho=tuple(range(nc))
                if not bad(rho):continue
                out=shrink(bad,rho)
                assert set(out)<=set(rho) and bad(out)
                assert all(not bad([v for v in out if v!=e]) for e in out)
                small=min(len(k) for r in range(nc+1) for k in combinations(rho,r) if bad(k))
                count['cover_cores']+=1;count['irreducible_not_minimum']+=len(out)>small
                if rho:
                    duplicate=rho+rho[:1]
                    d=shrink(bad,duplicate)
                    assert bad(d) and all(not bad([v for v in d if v!=e]) for e in d)
                    count['duplicate_cores']+=1
    rng=Random(240023)
    models=[]
    for matrices in product(product((0,1),repeat=2),repeat=4):
        models.append((task(2,2,2,matrices[:2]),task(2,2,2,matrices[2:])))
    for _ in range(256):
        models.append((rand_task(rng,rng.randrange(3),rng.randrange(3),rng.randrange(1,3)),rand_task(rng,rng.randrange(3),rng.randrange(3),rng.randrange(1,3))))
    for s,t in models:
        ref=brute(s,t); count['task_pairs']+=1
        # Learn from actual read-obstructed prefixes, then compile to subset checks.
        cores=[]
        for n in range(s.q+1):
            for targets in maps(n,t.q):
                rho=tuple(enumerate(targets))
                rr=rows(s,t,rho)
                for x,r in enumerate(rr):
                    if r:continue
                    bad=lambda es:not rows(s,t,es)[x]
                    c=shrink(bad,rho)
                    assert bad(c) and set(c)<=set(rho)
                    assert all(not bad([e for e in c if e!=a]) for a in c)
                    assert not any(all(p[q]==v for q,v in c) for p,a in ref)
                    count['read_cores']+=1
                    if c not in cores:cores.append(c)
                    # Explicit reflection-preserving identity transfer to renamed worlds.
                    if s.w:
                        perm=tuple(reversed(range(s.w)))
                        ss=task(s.w,s.q,s.a,[[r[i] for i in perm] for r in s.read],s.price,[[r[i] for i in perm] for r in s.loss],s.depth)
                        assert not rows(ss,t,c)[x]
                        count['transport_witnesses']+=1
        compiled=tuple(('core',0,c) for c in cores[:4])
        policies=[(),(('read',1,()),('injective',0,()),('price',1,())),compiled]
        for policy in policies:
            fees=(rng.randrange(3),rng.randrange(3),rng.randrange(3))
            start=initial(s,policy); cap=potential(s,t,policy,fees,start)
            full=execute(s,t,policy,fees,topup(start,cap))
            assert not full.jobs; inv(full,ref);count['funded']+=1
            # Exact coverage and decreasing liability at every paid step.
            u=topup(start,cap)
            while u.jobs:
                inv(u,ref); fee,thunk=quote(s,t,policy,fees,u); v=thunk()
                assert potential(s,t,policy,fees,v)+fee<=potential(s,t,policy,fees,u)
                assert v.certs[:len(u.certs)]==u.certs
                assert v.remaining+v.spent==u.remaining+u.spent
                u=v;count['transitions']+=1
            assert u==full
            for b1,b2 in [(0,0),(0,cap),(cap,0),(1,2),(2,1),*( (rng.randrange(cap+1),rng.randrange(cap+1)) for _ in range(5))]:
                x=execute(s,t,policy,fees,topup(start,b1));inv(x,ref)
                y=execute(s,t,policy,fees,topup(x,b2));inv(y,ref)
                z=execute(s,t,policy,fees,topup(start,b1+b2));assert y==z
                assert y.remaining+y.spent==b1+b2
                count['budget_splits']+=1
    # Same semantics, paid checks can make a policy strictly more expensive.
    s=t=task(1,1,1); fees=(0,0,0); p=(('noop',2,()),)
    a=execute(s,t,(),fees,initial(s,(),100));b=execute(s,t,p,fees,initial(s,p,100))
    assert a.certs==b.certs and a.spent<b.spent
    print('PASS independent finite models: '+', '.join(f'{k}={v}' for k,v in sorted(count.items())))
    print(f'PASS no-op cost witness: {a.spent} -> {b.spent}; not Lean execution.')

if __name__=='__main__':main()
