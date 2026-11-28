#!/usr/bin/env python3
"""Independent finite implementation, not execution of the Lean sources.
Tests paid endogenous compilation, semantic subsumption, coverage, and resume.
"""
from itertools import product
from typing import NamedTuple
from collections import Counter
from random import Random
from check_pruning import task, rand_task, brute, rows
from check_impasse import shrink, initial as base_initial, quote as base_quote, covered

class State(NamedTuple):
    frontier: object
    library: tuple
    history: tuple
    pending: object
    stage: str
    feesPaid: tuple

class Account(NamedTuple):
    state: State
    remaining: int
    spent: int

class Fees(NamedTuple):
    base: tuple = (1,1,1)
    lookup: int = 0
    perCore: int = 1
    probe: int = 9
    compile: int = 10


def initial(s, base=()):
    return Account(State(base_initial(s,base),(),(),None,'lookup',()),0,0)


def insert(k, lib):
    if any(set(old[1]) <= set(k[1]) for old in lib):
        return lib
    return (k,) + tuple(old for old in lib if not set(k[1]) <= set(old[1]))


def topup(a,b):return a._replace(remaining=a.remaining+b)


def quote(s,t,base,fees,st):
    # Returns a quoted fee and deferred transition. No hidden row tests in quote.
    f=st.frontier
    if st.pending is not None:
        def learn():
            x,rho=st.pending
            reduced=(x,shrink(lambda r:not rows(s,t,r)[x],rho))
            assert not rows(s,t,reduced[1])[x]
            return st._replace(library=insert(reduced,st.library),history=((st.pending,reduced),)+st.history,pending=None,stage='lookup')
        fee=fees.compile+1; kind='compile'; transition=learn
    elif not f.jobs:return None
    else:
        j,*rest=f.jobs
        if j[0]=='ports' and not j[3] and st.stage=='lookup':
            rho=j[2]
            def lookup():
                if any(set(k[1])<=set(rho) for k in st.library):
                    return st._replace(frontier=f._replace(jobs=tuple(rest)),stage='lookup')
                return st._replace(stage='probe')
            fee=fees.lookup+len(st.library)*fees.perCore+1; kind='lookup'; transition=lookup
        elif j[0]=='ports' and not j[3] and st.stage=='probe':
            rho=j[2]
            def probe():
                x=next((i for i,r in enumerate(rows(s,t,rho)) if not r),None)
                if x is None:return st._replace(stage='advance')
                return st._replace(frontier=f._replace(jobs=tuple(rest)),pending=(x,rho),stage='lookup')
            fee=fees.probe+1; kind='probe'; transition=probe
        else:
            fee,step=base_quote(s,t,base,fees.base,f)
            # The base account fields are not used to decide affordability here.
            # Reset them: the outer account is the only budget authority.
            def advance():
                nf=step()._replace(remaining=0,spent=0)
                return st._replace(frontier=nf,stage='lookup')
            kind='base'; transition=advance
    def paid():
        return transition()._replace(feesPaid=((kind,fee),)+st.feesPaid)
    return fee,paid


def run(s,t,base,fees,a, fuel=None, inv=None):
    for _ in range(a.remaining if fuel is None else fuel):
        q=quote(s,t,base,fees,a.state)
        if q is None or q[0]>a.remaining: break
        old=a
        a=Account(q[1](), a.remaining-q[0],a.spent+q[0])
        if inv is not None: inv(old,a)
    return a


def full_bound(s,t,base,fees):
    # Specification upper bound, not computed by quote/run.
    # N full prefix-tree nodes, at most one compilation per port node.
    n=sum(t.q**d for d in range(s.q+1))
    rules=sum(r[1]+1 for r in base)
    look=fees.lookup+n*fees.perCore+1
    leaf=t.q**s.q
    return n*(rules+look+fees.probe+1+fees.compile+1+max(fees.base[:2])+1)+leaf*(t.a**s.a+1)*(fees.base[2]+1)


def rejected(lib,rho):return any(set(k[1])<=set(rho) for k in lib)


def main():
    c=Counter()
    # Every possible 3-region predicate is not needed: core inclusion semantics
    # is exhaustively checked over a 3-element constraint universe instead.
    universe=tuple(range(3)); cores=[(0,tuple(e for e in universe if mask>>e&1)) for mask in range(8)]
    for n in range(4):
        for lib in product(cores,repeat=n):
            for k in cores:
                out=insert(k,lib)
                for _,rho in cores:
                    assert rejected(out,rho)==(rejected(lib,rho) or set(k[1])<=set(rho))
                    c['subsumption_equivalence']+=1
    # Generic resume, including loops: deterministic arbitrary positive-fee
    # transition tables need not have a decreasing measure.
    def generic_run(table,a,fuel=None):
        st,bal,spent,hist=a
        for _ in range(bal if fuel is None else fuel):
            q=table[st]
            if q is None or q[0]>bal:break
            fee,nxt=q; hist=hist+((st,nxt,fee),); st=nxt; bal-=fee; spent+=fee
        return st,bal,spent,hist
    def gtop(a,b):return (a[0],a[1]+b,a[2],a[3])
    options=[None,*product(range(1,4),range(2))]
    for table in product(options,repeat=2):
        for st,b0,b1,b2 in product(range(2),range(3),range(6),range(6)):
            a=(st,b0,4,())
            assert generic_run(table,gtop(a,b1+b2))==generic_run(table,gtop(generic_run(table,gtop(a,b1)),b2))
            c['generic_resume']+=1
    # Counterexample to budget-sensitive scheduling.
    def budget_sensitive(b,state='root'):
        if state!='root' or not b:return state,b
        return ('expensive',b-2) if b>=2 else ('cheap',b-1)
    assert budget_sensitive(2)[0]=='expensive'
    st,r=budget_sensitive(1); assert budget_sensitive(r+1,st)[0]=='cheap'

    models=[]
    for matrices in product(product((0,1),repeat=2),repeat=4):
        models.append((task(2,2,2,matrices[:2]),task(2,2,2,matrices[2:])))
    rng=Random(2407)
    for _ in range(256):
        models.append((rand_task(rng,rng.randrange(3),rng.randrange(4),rng.randrange(1,3)),rand_task(rng,rng.randrange(3),rng.randrange(4),rng.randrange(1,3))))
    # Seed cases where an earlier learned core matches a previously queued region.
    models += [(task(2,3,1,[[0,1],[0,0],[1,0]]),task(2,3,1,[[0,1],[0,0],[0,1]])),(task(0,0,1),task(1,0,1)),(task(0,0,1),task(0,0,1))]
    fees=Fees()
    for s,t in models:
        ref=brute(s,t); base=()
        bound=full_bound(s,t,base,fees)
        def check(old,a):
            st=a.state; f=st.frontier
            got={(p,ac):h for p,ac,h in f.certs}
            assert len(got)==len(f.certs) and all(ref[k]==v for k,v in got.items())
            assert all(k in got or any(covered(j,*k) for j in f.jobs) for k in ref)
            assert a.remaining+a.spent==old.remaining+old.spent
            assert a.spent==sum(v for _,v in st.feesPaid)
            assert len(st.feesPaid)==len(old.state.feesPaid)+1
            assert f.certs[:len(old.state.frontier.certs)]==old.state.frontier.certs
            assert all(not rows(s,t,k[1])[k[0]] for k in st.library)
            assert all(i==j or not set(k[1])<=set(l[1]) for i,k in enumerate(st.library) for j,l in enumerate(st.library))
            assert len(st.history)>=len(old.state.history)
            for raw,k in st.history:
                assert raw[0]==k[0] and set(k[1])<=set(raw[1]) and not rows(s,t,k[1])[k[0]]
                assert all(rows(s,t,tuple(v for v in k[1] if v!=e))[k[0]] for e in k[1])
            c['paid_transitions']+=1
            if st.feesPaid[0][0]=='lookup' and len(f.jobs)<len(old.state.frontier.jobs): c['live_cache_hits']+=1
            if st.feesPaid[0][0]=='compile':c['compiled_events']+=1
        a=run(s,t,base,fees,topup(initial(s,base),bound),inv=check)
        assert not a.state.frontier.jobs and a.state.pending is None
        assert {(p,ac):h for p,ac,h in a.state.frontier.certs}==ref
        c['funded_complete']+=1
        # Generic equality of the entire account, including active and historical
        # core records and a pending uncompiled obstruction.
        for b1,b2 in [(0,0),(1,2),(4,7),(13,19),(bound//3,bound-bound//3),(bound,7)]:
            a0=initial(s,base)
            left=run(s,t,base,fees,topup(a0,b1+b2))
            mid=run(s,t,base,fees,topup(a0,b1))
            right=run(s,t,base,fees,topup(mid,b2))
            assert left==right
            c['learning_resume']+=1
        # Compare the full learned bill to the unchanged no-prune baseline.
        b=base_initial(s,base,bound*2+1)
        while (q:=base_quote(s,t,base,fees.base,b)) is not None:
            assert b.remaining>=q[0]; b=q[1]()
        c['learned_cheaper']+=a.spent<b.spent
        c['learned_costlier']+=a.spent>b.spent
        c['learned_equal']+=a.spent==b.spent
        # Matched read-pruning control: same local compatibility test price,
        # no compilation, no active-core scan. Final T22 guards unchanged.
        read_policy=(('read',fees.probe,None),)
        rb=base_initial(s,read_policy,full_bound(s,t,read_policy,fees)*2+1)
        while (q:=base_quote(s,t,read_policy,fees.base,rb)) is not None:
            assert rb.remaining>=q[0]; rb=q[1]()
        assert {(p,ac):h for p,ac,h in rb.certs}==ref
        c['vs_read_cheaper']+=a.spent<rb.spent
        c['vs_read_costlier']+=a.spent>rb.spent
        c['vs_read_equal']+=a.spent==rb.spent
        c['reference_bill']+=b.spent
        c['read_bill']+=rb.spent
        c['learning_bill']+=a.spent
    for k,v in sorted(c.items()):print(f'{k}: {v}')
    print('PASS: independent finite learning model, subsumption, generic cyclic resume, paid trace, full-budget coverage, budget-sensitive counterexample. Not Lean execution.')

if __name__=='__main__':main()
