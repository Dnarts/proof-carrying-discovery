#!/usr/bin/env python3
"""Independent finite cross-check of T23, not Lean execution or timing.
Literal h,p,a enumeration is the reference. Each DFS implements the same
canonical witness convention (first compatible world). Costs are explicit
abstract node/leaf/action/individual rule charges, never wall-clock claims.
"""
from itertools import product
from dataclasses import dataclass
from random import Random
from collections import Counter

@dataclass(frozen=True)
class Task:
    w: int
    q: int
    a: int
    read: tuple
    price: tuple
    loss: tuple
    depth: int


def task(w, q, a, read=None, price=None, loss=None, depth=None):
    return Task(w,q,a,tuple(tuple(row) for row in (read if read is not None else [[0]*w for _ in range(q)])),
                tuple(price if price is not None else [1]*q),
                tuple(tuple(row) for row in (loss if loss is not None else [[0]*w for _ in range(a)])),
                q if depth is None else depth)


def maps(n,m):
    return product(range(m),repeat=n)


def port_ok(s,t,p):
    return len(set(p))==len(p) and all(t.price[v]<=s.price[q] for q,v in enumerate(p))


def rows(s,t,rho):
    return tuple(tuple(y for y in range(s.w) if all(s.read[q][y]==t.read[v][x] for q,v in rho)) for x in range(t.w))


def loss_ok(s,t,a,x,y):
    return all(t.loss[v][x]<=s.loss[u][y] for u,v in enumerate(a))


def brute(s,t):
    out={}
    if s.depth>t.depth:
        return out
    for p in maps(s.q,t.q):
        if not port_ok(s,t,p):
            continue
        for a in maps(s.a,t.a):
            for h in maps(t.w,s.w):
                if all(all(t.read[v][x]==s.read[q][y] for q,v in enumerate(p)) and loss_ok(s,t,a,x,y) for x,y in enumerate(h)):
                    out[p,a]=h
                    break
    return out


def rules(s,t,rho,name):
    if name=='noop': return True
    if name=='depth': return s.depth<=t.depth
    if name=='price': return all(t.price[v]<=s.price[q] for q,v in rho)
    if name=='injective': return len({v for _,v in rho})==len(rho)
    if name=='read': return all(rows(s,t,rho))
    raise ValueError(name)


def dfs(s,t,policy,reference):
    out={}; stats=Counter(); rejected=[]
    def go(rho):
        stats['nodes']+=1
        for name in policy:
            stats['rule:'+name]+=1
            if not rules(s,t,rho,name):
                stats['rejected']+=1
                if len(rho)<s.q: stats['internal_rejected']+=1
                rejected.append(rho)
                return
        if len(rho)<s.q:
            for v in range(t.q):
                go(rho+((len(rho),v),))
            return
        stats['leaves']+=1
        p=tuple(v for _,v in rho)
        if not (s.depth<=t.depth and port_ok(s,t,p)):
            return
        rr=rows(s,t,rho)
        if not all(rr): return
        for a in maps(s.a,t.a):
            stats['actions']+=1
            h=tuple(next((y for y in r if loss_ok(s,t,a,x,y)),None) for x,r in enumerate(rr))
            if None not in h:
                assert (p,a) not in out
                out[p,a]=h
    go(())
    assert out==reference, (s,t,policy,out,reference)
    for rho in rejected:
        assert not any(all(p[q]==v for q,v in rho) for p,a in reference), (s,t,rho,policy)
    return stats


def bill(stats, rule_fees):
    return 2*stats['nodes']+3*stats['leaves']+4*stats['actions']+sum(stats['rule:'+r]*c for r,c in rule_fees.items())


def rand_task(rng,w,q,a):
    return task(w,q,a,[[rng.randrange(2) for _ in range(w)] for _ in range(q)],
                [rng.randrange(3) for _ in range(q)],[[rng.randrange(3) for _ in range(w)] for _ in range(a)],rng.randrange(4))


def main():
    mono=0
    for s0,s1,t0,t1 in product(product((0,1),repeat=2),repeat=4):
        s,t=task(2,2,1,[s0,s1]),task(2,2,1,[t0,t1])
        for v0,v1 in product(range(2),repeat=2):
            before=rows(s,t,((0,v0),)); after=rows(s,t,((0,v0),(1,v1)))
            for r1,r2 in zip(before,after):
                assert set(r2)<=set(r1); mono+=1
    econ=0
    for b in range(15):
        for p in range(b+1):
            for c,f in product(range(5),repeat=2):
                assert (p*(c+f)<b*c)==(p*f<(b-p)*c); econ+=1

    order_cases=0
    for n in range(10):
        for a,b in product(range(n+1),repeat=2):
            for ca,cb in product(range(5),repeat=2):
                assert (n*ca+a*cb < n*cb+b*ca)==((n-b)*ca<(n-a)*cb)
                order_cases+=1

    policies=[(),('read',),('price',),('injective',),('depth',),('depth','price','injective','read'),('read','injective','price','depth'),('noop',)]
    total=Counter(); aggregate={p:Counter() for p in policies}; fee={r:1 for p in policies for r in p}
    def check(s,t):
        ref=brute(s,t); total['pairs']+=1; total['canonical_pairs']+=len(ref)
        base=dfs(s,t,(),ref); aggregate[()]+=base
        for policy in policies[1:]:
            st=dfs(s,t,policy,ref); aggregate[policy]+=st
            assert st['nodes']<=base['nodes'] and st['actions']<=base['actions']
            total['policy_checks']+=1; total['rejected_regions']+=st['rejected']
            if policy==policies[5]:
                total['cheaper']+=bill(st,fee)<bill(base,fee)
                total['more_expensive']+=bill(st,fee)>bill(base,fee)
                total['tied']+=bill(st,fee)==bill(base,fee)
    # 256 read matrices x 16 price assignments, exact 2-world/2-port carriers.
    for s0,s1,t0,t1 in product(product((0,1),repeat=2),repeat=4):
        for sp0,sp1,tp0,tp1 in product(range(2),repeat=4):
            check(task(2,2,2,[s0,s1],[sp0,sp1],[[0,1],[1,0]]),task(2,2,2,[t0,t1],[tp0,tp1],[[0,1],[1,0]]))
    rng=Random(20261127)
    for _ in range(4096):
        check(rand_task(rng,rng.randrange(3),rng.randrange(4),rng.randrange(1,3)),rand_task(rng,rng.randrange(3),rng.randrange(4),rng.randrange(1,3)))
    # Explicit positive controls for empty carriers, and fully valid renamed cases.
    for sw,tw,sq,tq in product(range(3),repeat=4): check(task(sw,sq,1),task(tw,tq,1))
    for _ in range(256):
        s=rand_task(rng,2,3,2); p=(2,0,1); h=(1,0); a=(1,0)
        tr=[None]*3; prices=[None]*3; losses=[None]*2
        for q,v in enumerate(p): tr[v]=[s.read[q][y] for y in h]; prices[v]=s.price[q]
        for u,v in enumerate(a): losses[v]=[s.loss[u][y] for y in h]
        t=task(2,3,2,tr,prices,losses,s.depth)
        assert (p,a) in brute(s,t)
        check(s,t)
    # Profitable real prune, and real no-op rule with identical results but higher bill.
    s=task(2,3,1,[[0,0]]*3); t=task(2,3,1,[[0,1]]*3)
    ref=brute(s,t); assert not ref
    b=dfs(s,t,(),ref); r=dfs(s,t,('read',),ref)
    assert b['nodes']==40 and r['nodes']==4 and bill(r,fee)<bill(b,fee)
    u=task(1,1,1); ref=brute(u,u); assert ref
    b2=dfs(u,u,(),ref); n=dfs(u,u,('noop',),ref)
    assert b2['nodes']==n['nodes'] and bill(b2,fee)<bill(n,fee)
    # Reversing rule order preserves results but changes charged rule evaluations.
    s=task(2,3,1,[[0,0]]*3,[0,0,0]); t=task(2,3,1,[[0,1]]*3,[1,1,1])
    ref=brute(s,t); a1=dfs(s,t,('price','read'),ref); a2=dfs(s,t,('read','price'),ref)
    # Non-unit rule fees distinguish orders; same number of visited nodes.
    assert a1['nodes']==a2['nodes']
    assert bill(a1,{'price':1,'read':4}) < bill(a2,{'price':1,'read':4})
    print(f'PASS monotonicity={mono}; arithmetic={econ}; order={order_cases}; independent literal h,p,a enumeration.')
    for k,v in sorted(total.items()): print(f'{k}: {v}')
    for p,st in aggregate.items():
        print(f'policy={"+".join(p) or "none"}: nodes={st["nodes"]}, leaves={st["leaves"]}, actions={st["actions"]}, rule_calls={sum(st["rule:"+r] for r in p)}, internal_rejected={st["internal_rejected"]}, abstract_cost={bill(st,fee)}')
    print(f'Witness early prune: nodes {b["nodes"]}->{r["nodes"]}; cost {bill(b,fee)}->{bill(r,fee)}.')
    print(f'Witness noop: nodes {b2["nodes"]}->{n["nodes"]}; cost {bill(b2,fee)}->{bill(n,fee)}.')
    print(f'Witness order: abstract cost {bill(a1,{"price":1,"read":4})} vs {bill(a2,{"price":1,"read":4})}.')
    print('PASS exact canonical certificates, scoped rejections, empty/asymmetric domains, short-circuit accounting; Lean kernel NOT executed.')

if __name__=='__main__': main()
