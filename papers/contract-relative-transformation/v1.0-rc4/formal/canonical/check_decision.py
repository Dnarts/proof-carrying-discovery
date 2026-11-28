#!/usr/bin/env python3
"""Independent finite stand for decision-relative evidence. Not Lean execution.
Hypotheses are whole tables/whole vectors of aggregate controller bills, not
underlying task worlds. Enumerate legal trees independently of the Bellman DP.
No external LLM, random validation, wall-clock or free acquisition claims.
"""
from collections import Counter
from functools import lru_cache
from itertools import product, combinations


@lru_cache(None)
def trees(actions, ports, depth):
    base = tuple(('act', a) for a in range(actions))
    if not depth:
        return base
    out = list(base)
    for q in ports:
        sub = trees(actions, tuple(p for p in ports if p != q), depth-1)
        out.extend(('obs', q, l, r) for l in sub for r in sub)
    return tuple(out)


def execute(t, read, fee, h):
    price = 0
    trace = []
    while t[0] == 'obs':
        _, q, l, r = t
        bit = read[q][h]
        price += fee[q]
        trace.append((q, bit, fee[q]))
        t = r if bit else l
    return t[1], price, tuple(trace)


def objective(t, losses, belief, read, fee):
    vals = []
    for h in belief:
        a, paid, _ = execute(t, read, fee, h)
        vals.append(paid+losses[h][a])
    return max(vals, default=0)


def regret_table(cost):
    ref = tuple(min(row) for row in cost)
    return tuple(tuple(v-r for v in row) for row,r in zip(cost,ref)),ref


def solve(loss, belief, read, fee, ports, depth):
    """Direct recurrence over explicit information sets. Value and a tree."""
    na = len(loss[0])
    @lru_cache(None)
    def go(E, Q, d):
        val, tree = min((max((loss[h][a] for h in E), default=0), ('act',a)) for a in range(na))
        if E and d:
            for q in Q:
                rem = tuple(p for p in Q if p != q)
                x, l = go(tuple(h for h in E if not read[q][h]), rem, d-1)
                y, r = go(tuple(h for h in E if read[q][h]), rem, d-1)
                cost = fee[q] + max(x, y)
                if cost < val:
                    val, tree = cost, ('obs',q,l,r)
        return val, tree
    return go(tuple(belief),tuple(ports),depth)


def subsets(xs):
    return (b for k in range(len(xs)+1) for b in combinations(xs,k))


def exhaustive():
    c = Counter()
    # 256 aggregate bill tables; 16 pairs of binary queries; 9 tariffs.
    all_trees = trees(2, (0,1), 2)
    for v in product(range(4), repeat=4):
        cost = (v[:2],v[2:])
        loss, ref = regret_table(cost)
        E = (0,1)
        residual = min(max(loss[h][a] for h in E) for a in range(2))
        for a in range(2):
            for eps in range(4):
                robust = max(loss[h][a] for h in E) <= eps
                pair = all(cost[h][a] <= cost[h][b]+eps for h in E for b in range(2))
                assert robust == pair
                c['pairwise_exact']+=1
        for B in subsets(E):
            R = min(max((loss[h][a] for h in B),default=0) for a in range(2))
            assert R <= residual
            c['belief_monotonicity'] += 1
        for bits in product((0,1),repeat=4):
            read = (bits[:2],bits[2:])
            for fee in product((0,1,3),repeat=2):
                val,t = solve(loss,E,read,fee,(0,1),2)
                stats=[]
                for u in all_trees:
                    obs=reg=run=0
                    for h in E:
                        a,p,trace=execute(u,read,fee,h)
                        assert p==sum(f for _,_,f in trace)
                        assert len({q for q,_,_ in trace})==len(trace)
                        j=cost[h][a]; r=loss[h][a]
                        assert p+j==ref[h]+p+r
                        obs=max(obs,p); reg=max(reg,r); run=max(run,p+r)
                        c['bill_identities']+=1
                    stats.append((obs,reg,run))
                assert val==min(x[2] for x in stats)==objective(t,loss,E,read,fee)
                c['acquisition_models']+=1
                c['legal_tree_comparisons']+=len(stats)
                # The penalty model is independent of the summed-regret objective.
                for eps,budget in ((0,0),(0,1),(0,3),(1,2),(3,0)):
                    caploss=tuple(tuple(0 if r<=eps else budget+1 for r in row) for row in loss)
                    capvalue,u=solve(caploss,E,read,fee,(0,1),2)
                    valid=[o for o,r,_ in stats if r<=eps]
                    want=bool(valid) and min(valid)<=budget
                    assert (capvalue<=budget)==want
                    if want:
                        actual=tuple(execute(u,read,fee,h)[:2] for h in E)
                        assert all(loss[h][a]<=eps and p<=budget for h,(a,p) in zip(E,actual))
                        assert max(p for a,p in actual)==min(valid)==capvalue
                        c['hard_success']+=1
                    c['hard_feasibility_checks']+=1
    return c


def interval_checks():
    # Rectangular interval dominance: every compatible completion is covered.
    c=Counter(); ints=[(lo,hi) for lo in range(3) for hi in range(lo,3)]
    for box in product(ints,repeat=4):
        lo=(tuple(x[0] for x in box[:2]),tuple(x[0] for x in box[2:]))
        hi=(tuple(x[1] for x in box[:2]),tuple(x[1] for x in box[2:]))
        for eps in range(3):
            for a in range(2):
                cert=all(hi[h][a]<=lo[h][1-a]+eps for h in (0,1))
                for z in product(*(range(l,u+1) for l,u in box)):
                    cost=(z[:2],z[2:]); r,_=regret_table(cost)
                    if cert:
                        assert max(row[a] for row in r)<=eps
                        c['interval_certificate_checks']+=1
        # T26 shared endpoints, for all legal underlying T19 trees over two
        # execution worlds and one port. A whole cost table is the hypothesis.
        read=((0,1),); fee=(1,); B=(0,1); ts=trees(2,(0,),1)
        lv=min(objective(t,lo,B,read,fee) for t in ts)
        uv,ut=min((objective(t,hi,B,read,fee),t) for t in ts)
        for z in product(*(range(l,u+1) for l,u in box)):
            cost=(z[:2],z[2:])
            opt=min(objective(t,cost,B,read,fee) for t in ts)
            worst=objective(ut,cost,B,read,fee)
            assert lv<=opt<=worst<=uv and worst-opt<=uv-lv
            # All legal controllers admitted; exact robust residual over the
            # complete rectangle <= T26 gap, checked via their explicit bills.
            c['endpoint_completions']+=1
        bills=[]
        for z in product(*(range(l,u+1) for l,u in box)):
            cost=(z[:2],z[2:])
            bills.append(tuple(objective(t,cost,B,read,fee) for t in ts))
        reg,_=regret_table(tuple(bills))
        residual=min(max(row[i] for row in reg) for i in range(len(ts)))
        assert residual<=uv-lv
        c['endpoint_catalogues']+=1
    return c


def witnesses():
    # Exact same decision across correlated hypotheses; neither exact cost
    # knowledge nor rectangular interval comparison is necessary.
    b=((0,1),(100,101)); r,ref=regret_table(b)
    assert ref==(0,100) and max(x[0] for x in r)==0
    assert max(x[0] for x in b)>min(x[1] for x in b)
    # One charged bit buys exact decision, but may not be worth buying.
    b=((0,8),(8,0)); r,ref=regret_table(b); E=(0,1); read=((0,1),)
    assert solve(r,E,read,(2,),(0,),1)[0]==2
    v,t=solve(r,E,read,(9,),(0,),1); assert v==8 and t[0]=='act'
    caploss=((0,10),(10,0))
    assert solve(caploss,E,read,(9,),(0,),1)[0]==9
    # Zero regret inside an incomplete hypothesis catalogue proves nothing
    # about an actual hypothesis outside it.
    _,t=solve(r,(0,),read,(2,),(0,),1); a,_,_=execute(t,read,(2,),1)
    assert r[1][a]==8
    # Different reference levels: minimax regret need not minimize worst bill.
    b=((0,11),(110,100)); r,_=regret_table(b)
    assert min(range(2),key=lambda a:max(row[a] for row in r))==0
    assert min(range(2),key=lambda a:max(row[a] for row in b))==1
    # XOR synergy: two paid bits, neither alone resolves decision uncertainty.
    h=((0,0),(0,1),(1,0),(1,1))
    b=tuple((0,10) if x==y else (10,0) for x,y in h); r,_=regret_table(b)
    read=tuple(tuple(x[j] for x in h) for j in range(2)); E=tuple(range(4))
    assert solve(r,E,read,(1,1),(0,1),1)[0]==10
    assert solve(r,E,read,(1,1),(0,1),2)[0]==2
    # Empty belief is vacuous, not a deployable decision for any actual world.
    assert solve(r,(),read,(1,1),(0,1),2)[0]==0
    print('Witness common optimum: reference 0..100; decision regret=0; rectangular gap=100.')
    print('Witness one-bit: residual=8, acquisition=2; with price=9 stop for sum objective, query for hard eps=0.')
    print('Witness XOR: depth 1 value=10, depth 2 value=2.')
    print('Witness differing objectives: minimax regret picks A (10), worst bill picks B (100 vs 110).')
    print('PASS excluded-truth and empty-belief negative controls.')


if __name__=='__main__':
    c=exhaustive(); c.update(interval_checks()); witnesses()
    for k,v in sorted(c.items()): print(f'{k}: {v}')
    print('PASS finite robust regret, pairwise dominance, shared endpoints, legal-tree Bellman comparison, hard regret/observation budget, and accounting. Not Lean execution.')
