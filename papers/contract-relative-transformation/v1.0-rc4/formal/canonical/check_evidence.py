#!/usr/bin/env python3
"""Independent finite reference for partial cost tables and paid evidence.
No Lean execution. All fees are symbolic; acquisition pays the declared cap,
not the (possibly smaller) realized plan bill. Solver fees are explicit.
"""
from itertools import product
from collections import Counter
from dataclasses import dataclass, replace
from check_meta import solve, trees, worst, perform, initial_reserve, Plan, PLANS
from check_pruning import task, brute


def endpoints(table):
    return tuple(tuple(x[0] for x in row) for row in table), tuple(tuple(x[1] for x in row) for row in table)


def assess(table, ws, ports, depth, bits, prices, na, eps):
    lo, hi = endpoints(table)
    ltree = solve(ws, ports, depth, lo, bits, prices, na)
    utree = solve(ws, ports, depth, hi, bits, prices, na)
    lv = worst(ltree, ws, lo, bits, prices)
    uv = worst(utree, ws, hi, bits, prices)
    assert lv <= uv
    return (utree, lv, uv) if uv-lv <= eps else None, lv, uv


def check_rectangles():
    c = Counter()
    ints = [(l,u) for l in range(3) for u in range(l,3)]
    ts = tuple(trees((0,),1,2))
    for bs in product(ints, repeat=4):
        tab = (bs[:2], bs[2:])
        lo,hi = endpoints(tab)
        for b0,b1,price in product((False,True),(False,True),(0,1)):
            bits=((b0,),(b1,)); prices=(price,); ws=(0,1)
            r,lv,uv=assess(tab,ws,(0,),1,bits,prices,2,4)
            assert r is not None
            tree=r[0]
            assert lv==min(worst(t,ws,lo,bits,prices) for t in ts)
            assert uv==min(worst(t,ws,hi,bits,prices) for t in ts)
            c['interval_models']+=1
            for xs in product(*(range(l,u+1) for l,u in bs)):
                true=(xs[:2],xs[2:])
                opt=min(worst(t,ws,true,bits,prices) for t in ts)
                actual=worst(tree,ws,true,bits,prices)
                assert lv<=opt<=actual<=uv and actual-opt<=uv-lv
                c['compatible_completions']+=1
                c['tree_comparisons']+=len(ts)
                for k in range(4):
                    nb=list(bs); nb[k]=(xs[k],xs[k]); nb=tuple(nb)
                    _,nl,nu=assess((nb[:2],nb[2:]),ws,(0,),1,bits,prices,2,4)
                    assert lv<=nl<=nu<=uv and nu-nl<=uv-lv
                    c['refinements']+=1
    # Empty world list: exact and uncertain tables have zero worst loss.
    result, lv, uv = assess((),(),(0,),1,(),(3,),2,0)
    assert result is not None and lv==uv==0
    # Sufficient, NOT necessary: only one action, any uncertainty is harmless.
    r,lv,uv=assess((((0,9),),),(0,),(),0,((),),(),1,0)
    assert r is None and (lv,uv)==(0,9)
    # Zero minimax gap need not imply zero world-by-world oracle regret.
    t=((0,8),(8,0)); exact=tuple(tuple((x,x) for x in row) for row in t)
    r,lv,uv=assess(exact,(0,1),(),0,((),()),(),2,0)
    assert r is not None and lv==uv==8
    assert max(worst(r[0],(w,),t,((),()),())-min(t[w]) for w in (0,1))==8
    return c

@dataclass(frozen=True)
class State:
    table: tuple
    pending: tuple
    receipts: tuple=()
    result: object=None
    remaining: int=0
    spent: int=0


def run(state,bits,prices,depth,eps,provider,extra=0):
    # quote reads only operation metadata, never the acquired result or optimizer.
    s=replace(state,remaining=state.remaining+extra)
    while s.pending and s.result is None:
        op=s.pending[0]; fee=op[-1]
        assert fee>0
        if fee>s.remaining: break
        old=s; result=None; tab=s.table
        if op[0]=='acquire':
            _,w,a,_=op
            evidence=provider(w,a)
            rows=[list(r) for r in s.table]
            l,u=rows[w][a]; el,eu=evidence
            rows[w][a]=(max(l,el),min(u,eu)); assert rows[w][a][0]<=rows[w][a][1]
            tab=tuple(map(tuple,rows)); receipt=('acquired',w,a,el,eu,fee)
        else:
            result,_,_=assess(tab,tuple(range(len(tab))),tuple(range(len(prices))),depth,bits,prices,len(tab[0]),eps)
            receipt=('assessed',fee)
        s=State(tab,old.pending[1:],(receipt,)+old.receipts,result,old.remaining-fee,old.spent+fee)
        assert s.remaining+s.spent==old.remaining+old.spent
        assert s.spent-old.spent==sum(r[-1] for r in s.receipts)-sum(r[-1] for r in old.receipts)
        lo,hi=endpoints(old.table); nl,nu=endpoints(s.table)
        assert all(lo[w][a]<=nl[w][a]<=nu[w][a]<=hi[w][a] for w in range(len(lo)) for a in range(len(lo[w])))
    return s


def check_paid():
    c=Counter()
    for v in product(range(3),repeat=4):
        true=(v[:2],v[2:]); tab=(((0,2),(0,2)),)*2
        def provider(w,a): return (true[w][a],)*2
        ops=(('assess',2),('acquire',0,0,3),('assess',1),('acquire',1,1,2),('assess',2),('acquire',0,1,1),('acquire',1,0,3),('assess',1))
        initial=State(tab,ops); total=sum(o[-1] for o in ops)
        for eps in (0,1):
            def advance(s,b):return run(s,((False,),(True,)),(1,),1,eps,provider,b)
            full=advance(initial,total); assert full.result is not None
            c['funded_success']+=1
            assert full.spent==sum(r[-1] for r in full.receipts)
            for b1,b2 in product(range(8),repeat=2):
                first=advance(initial,b1); final=advance(first,b2)
                assert final==advance(initial,b1+b2)
                c['resume_checks']+=1
    def poison(*_):raise AssertionError('unpaid evidence evaluated')
    initial=State((((0,2),),),(('acquire',0,0,3),))
    assert run(initial,((),),(),0,0,poison,2)==replace(initial,remaining=2)
    # Fully funded schedule need not provide sufficient information.
    s=State((((0,9),),),(('assess',1),))
    r=run(s,((),),(),0,0,poison,1)
    assert not r.pending and r.result is None
    return c


def concrete_t25():
    # The two-task witness in check_meta, same four funded plans and tariff.
    family=(
      (task(2,3,2,((0,0),(1,1),(1,0)),(1,0,1),((2,2),(1,0)),3),
       task(2,3,2,((0,0),(0,0),(0,0)),(0,1,0),((0,2),(2,2)),3)),
      (task(2,3,2,((1,0),(0,1),(1,0)),(1,0,1),((2,1),(0,2)),3),
       task(2,3,2,((0,1),(0,1),(1,0)),(2,2,0),((2,2),(1,1)),3)))
    plans=PLANS[:4]; reserves=[max(initial_reserve(s,t,p) for s,t in family) for p in plans]
    caps=tuple(p.setup+p.learning+r for p,r in zip(plans,reserves))
    tab=tuple(tuple((p.setup,cap) for p,cap in zip(plans,caps)) for _ in family)
    actual_calls=[]
    def provider(w,a):
        s,t=family[w]; val=perform(s,t,plans[a],reserves[a],brute(s,t))
        assert val<=caps[a]; actual_calls.append((w,a,val)); return (val,val)
    # Fixed public schedule, NOT an optimizer with free access to unknown bills.
    # First catalogue row, then read and price cells in second row; assess before tail.
    order=((0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,0),(1,3))
    ops=tuple(('acquire',w,a,caps[a]+1) for w,a in order[:6])+(('assess',3),)+tuple(('acquire',w,a,caps[a]+1) for w,a in order[6:])+(('assess',3),)
    total=sum(o[-1] for o in ops)
    out=run(State(tab,ops),((False,),(True,)),(1,),1,0,provider,total)
    assert out.result is not None and len(actual_calls)==6 and out.result[1:]==(22,22)
    paid_partial=out.spent; acquired=tuple(actual_calls)
    actual_calls.clear()
    fullops=tuple(('acquire',w,a,caps[a]+1) for w,a in order)+(('assess',3),)
    full=run(State(tab,fullops),((False,),(True,)),(1,),1,0,provider,total)
    assert full.result is not None and full.result[1:]==(22,22) and len(actual_calls)==8
    assert paid_partial<full.spent
    assert out.spent==sum(r[-1] for r in out.receipts)
    print('T25 concrete reference: actual acquired cells=',acquired)
    print('T25 reserve caps:',caps)
    print(f'T25 partial acquisition: {len(acquired)}/8 cells, certified value={out.result[1]}, prepaid bill={paid_partial}; full prepaid bill={full.spent}; actual plan bills acquired={sum(v for _,_,v in acquired)} vs {sum(v for _,_,v in actual_calls)}.')
    print('Positive witness is fixed ex-post schedule on known family, not an online schedule-optimality or generalization result.')


if __name__=='__main__':
    c=check_rectangles(); c.update(check_paid())
    for k,v in sorted(c.items()): print(f'{k}: {v}')
    concrete_t25()
    print('PASS interval minimax, monotone refinement, paid schedule, quiescence, split, insufficient evidence and oracle-regret controls. Not Lean execution.')
