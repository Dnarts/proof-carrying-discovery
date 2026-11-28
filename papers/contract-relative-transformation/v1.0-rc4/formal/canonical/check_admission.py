#!/usr/bin/env python3
"""Independent reference tests for T29b, not execution of Lean.
The gate sees numeric inputs only. Prospective bills are obtained offline for
these fixtures; this is not a free evidence-acquisition algorithm.
"""
from collections import Counter
from dataclasses import dataclass, replace
from itertools import product
from random import Random
import check_replacement as R
from check_relative import relative_ok, covered
from check_pruning import task, rand_task, brute


def gate(fee, migration, old_reserve, new_reserve, balance, rows):
    if fee + old_reserve > balance:
        return 'deferred'
    if fee + migration + new_reserve > balance:
        return 'rejectLiquidity'
    if not relative_ok(fee + migration, rows):
        return 'rejectGain'
    return 'accepted'


def debit(fee, migration, v):
    return 0 if v == 'deferred' else fee + (migration if v == 'accepted' else 0)


def check_numeric():
    c = Counter()
    rows_cases = ((), ((0,0),), ((3,0),), ((7,1),(70,64)), ((10,8),(100,98)), ((1,9),(10,0)))
    for H,K,Ro,Rn,B in product(range(5), range(5), range(5), range(5), range(12)):
        for rows in rows_cases:
            v = gate(H,K,Ro,Rn,B,rows)
            f = H+Ro <= B; l = H+K+Rn <= B; g = relative_ok(H+K, rows)
            assert (v=='deferred') == (not f)
            assert (v=='rejectLiquidity') == (f and not l)
            assert (v=='rejectGain') == (f and l and not g)
            assert (v=='accepted') == (f and l and g)
            d = debit(H,K,v)
            assert d <= B
            if Ro <= B:
                assert (Rn if v=='accepted' else Ro) <= B-d
                c['funded_guard_cases'] += 1
            c['numeric_cases'] += 1
    # The raw gate can have a vacuous row pass. A typed offer cannot.
    assert gate(1,0,0,0,1,())=='accepted' and not covered(2,1,())
    class NoRead:
        def __iter__(self): raise AssertionError('unaffordable scan was evaluated')
    assert gate(1,0,10,0,10,NoRead())=='deferred'
    assert gate(1,0,10,20,11,NoRead())=='rejectLiquidity'
    return c

@dataclass(frozen=True)
class Offer:
    old: R.Continuation
    candidate: R.Continuation
    migration: int
    rows: tuple
    label: str

@dataclass(frozen=True)
class Entry:
    kind: str
    fee: int
    offer: object = None
    balance_before: int = 0
    status: str = ''
    label: str = ''
    def charge(self):
        return self.fee if self.kind=='evidence' else debit(self.fee,self.offer.migration,self.status)

@dataclass(frozen=True)
class Session:
    live: R.Live
    journal: tuple = ()
    def spent(self): return self.live.spent()+sum(e.charge() for e in self.journal)
    def funds(self): return self.live.balance+self.spent()


def charge(s,c,e,d):
    assert d==e.charge() and d+c.reserve<=s.live.balance
    return Session(replace(s.live,current=c,balance=s.live.balance-d),(e,)+s.journal)


def apply(s,o,fee,v):
    # Mirror the typed proof boundary with explicit reference assertions.
    assert o.old==s.live.current, 'stale continuation'
    assert o.old.controller.fees==o.candidate.controller.fees, 'tariff mismatch'
    assert o.rows, 'empty proof domain'
    assert v==gate(fee,o.migration,o.old.reserve,o.candidate.reserve,s.live.balance,o.rows), 'forged verdict'
    if v=='deferred':return s
    c=o.candidate if v=='accepted' else o.old
    e=Entry('attempt',fee,o,s.live.balance,v)
    return charge(s,c,e,debit(fee,o.migration,v))


def attempt(s,o,base):
    H=base+1
    v=gate(H,o.migration,o.old.reserve,o.candidate.reserve,s.live.balance,o.rows)
    return v,apply(s,o,H,v)


def record(s,base):return charge(s,s.live.current,Entry('evidence',base+1,label='external charge'),base+1)


def checked(s,t,before,o,base,oldbill,newbill,ref,c):
    v,after=attempt(before,o,base); H=base+1; d=debit(H,o.migration,v)
    assert before.funds()==after.funds()
    assert after.spent()==before.spent()+d
    assert after.live.balance==before.live.balance-d
    assert after.live.current.reserve<=after.live.balance
    assert after.live.history==before.live.history
    assert after.live.current.controller.fees==before.live.current.controller.fees
    assert after.live.current.certs==before.live.current.certs
    assert after.live.current.receipts==before.live.current.receipts
    if v=='deferred': assert after is before
    else:
        assert after.journal[1:]==before.journal
        assert after.journal[0].offer==o and after.journal[0].status==v
        assert after.journal[0].balance_before==before.live.balance
    if v=='accepted':
        assert after.live.current==o.candidate
        assert H+o.migration+newbill<oldbill
        c['correlated_only_accepts']+=int(H+o.migration+max(u for _,u in o.rows)>=min(l for l,_ in o.rows))
        c['accepted_with_previous_certificates']+=bool(before.live.current.certs)
        c['accepted_with_previous_search_receipts']+=bool(before.live.current.receipts)
        R.assert_rebase(s,t,before.live.current,after.live.current,c)
    else:assert after.live.current==before.live.current
    done=R.finish(s,t,after.live)
    actual=done.spent()+sum(e.charge() for e in after.journal)
    assert actual==after.spent()+(newbill if v=='accepted' else oldbill)
    assert {(p,a):h for p,a,h in done.current.certs}==ref
    assert len(done.current.certs)==len(ref)
    assert (actual<before.spent()+oldbill)==(v=='accepted')
    c[v]+=1;c['attempts']+=1;c['completed_after_attempt']+=1
    return after


def check_concrete():
    c=Counter();rng=Random(291129)
    controllers=[R.Controller((),(0,0,0)),R.Controller((('read',0,()),),(0,0,0)),
      R.Controller((('price',0,()),),(0,0,0)),R.Controller((('depth',0,()),),(0,0,0)),
      R.Controller((('injective',0,()),),(0,0,0)),R.Controller((('noop',2,()),),(0,0,0))]
    models=[(task(2,2,2,mat[:2]),task(2,2,2,mat[2:])) for mat in product(product((0,1),repeat=2),repeat=4)]
    models += [(rand_task(rng,rng.randrange(3),rng.randrange(3),rng.randrange(1,3)),rand_task(rng,rng.randrange(3),rng.randrange(3),rng.randrange(1,3))) for _ in range(48)]
    models += [(task(sw,sq,1),task(tw,tq,1)) for sw,tw,sq,tq in product(range(2),repeat=4)]
    for s,t in models:
        ref=brute(s,t);c['task_pairs']+=1
        root=R.root(s,t,rng.choice(controllers))
        for n in (0,3,8):
            mid=R.prefix(s,t,R.Live(root,root.reserve),n); old=mid.current
            a=R.remaining_bill(s,t,old);c['prefixes']+=1
            for ctrl in controllers:
                new=R.rebase(s,t,old,ctrl,slack=n%2);b=R.remaining_bill(s,t,new)
                K=rng.randrange(3);H=1+rng.randrange(2)
                rows=((a,b),(a+100,b+100))
                assert covered(a,b,rows)
                o=Offer(old,new,K,rows,'offline paired fixture')
                cap=max(old.reserve+H,new.reserve+H+K)
                for B in sorted({old.reserve,old.reserve+H,max(old.reserve,cap-1),cap}):
                    state=Session(replace(mid,balance=B+1))
                    # A paid external receipt must survive both admission and rejection.
                    state=record(state,0)
                    assert state.live.balance==B and state.live.current==old
                    assert state.funds()==mid.spent()+B+1
                    c['external_receipts']+=1
                    checked(s,t,state,o,H-1,a,b,ref,c)
    # Same concrete T28 root and T29a correlated enclosure; all four outcomes.
    s=task(1,2,1,depth=1);t=task(1,2,1,depth=0);ref=brute(s,t)
    old=replace(R.root(s,t,controllers[0]),reserve=100)
    new=replace(R.rebase(s,t,old,controllers[3]),reserve=100)
    assert (R.remaining_bill(s,t,old),R.remaining_bill(s,t,new))==(7,1)
    o=Offer(old,new,1,((7,1),(70,64)),'closed witness')
    for B,v in [(100,'deferred'),(101,'rejectLiquidity'),(110,'accepted')]:
        state=Session(R.Live(old,B));assert attempt(state,o,0)[0]==v
        checked(s,t,state,o,0,7,1,ref,c)
    same=Offer(old,old,0,((7,7),),'no gain')
    state=Session(R.Live(old,110));assert attempt(state,same,0)[0]=='rejectGain'
    checked(s,t,state,same,0,7,7,ref,c)
    after=attempt(state,o,0)[1]
    for x,offer,verdict in [(after,o,'accepted'),(state,o,'deferred'),(state,replace(o,rows=()),'accepted')]:
        try: apply(x,offer,1,verdict)
        except AssertionError:c['invalid_application_rejections']+=1
        else:raise AssertionError('invalid application accepted')
    print('Closed witness: baseline 7, accepted total 3, rejected liquidity total 8, deferred total 7.')
    print('Gate does not read rows before liquidity. Empty or stale offers and forged verdicts are rejected at the typed boundary model.')
    return c

if __name__=='__main__':
    c=check_numeric();c.update(check_concrete())
    for k,v in sorted(c.items()):print(f'{k}: {v}')
    print('PASS numeric reflection, exact charges, preserved reserves, receipts and root completion. Not Lean execution.')
