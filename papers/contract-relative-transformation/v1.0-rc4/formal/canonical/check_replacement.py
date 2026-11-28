#!/usr/bin/env python3
"""Finite reference model of scoped live controller replacement.
Not execution of Lean. The verified T23 Python reference enumerates actual
morphism pairs independently. Exact prospective bills are constructed offline
for the test, NOT treated as free deployment-time evidence.
"""
from dataclasses import dataclass, replace
from itertools import product
from collections import Counter
from random import Random
from check_pruning import task, rand_task, brute, maps
import check_impasse as B

@dataclass(frozen=True)
class Controller:
    rules: tuple
    fees: tuple

@dataclass(frozen=True)
class Continuation:
    controller: Controller
    jobs: tuple
    certs: tuple
    receipts: tuple
    reserve: int

@dataclass(frozen=True)
class Offer:
    old: Continuation
    candidate: Continuation
    migration: int
    lower: int
    upper: int

@dataclass(frozen=True)
class Event:
    offer: Offer
    balance_before: int
    fee: int
    status: str

    def charge(self):
        return self.fee + (self.offer.migration if self.status=='accepted' else 0)

@dataclass(frozen=True)
class Live:
    current: Continuation
    balance: int
    history: tuple=()

    def spent(self):
        return sum(fee for _,fee in self.current.receipts)+sum(e.charge() for e in self.history)

    def funds(self):
        return self.balance+self.spent()


def as_account(c):
    return B.Account(c.jobs,c.certs,c.receipts,c.reserve,0)


def reserve(s,t,c):
    return B.potential(s,t,c.controller.rules,c.controller.fees,as_account(c))


def root(s,t,controller):
    f=B.initial(s,controller.rules)
    c=Continuation(controller,f.jobs,f.certs,f.receipts,0)
    return replace(c,reserve=reserve(s,t,c))


def rebase(s,t,c,new,slack=0):
    jobs=tuple(B.port_job(j[1],j[2],new.rules) if j[0]=='ports' else j for j in c.jobs)
    out=Continuation(new,jobs,c.certs,c.receipts,0)
    return replace(out,reserve=reserve(s,t,out)+slack)


def prefix(s,t,live,n):
    c=live.current; acc=as_account(c)
    assert c.reserve<=live.balance and reserve(s,t,c)<=c.reserve
    for _ in range(n):
        q=B.quote(s,t,c.controller.rules,c.controller.fees,acc)
        if q is None or q[0]>acc.remaining:
            break
        acc=q[1]()
    out=replace(live,current=Continuation(c.controller,acc.jobs,acc.certs,acc.receipts,acc.remaining),
                balance=live.balance-c.reserve+acc.remaining)
    assert reserve(s,t,out.current)<=out.current.reserve<=out.balance
    assert out.funds()==live.funds()
    assert out.spent()==live.spent()+acc.spent
    assert out.history==live.history
    assert out.current.certs[:len(c.certs)]==c.certs
    assert not c.receipts or out.current.receipts[-len(c.receipts):]==c.receipts
    return out


def finish(s,t,live):
    out=prefix(s,t,live,live.current.reserve)
    assert not out.current.jobs
    return out


def remaining_bill(s,t,c):
    live=Live(c,c.reserve)
    return finish(s,t,live).spent()-live.spent()


def build_offer(s,t,old,new,migration,loose=0):
    # OFFLINE validation for the reference test. Do not call these simulations
    # from the runtime gate: their real preparation cost is external evidence.
    candidate=rebase(s,t,old,new,slack=loose)
    oldbill=remaining_bill(s,t,old)
    newbill=remaining_bill(s,t,candidate)
    return Offer(old,candidate,migration,max(0,oldbill-loose),newbill+loose)


def attempt(live,offer,fee):
    assert live.current==offer.old, 'stale evidence'
    assert live.current.controller.fees==offer.candidate.controller.fees, 'base fee mismatch'
    assert fee>0
    if fee+live.current.reserve>live.balance:
        return 'deferred',live
    if fee+offer.migration+offer.candidate.reserve>live.balance:
        status='rejectLiquidity'
    elif fee+offer.migration+offer.upper>=offer.lower:
        status='rejectGain'
    else:
        status='accepted'
    event=Event(offer,live.balance,fee,status)
    return status,Live(offer.candidate if status=='accepted' else live.current,
                       live.balance-event.charge(),(event,)+live.history)


def coverage(c,p,a):
    return any(B.covered(j,p,a) for j in c.jobs)


def assert_rebase(s,t,old,new,counters):
    assert old.certs==new.certs and old.receipts==new.receipts
    assert len(old.jobs)==len(new.jobs)
    for j,k in zip(old.jobs,new.jobs):
        if j[0]=='actions':
            assert j==k
            counters['action_suffix_preserved']+=1
        else:
            assert j[:3]==k[:3]
            counters['port_region_preserved']+=1
    for p in maps(s.q,t.q):
        for a in maps(s.a,t.a):
            assert coverage(old,p,a)==coverage(new,p,a)
            counters['coverage_pairs']+=1


def assert_attempt(s,t,live,offer,fee,counters,ref,old_bill=None):
    status,out=attempt(live,offer,fee)
    expected=(fee+live.current.reserve<=live.balance and
              fee+offer.migration+offer.candidate.reserve<=live.balance and
              fee+offer.migration+offer.upper<offer.lower)
    assert (status=='accepted')==expected
    assert out.current.reserve<=out.balance
    assert out.funds()==live.funds()
    if status=='deferred':
        assert out is live
    else:
        assert out.history[1:]==live.history
        assert out.history[0].status==status
        assert out.history[0].offer==offer
        assert out.history[0].balance_before==live.balance
    charge=0 if status=='deferred' else fee+(offer.migration if expected else 0)
    assert out.spent()==live.spent()+charge and out.balance==live.balance-charge
    if not expected:assert out.current==live.current
    else:
        assert_rebase(s,t,live.current,out.current,counters)
        counters['accepted_with_certificates']+=bool(live.current.certs)
        counters['accepted_with_action_jobs']+=any(j[0]=='actions' for j in live.current.jobs)
    done=finish(s,t,out)
    assert {(p,a):h for p,a,h in done.current.certs}==ref
    assert len(done.current.certs)==len(ref)
    if old_bill is None:old_bill=remaining_bill(s,t,live.current)
    if expected: assert done.spent()<live.spent()+old_bill
    if status in ('rejectGain','rejectLiquidity'):
        assert done.spent()==live.spent()+old_bill+fee
    counters[status]+=1
    counters['attempts']+=1
    counters['completed_after_attempt']+=1
    return out


def main():
    rng=Random(281104)
    counts=Counter()
    controllers=[Controller((),(0,0,0)), Controller((('read',0,()),),(0,0,0)),
      Controller((('price',0,()),),(0,0,0)),Controller((('depth',0,()),),(0,0,0)),
      Controller((('injective',0,()),),(0,0,0)),Controller((('noop',2,()),),(0,0,0))]
    models=[(task(2,2,2,matrices[:2]),task(2,2,2,matrices[2:]))
        for matrices in product(product((0,1),repeat=2),repeat=4)]
    for _ in range(128):
        models.append((rand_task(rng,rng.randrange(3),rng.randrange(3),rng.randrange(1,3)),
                       rand_task(rng,rng.randrange(3),rng.randrange(3),rng.randrange(1,3))))
    models.extend((task(sw,sq,1),task(tw,tq,1)) for sw,tw,sq,tq in product(range(2),repeat=4))
    for s,t in models:
        ref=brute(s,t);counts['task_pairs']+=1
        # Prefix of the actual paid T23 search, including action suffix and
        # previously emitted certificates. Some regions have partly consumed rules.
        old_controller=controllers[rng.randrange(len(controllers))]
        old=root(s,t,old_controller)
        base=Live(old,old.reserve)
        for n in (0,1,3,8,20):
            mid=prefix(s,t,base,n); c=mid.current
            counts['prefixes']+=1
            counts['nonempty_certificate_prefixes']+=bool(c.certs)
            counts['nonempty_action_prefixes']+=any(j[0]=='actions' for j in c.jobs)
            cb=remaining_bill(s,t,c)
            for new in controllers:
                o=build_offer(s,t,c,new,1,loose=counts['prefixes']%2)
                assert_rebase(s,t,c,o.candidate,counts)
                # Check affordability separately at boundary points. Include
                # exact fallback and candidate reserves, and ample surplus.
                fee=1
                cap=max(c.reserve+fee,o.candidate.reserve+o.migration+fee)
                for balance in sorted({c.reserve,c.reserve+fee,max(c.reserve,cap-1),cap}):
                    live=replace(mid,balance=balance)
                    assert_attempt(s,t,live,o,fee,counts,ref,cb)
            # Rebase composition leaves region and certificate semantics intact.
            a=rebase(s,t,c,controllers[1]); b=rebase(s,t,a,controllers[2]); d=rebase(s,t,c,controllers[2])
            assert b==d
            counts['migration_compositions']+=1
    # Positive closed witness corresponding to the Lean source example.
    s=task(1,2,1,depth=1);t=task(1,2,1,depth=0);ref=brute(s,t)
    c=replace(root(s,t,controllers[0]),reserve=100)
    new=replace(rebase(s,t,c,controllers[3]),reserve=100)
    o=Offer(c,new,1,7,1)
    assert remaining_bill(s,t,c)==7 and remaining_bill(s,t,new)==1
    assert attempt(Live(c,100),o,1)[0]=='deferred'
    assert attempt(Live(c,101),o,1)[0]=='rejectLiquidity'
    a=assert_attempt(s,t,Live(c,110),o,1,counts,ref)
    assert a.spent()==2 and finish(s,t,a).spent()==3
    # Repeated replacement under a fixed base tariff and fixed rule fees.
    # Remove redundant expensive no-op tests, then add useful depth pruning.
    noop=controllers[5].rules
    c=root(s,t,Controller(noop*3,(0,0,0))); live=Live(c,c.reserve+1000)
    old_projected=finish(s,t,live).spent()
    for ctrl in (Controller(noop,(0,0,0)),controllers[0],controllers[3]):
        o=build_offer(s,t,live.current,ctrl,1)
        live2=assert_attempt(s,t,live,o,1,counts,ref)
        assert len(live2.history)==len(live.history)+1
        assert finish(s,t,live2).spent()<old_projected
        old_projected=finish(s,t,live2).spent()
        # Previous offer has no authority over the new continuation.
        try:attempt(live2,o,1)
        except AssertionError:counts['stale_offer_rejections']+=1
        else:raise AssertionError('stale offer accepted')
        live=live2
    # A fabricated gain obtained by repricing the base operations is outside the contract.
    bogus=build_offer(s,t,live.current,Controller((),(1,1,1)),0)
    try:attempt(live,bogus,1)
    except AssertionError:counts['repricing_rejections']+=1
    else:raise AssertionError('repriced offer accepted')
    # Even with an unchanged economic bill, a more generous reserve can block
    # a cheaper replacement. Retrying a rejected check consumes the surplus.
    live=Live(c,c.reserve+2)
    o=build_offer(s,t,c,c.controller,0)
    for _ in range(3):
        st,live=attempt(live,o,1)
    assert st=='deferred' and live.balance==c.reserve
    print('PASS actual finite frontier model (not Lean execution).')
    for k,v in sorted(counts.items()):print(f'{k}: {v}')
    print('Closed depth witness: baseline 7, accepted full incremental bill 3, deferred at balance 100, rejected for liquidity at 101.')
    print('PASS repeated replacements, stale evidence, rejected-check charge and fallback reserve protection.')
    print('Prospective cost evidence was prepared offline; no claim of free economic witnesses or physical runtime improvement.')

if __name__=='__main__':main()
