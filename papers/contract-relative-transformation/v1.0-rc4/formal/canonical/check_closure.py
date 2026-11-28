#!/usr/bin/env python3
"""T31 independent finite reference model. Not Lean execution.
The fixed provider is used throughout each schedule. Bounds are computed
OFFLINE on the declared fixture, not by the live numerical gate. The schedule
itself is an explicit finite input, not a synthesized scheduler.
"""
from collections import Counter
from dataclasses import dataclass, replace
from itertools import product
from random import Random
import check_policy as P
import check_admission as A
import check_replacement as R
import check_trace as T
from check_pruning import task, rand_task, brute

@dataclass(frozen=True)
class Transition:
    before: P.Machine
    after: P.Machine
    base: int
    status: str
    provider_id: int


def execute_plan(m, base, factory, provider_id):
    nxt,status=P.upgrade(m,base,lambda:factory(m))
    return Transition(m,nxt,base,status,provider_id)


def connected(initial, trace, end, provider_id):
    m=initial
    for step in trace:
        if step.before != m or step.provider_id != provider_id:
            return False
        m=step.after
    return m==end


def run(s,t,initial,provider,plans,c):
    m=initial; trace=[]; provider_id=id(provider)
    for base,candidate in plans:
        old_bill=P.allin(s,t,provider,m.active,m.s)
        # Independent exact bounds for the closed test fixture. Compute before
        # the online gate and mark the work as offline; no timing claim.
        affordable=P.affordable(m.s,base)
        if affordable:
            prepaid=A.record(m.s,base)
            new_bill=P.allin(s,t,provider,candidate,prepaid)
            proposed=P.Proposal(candidate,old_bill,new_bill)
        else:
            proposed=None
        calls=[]
        def factory(actual):
            assert affordable and actual==m and proposed is not None
            calls.append(1)
            return proposed
        tr=execute_plan(m,base,factory,provider_id)
        n,v=tr.after,tr.status
        assert len(calls)==int(affordable)
        assert v==('deferred' if not affordable else ('accepted' if new_bill<old_bill else 'rejected'))
        T.preserve(m.s,n.s)
        assert n.s.live.current==m.s.live.current
        debit=0 if v=='deferred' else base+1
        assert n.s.spent()==m.s.spent()+debit
        assert n.s.live.balance==m.s.live.balance-debit
        assert len(n.history)==len(m.history)+int(v!='deferred')
        assert not m.history or n.history[-len(m.history):]==m.history
        if v=='deferred':assert n is m
        elif v=='accepted':assert P.allin(s,t,provider,n.active,n.s)==new_bill<old_bill
        else:assert n.active==m.active
        trace.append(tr);m=n
        c['transition_laws']+=1;c[v]+=1
    assert len(trace)==len(plans)
    assert connected(initial,trace,m,provider_id)
    T.preserve(initial.s,m.s)
    paid=sum(tr.status!='deferred' for tr in trace)
    accepted=sum(tr.status=='accepted' for tr in trace)
    fees=sum(tr.base+1 for tr in trace if tr.status!='deferred')
    assert accepted<=paid<=fees
    assert m.s.spent()==initial.s.spent()+fees
    assert paid+m.s.live.balance<=initial.s.live.balance
    assert len(m.history)==len(initial.history)+paid
    assert not initial.history or m.history[-len(initial.history):]==initial.history
    if all(tr.status!='rejected' for tr in trace):
        assert P.allin(s,t,provider,m.active,m.s)+accepted<=P.allin(s,t,provider,initial.active,initial.s)
        c['no_rejection_gain_laws']+=1
    if trace:
        assert not connected(initial,[replace(trace[0],provider_id=-1)]+trace[1:],m,provider_id)
        c['provider_mismatch_rejections']+=1
    if m!=initial:
        assert not connected(m,trace,m,provider_id)
        assert not connected(initial,trace,initial,provider_id)
        c['forged_trace_rejections']+=2
    # Interpret the final policy and retain its actual events. All quote fees
    # are checked against the authoritative ledger; prepared offers survive
    # even when the subsequent root attempt is deferred.
    out,events,v=P.interpret(provider,m.active,m.s)
    T.preserve(m.s,out)
    expected=0;last=None
    for ev in events:
        if ev[0]=='observed':expected+=ev[2]
        elif ev[0]=='prepared':expected+=ev[1];last=ev[2]
        else:
            assert last is not None
            expected+=A.debit(provider.check_base+1,last.migration,ev[1])
    assert out.spent()==m.s.spent()+expected
    full=T.finish(s,t,out)
    T.preserve(initial.s,full)
    assert full.spent()==P.allin(s,t,provider,m.active,m.s)
    assert {(p,a):h for p,a,h in full.live.current.certs}==brute(s,t)
    assert len(full.live.current.certs)==len(brute(s,t))
    history=tuple(('upgrade',ev) for ev in reversed(m.history))+tuple(('episode',ev) for ev in events)
    assert history[len(m.history):]==tuple(('episode',ev) for ev in events)
    c['closed_runs']+=1;c['episode_events']+=len(events);c['root_'+v]+=1
    return full,trace,history


def qchain(n):
    t=P.ATTEMPT
    for _ in range(n):t=('obs',0,P.KEEP,t)
    return t


def main():
    c=Counter();rng=Random(311128)
    controllers=[R.Controller((),(0,0,0)),R.Controller((('depth',0,()),),(0,0,0)),R.Controller((('read',0,()),),(0,0,0))]
    models=[(task(2,2,1,mat[:2]),task(2,2,1,mat[2:])) for mat in list(product(product((0,1),repeat=2),repeat=4))[::16]]
    models += [(rand_task(rng,rng.randrange(3),rng.randrange(3),1),rand_task(rng,rng.randrange(3),rng.randrange(3),1)) for _ in range(8)]
    policies=(P.KEEP,P.ATTEMPT,P.QUERY,qchain(2),qchain(4))
    for s,t in models:
        c['task_pairs']+=1
        root=R.root(s,t,rng.choice(controllers));initial=A.Session(R.Live(root,root.reserve))
        for prefix in (0,3):
            partial=T.advance(s,t,initial,prefix);old=partial.live.current
            o=P.offer(s,t,old,rng.choice(controllers));p=P.Provider(lambda:bool(old.jobs),lambda:o)
            for extra in (0,1,3,8,20):
                frame=replace(partial,live=replace(partial.live,balance=old.reserve+extra))
                for n in (0,1,3,6):
                    m=P.Machine(frame,rng.choice(policies))
                    plans=tuple((rng.randrange(3),rng.choice(policies)) for _ in range(n))
                    run(s,t,m,p,plans,c)
    # Original T30 fixture, now closed through two actual upgrade attempts.
    s=task(1,2,1,depth=1);t=task(1,2,1,depth=0)
    old=replace(R.root(s,t,controllers[0]),reserve=100);new=replace(R.rebase(s,t,old,controllers[1]),reserve=100)
    o=A.Offer(old,new,1,((7,1),),'fixed proof fixture');p=P.Provider(lambda:bool(old.jobs),lambda:o)
    x=A.Session(R.Live(old,110));m=P.Machine(x,P.KEEP)
    final,ts,_=run(s,t,m,p,((0,P.QUERY),),c)
    assert final.spent()==6 and ts[0].status=='accepted'
    final,ts,_=run(s,t,m,p,((0,P.QUERY),(0,P.QUERY)),c)
    assert final.spent()==7 and tuple(z.status for z in ts)==('accepted','rejected')
    print('Closed T30 fixture: baseline 7, one accepted upgrade 6, additional paid rejection 7.')
    # Two strict accepted upgrades without new provider or verifier.
    m=P.Machine(x,qchain(4));baseline=P.allin(s,t,p,m.active,m.s)
    final,ts,_=run(s,t,m,p,((0,qchain(2)),(0,P.ATTEMPT)),c)
    assert baseline==8 and final.spent()==6 and all(z.status=='accepted' for z in ts)
    print('Two accepted changes, fixed provider: all-in bill 8 -> 7 -> 6.')
    # The old plan has exactly enough surplus for prep, root check, migration.
    # A rejected upgrade burns one unit; the subsequent root switch is now
    # illiquid. The all-in damage is greater than the fee itself.
    x=A.Session(R.Live(old,103));m=P.Machine(x,P.ATTEMPT)
    before=P.allin(s,t,p,m.active,m.s);final,ts,_=run(s,t,m,p,((0,P.ATTEMPT),),c)
    assert ts[0].status=='rejected' and before==4 and final.spent()==10
    print('Liquidity counterexample: rejected fee 1 changes all-in bill 4 -> 10, not 4 -> 5.')
    # Repeated free deferred requests cannot extend the supplied schedule.
    x=A.Session(R.Live(old,100));m=P.Machine(x,P.QUERY)
    final,ts,_=run(s,t,m,p,((0,P.ATTEMPT),)*12,c)
    assert len(ts)==12 and all(z.status=='deferred' for z in ts)
    print('Twelve free deferred requests: finite schedule consumed, fallback completes.')
    for k,v in sorted(c.items()):print(f'{k}: {v}')
    print('PASS fixed-provider closure, bounded schedules, exact charges, preserved history, terminal completion and economic controls. Not Lean execution.')

if __name__=='__main__':main()
