#!/usr/bin/env python3
"""Independent finite reference for T29a, not execution of Lean.
Rows are joint conservative bounds, not independent samples of absolute costs.
The actual bill is used only by the reference tests, never by relative_ok.
"""
from collections import Counter
from dataclasses import replace
from itertools import product
import check_replacement as R
from check_pruning import task, brute


def relative_ok(fee, rows):
    return all(fee + upper < lower for lower, upper in rows)


def covered(old, new, rows):
    return any(lower <= old and new <= upper for lower, upper in rows)


def exhaustive():
    counts = Counter()
    pairs = tuple(product(range(5), repeat=2))
    for n in range(3):
        for rows in product(pairs, repeat=n):
            for fee in range(4):
                ok = relative_ok(fee, rows)
                counts['row_gate_cases'] += 1
                for old, new in pairs:
                    if covered(old, new, rows):
                        counts['covered_actual_pairs'] += 1
                        assert rows
                        if ok:
                            assert fee + new < old
                            counts['sound_pass_cases'] += 1
                    elif not rows:
                        assert ok  # raw scan is vacuous, no covering offer exists
                        counts['empty_cover_rejections'] += 1
                if rows:
                    rect = fee + max(u for _, u in rows) < min(l for l, _ in rows)
                    assert not rect or ok
                    counts['rectangle_implications'] += 1
                    counts['strict_relative_advantage_cases'] += int(ok and not rect)
                for keep in product((False, True), repeat=n):
                    sub = tuple(p for p, k in zip(rows, keep) if k)
                    if ok:
                        assert relative_ok(fee, sub)
                    counts['subset_refinement_cases'] += 1
                    # This checks actual coverage separately from row truth.
                    for old, new in pairs:
                        if covered(old, new, sub):
                            assert covered(old, new, rows)
                            if ok:
                                assert fee + new < old
                            counts['refined_actual_coverage_cases'] += 1
    for lower, upper, fee, migration in product(range(5), repeat=4):
        assert relative_ok(fee + migration, [(lower, upper)]) == (fee + migration + upper < lower)
        counts['absolute_embedding_cases'] += 1
    # Two possible hypotheses, exact benchmark in each, selected controller
    # satisfies epsilon regret, and every incumbent margin is strict.
    # Additional actual-pair inequalities are tested, not assumed equalities.
    for old0, new0, old1, new1 in product(range(5), repeat=4):
        hs = ((old0, new0), (old1, new1))
        refs = tuple(min(old, new) for old, new in hs)
        for eps, fee in product(range(4), repeat=2):
            certificate = all(new <= ref + eps for (_, new), ref in zip(hs, refs))
            rows = tuple((old, ref + eps) for (old, _), ref in zip(hs, refs))
            margin = relative_ok(fee, rows)
            counts['decision_bridge_cases'] += 1
            if not (certificate and margin):
                continue
            counts['decision_bridge_passes'] += 1
            for old, new in pairs:
                if covered(old, new, hs):
                    assert covered(old, new, rows)
                    assert fee + new < old
                    counts['decision_bridge_actual_pairs'] += 1
    assert relative_ok(1, [(10, 8), (100, 98)])
    assert not 1 + 98 < 10
    assert not relative_ok(1, [(10, 10)])
    assert not covered(10, 8, [])
    # A passing row with no actual coverage has no authority to admit.
    assert relative_ok(1, [(100, 1)]) and not covered(2, 9, [(100, 1)])
    return counts


def concrete():
    s = task(1, 2, 1, price=(0,0), depth=1)
    t = task(1, 2, 1, price=(0,0), depth=0)
    old = replace(R.root(s, t, R.Controller((), (0,0,0))), reserve=100)
    new = replace(R.rebase(s, t, old, R.Controller((('depth', 0, ()),), (0,0,0))), reserve=100)
    before, after = R.remaining_bill(s,t,old), R.remaining_bill(s,t,new)
    assert (before, after) == (7,1)
    rows = ((7,1),(70,64))
    assert covered(before,after,rows) and relative_ok(2, rows)
    assert not 2+64 < 7
    assert 2+after < before
    assert old.certs == new.certs and old.receipts == new.receipts
    assert new.reserve == 100 and after <= new.reserve
    ref = brute(s,t)
    for c in (old,new):
        out = R.finish(s,t,R.Live(c,c.reserve))
        assert {(p,a):h for p,a,h in out.current.certs} == ref
    print('T28 reference witness: modeled bills 7 -> 1; check+migration 2; net gain 4.')
    print('Paired enclosure [(7,1),(70,64)] passes; rectangular extrema fail.')
    print('Second row is synthetic conservative uncertainty, not a measured second world.')
    print('Reserve 100 unchanged as a liquidity obligation; not a paid bill.')

if __name__ == '__main__':
    for k,v in sorted(exhaustive().items()): print(f'{k}: {v}')
    concrete()
    print('PASS: finite relative evidence, coverage, refinement, singleton embedding, T27 margin and T28 reference witness. Not Lean execution.')
