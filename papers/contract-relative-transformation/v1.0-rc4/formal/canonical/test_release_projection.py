#!/usr/bin/env python3
"""Synthetic parser controls only. Never presented as Lean output."""
import contextlib, io, tempfile
from pathlib import Path
import check_release as C

def synthetic(ref):
    lines=[]
    for name,r in ref.items():
        def emit(tag,*args):lines.append('|'.join([tag,name,*map(str,args)]))
        emit('T32',*r['metrics']);emit('T32STATUS',r['status'])
        for v in r['upgrades']:emit('T32UPGRADE',v)
        for e in r['events']:
            if e[0]=='observed':emit('T32EVENT',f'observed;answer={str(e[1]).lower()};fee={e[2]}')
            elif e[0]=='prepared':emit('T32EVENT',f'prepared;fee={e[1]};migration={e[2]};rows={list(map(tuple,e[3]))}')
            else:emit('T32EVENT','attempted;verdict='+e[1])
        for e in r['journal']:
            if e[0]=='evidence':emit('T32JOURNAL',f'evidence;fee={e[1]}')
            else:emit('T32JOURNAL',f'attempt;checkFee={e[1]};verdict={e[2]};debit={e[3]}')
        for k,f in r['search']:emit('T32SEARCH',k,f)
        for key,tag in [('prior','T32PRIOR'),('certificates','T32CERT')]:
            for c in r[key]:emit(tag,*[','.join(map(str,part)) for part in c])
    return lines

def main():
    ref=C.reference();lines=synthetic(ref)
    with tempfile.TemporaryDirectory() as d:
        p=Path(d)/'synthetic.txt'
        def check(ls,accept):
            p.write_text('\n'.join(ls)+'\n')
            try:
                with contextlib.redirect_stdout(io.StringIO()):C.compare(p,ref)
            except (AssertionError,ValueError,KeyError,IndexError):
                assert not accept
            else:assert accept
        check(lines,True)
        # For each control modify an existing field or remove a required row.
        for prefix,mutate in [
            ('T32|single|',lambda l:l.replace('|6|104|','|7|104|')),
            ('T32UPGRADE|single|',lambda l:l.replace('accepted','rejected')),
            ('T32EVENT|single|observed',lambda l:l.replace('true','false')),
            ('T32EVENT|single|prepared',lambda l:l.replace('(7, 1)','(7, 2)')),
            ('T32JOURNAL|single|attempt',lambda l:l.replace('debit=2','debit=1')),
            ('T32SEARCH|single|',lambda l:l[:-1]+'2'),
            ('T32CERT|nonempty|',lambda l:None),
            ('T32PRIOR|predecessor|',lambda l:None),
            ('T32STATUS|fallback|',lambda l:l.replace('blocked','kept')),
            ('T32|baseline|',lambda l:None),
        ]:
            i=next(i for i,l in enumerate(lines) if l.startswith(prefix));v=mutate(lines[i]);assert v!=lines[i]
            bad=lines[:i]+([] if v is None else [v])+lines[i+1:];check(bad,False)
        check(lines+[lines[0]],False)
    print('PASS 12 synthetic projection controls: clean + 11 rejected mutations. Not Lean execution.')
if __name__=='__main__':main()
