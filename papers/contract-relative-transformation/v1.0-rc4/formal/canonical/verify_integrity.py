#!/usr/bin/env python3
"""Fail closed on missing, changed, duplicated or unlisted release files."""
import hashlib,re
from pathlib import Path
from zipfile import ZipFile

root=Path(__file__).resolve().parent

def manifest(path):
    entries={}
    for line in path.read_text().splitlines():
        h,n=line.split(maxsplit=1)
        assert re.fullmatch(r'[0-9a-f]{64}',h),line
        assert Path(n).name==n and n not in ('.','..','SHA256SUMS.txt') and n not in entries,n
        entries[n]=h
    return entries

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    allfiles=manifest(root/'SHA256SUMS.txt');upstream=manifest(root/'UPSTREAM_SHA256.txt')
    # This is a flat immutable package. Run-generated files and logs belong elsewhere.
    actual={p.name for p in root.iterdir() if p.is_file()}-{'SHA256SUMS.txt'}
    assert actual==set(allfiles),('unlisted',sorted(actual-set(allfiles)),'missing',sorted(set(allfiles)-actual))
    for n,h in allfiles.items():assert digest(root/n)==h,n
    for n,h in upstream.items():assert allfiles[n]==h,n
    assert len(upstream)==19 and all(n.endswith('.lean') for n in upstream)
    count=0
    for n in ('HISTORY_T01_T18.zip','HISTORY_T03_T19.zip'):
        with ZipFile(root/n) as z:
            assert z.testzip() is None,n
            for m in z.namelist():
                if m.endswith('/SHA256SUMS.txt'):
                    parent=m.rsplit('/',1)[0]
                    for line in z.read(m).decode().splitlines():
                        h,f=line.split(maxsplit=1)
                        assert hashlib.sha256(z.read(parent+'/'+f)).hexdigest()==h,(n,f)
                        count+=1
    print(f'PASS complete manifest {len(allfiles)}/{len(allfiles)}; 19 upstream source pins; {count} standalone historical checks.')

if __name__=='__main__':main()
