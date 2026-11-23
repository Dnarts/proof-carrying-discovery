#!/usr/bin/env python3
"""Release packager: validates source receipts and creates a clean ZIP bundle.

Pure packaging; PDF must already have been generated. Excludes intermediate LaTeX
artefacts and does not claim more formal proof than the supplied Lean logs.
"""
import hashlib, json, zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
CODE=ROOT/'gate12'
PAPER=ROOT/'hypothesis_language_gate12_ru.pdf'
assert PAPER.is_file() and PAPER.stat().st_size>40000
sup=json.loads((CODE/'gate12_final_manifest.json').read_text())
for fn,expect in sup['output_files_sha256'].items():
    actual=hashlib.sha256((CODE/fn).read_bytes()).hexdigest()
    if actual!=expect:raise ValueError(f'Source manifest mismatch: {fn}: {actual} != {expect}')
files=[ROOT/'README.md', PAPER, ROOT/'src/build_revision.py',
       ROOT/'src/hypothesis_language_gate11_ru.original.tex',
       ROOT/'src/hypothesis_language_gate12_ru.tex',
       ROOT/'verification/independent_gate12_audit.py',
       ROOT/'verification/independent_audit.json',
       ROOT/'verification/GATE12_REVIEW_RU.md',
       ROOT/'verification/latex_build_final.log']
files += sorted(CODE.glob('*'))
files=[p for p in files if p.is_file() and p.suffix not in ('.zip','.pyc') and p.name!='independent_regenerated.lean']
for p in files:assert p.is_relative_to(ROOT)
relpaths=[p.relative_to(ROOT).as_posix() for p in files]
assert len(relpaths)==len(set(relpaths))
manifest={
    'abi':'proof-carrying-discovery/hypothesis-language-gate11-12/1',
    'edition':'2026-11-23-v12.3',
    'paper_title':'Языки гипотез и доказательная эскалация представления',
    'original_gate12_archive_sha256':'dbe2bcee9602e5039c45d30c9677e8822c37c3b9762c7ab9a8da136e5097a1a9',
    'formal_verification':'Lean 4.36.0 success as reported by upstream logs; not independently recompiled in the original local audit',
    'independent_audit':'3/3 Python fixture tests; 59048 direct finite word comparisons; 9/9 source checksums; exported Lean byte-identical',
    'provenance_limit':'Selected observation prefixes are not a verified chronological oracle-call trace',
    'files':{k:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for k,p in zip(relpaths,files)},
}
manifestpath=ROOT/'RELEASE_SHA256.json'; manifestpath.write_text(json.dumps(manifest,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
all_files=files+[manifestpath]
archive=ROOT/'gate12_reproducible_bundle.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in all_files:
        rel=p.relative_to(ROOT).as_posix();zi=zipfile.ZipInfo(rel,date_time=(2026,11,23,0,0,0))
        zi.compress_type=zipfile.ZIP_DEFLATED
        zi.external_attr=0o644<<16
        z.writestr(zi,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for name,info in manifest['files'].items():
        assert hashlib.sha256(z.read(name)).hexdigest()==info['sha256']
    print('ARCHIVE',archive,'FILES',len(z.namelist()),'SIZE',archive.stat().st_size,'SHA',hashlib.sha256(archive.read_bytes()).hexdigest())
