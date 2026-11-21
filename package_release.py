#!/usr/bin/env python3
"""Reproducible artifact indexing and byte-level archive validation.

This is packaging metadata, NOT a scientific preregistration or attestation.
"""
from pathlib import Path
from hashlib import sha256
import json, zipfile

ROOT=Path(__file__).resolve().parent
EXCLUDE={'MANIFEST.json','SHA256SUMS.txt'}
EXCLUDE_DIR={'__pycache__','pdf_renders','.git','.venv'}
EXCLUDE_PATHS={'evidence/preprint_montage.png','evidence/preprint_extracted.txt',
               'evidence/pdf_build_stdout.txt','evidence/pdf_build_stderr.txt',
               'evidence/audit_receipt_pre_manifest.json'}
ARCHIVE=ROOT.parent/'proof-carrying-discovery-v1.1.1.zip'


def payload_files():
    selected=[]
    for p in ROOT.rglob('*'):
        if not p.is_file():continue
        rel=p.relative_to(ROOT).as_posix()
        if any(part in EXCLUDE_DIR for part in p.relative_to(ROOT).parts):continue
        if rel in EXCLUDE_PATHS or rel in EXCLUDE:continue
        if p.suffix in ('.pyc','.tmp'):continue
        selected.append(p)
    return sorted(selected)


def main():
    files=payload_files()
    metadata={'schema':'invariantnet-release/1','version':'1.1.1',
              'repository':'https://github.com/Dnarts/proof-carrying-discovery',
              'source_of_truth':'byte-addressed files, not their render projections',
              'manifest_self_hash':'omitted to avoid recursion',
              'previous':'v1.0 unmodified in legacy/; exact v1.1.0 archive in history/',
              'timestamp':'22 November 2026 (authoring date; no third-party timestamp)',
              'files':{p.relative_to(ROOT).as_posix():{
                   'bytes':p.stat().st_size,'sha256':sha256(p.read_bytes()).hexdigest()} for p in files}}
    (ROOT/'MANIFEST.json').write_text(json.dumps(metadata,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    (ROOT/'SHA256SUMS.txt').write_text(''.join(
        f'{metadata["files"][p.relative_to(ROOT).as_posix()]["sha256"]}  {p.relative_to(ROOT).as_posix()}\n'
        for p in files),encoding='utf-8')
    with zipfile.ZipFile(ARCHIVE,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for p in files+[ROOT/'SHA256SUMS.txt',ROOT/'MANIFEST.json']:
            z.write(p,arcname='proof-carrying-discovery/'+p.relative_to(ROOT).as_posix())
    with zipfile.ZipFile(ARCHIVE) as z:
        assert z.testzip() is None
        for p in files+[ROOT/'SHA256SUMS.txt',ROOT/'MANIFEST.json']:
            n='proof-carrying-discovery/'+p.relative_to(ROOT).as_posix()
            assert z.read(n)==p.read_bytes(),n
    print(json.dumps({'archive':str(ARCHIVE),'version':'1.1.1','n_files':len(files)+2,
                      'archive_bytes':ARCHIVE.stat().st_size,
                      'archive_sha256':sha256(ARCHIVE.read_bytes()).hexdigest(),
                      'manifest_sha256':sha256((ROOT/'MANIFEST.json').read_bytes()).hexdigest(),
                      'zip_readback':'PASS'},indent=2))

if __name__=='__main__':main()
