#!/usr/bin/env python3
"""Verify the shipped v1.1 artifacts without modifying the source files.

Reexecutes the programs, compares deterministic output to shipped receipts,
checks immutable predecessor hashes and runs the separate independent tests.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
VOLATILE={"time_s","wall_seconds","platform","python_version"}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def stable(value):
    if isinstance(value,dict):
        return {k:stable(v) for k,v in value.items() if k not in VOLATILE}
    if isinstance(value,list):return [stable(v) for v in value]
    return value


def cmd(args):
    r=subprocess.run(args,cwd=ROOT,capture_output=True,text=True)
    if r.returncode:
        raise AssertionError(f"FAILED: {' '.join(args)}\n{r.stdout}\n{r.stderr}")
    return r


def verify():
    known={
       'legacy/abc_shapley_v1.py':'90edaa1d3e9b9ddbccee07bd3893562054aabf5ae899013388a5419c6bf828fc',
       'legacy/dfa_to_1dca_v1.py':'4975381c4ed98e8db13be24029fb6c6d21a49dffea1851b258a00d9066b8d9ba',
       'legacy/abc_shapley_v1_results.json':'13d3eedccdfe6df9ec8ec4a0e0eb1734a0a8559627d10b69ee7d6475025c4958',
       'legacy/dfa_to_1dca_v1_results.json':'6b4bac1a9937cae3e0e5f1d8791f0af07cac5346e2712618099f86976ccae459',
    }
    for name,digest in known.items():
        assert sha(ROOT/name)==digest, (name,'original altered')
    audit=cmd([sys.executable,'-m','unittest','discover','-s','tests','-p','test_*.py','-v'])
    assert 'Ran 9 tests' in audit.stderr and 'OK' in audit.stderr
    programs={
      'v1_1/dfa_to_1dca_v1_1.py':'v1_1/dfa_to_1dca_v1_1_results.json',
      'v1_1/abc_historical_v1_1.py':'v1_1/abc_historical_v1_1_results.json',
    }
    deterministic={}
    for script,receipt in programs.items():
        fresh=json.loads(cmd([sys.executable,script]).stdout)
        shipped=json.loads((ROOT/receipt).read_text())
        assert stable(fresh)==stable(shipped),f'{script} diverged in deterministic output'
        deterministic[script]={"status":"PASS","source_sha256":sha(ROOT/script),
                               "receipt_sha256":sha(ROOT/receipt)}
    manifest=ROOT/'MANIFEST.json'
    if manifest.exists():
        data=json.loads(manifest.read_text())
        for name,info in data['files'].items():
            assert sha(ROOT/name)==info['sha256'],f'{name} failed manifest'
        manifest_status='PASS'
    else:manifest_status='NOT_CREATED_YET'
    return {"status":"PASS","python_version":platform.python_version(),
            "original_legacy_hashes":"PASS", "independent_unittests":"9/9 PASS",
            "fresh_deterministic_reexecution":deterministic,
            "manifest":manifest_status,
            "global_unknown_teacher_equivalence":"NOT_CLAIMED",
            "proof_assistant":"NOT_CLAIMED"}


if __name__=='__main__':
    print(json.dumps(verify(),ensure_ascii=False,indent=2))
