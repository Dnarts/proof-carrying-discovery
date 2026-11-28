#!/usr/bin/env python3
"""Synthetic fixtures for the audit parser; not Lean execution."""
from pathlib import Path
from tempfile import TemporaryDirectory
from subprocess import run
import sys

checker = Path(__file__).with_name('audit_lean.py')
valid = "'CRTT.Test.a' depends on axioms: [propext, Quot.sound]\n'CRTT.Test.Witnesses.b' does not depend on any axioms\n"
with TemporaryDirectory() as tmp:
    source = Path(tmp) / 'Test.lean'
    source.write_text('#print axioms a\n#print axioms Witnesses.b\n')
    log = Path(tmp) / 'fake.log'
    cases = [
        ('clean', valid, 0, True),
        ('nonzero compiler exit despite complete reports', valid, 1, False),
        ('partial reports', valid.splitlines()[0] + '\n', 1, False),
        ('placeholder', valid.replace('propext, Quot.sound', 'sorryAx'), 1, False),
        ('classical', valid.replace('propext, Quot.sound', 'Classical.choice'), 0, False),
        ('unknown axiom', valid.replace('propext, Quot.sound', 'unknownAxiom'), 0, False),
        ('warning', valid + 'Test.lean:1:1: warning: synthetic fixture\n', 0, False),
        ('error', valid + 'Test.lean:1:1: error: synthetic fixture\n', 0, False),
        ('wrong name with same count', valid.replace('Witnesses.b', 'Witnesses.c'), 0, False),
        ('duplicate', valid + valid.splitlines()[0] + '\n', 0, False),
    ]
    for name, data, status, passes in cases:
        log.write_text(data)
        result = run([sys.executable, str(checker), str(source), str(log), str(status)], capture_output=True, text=True)
        assert (result.returncode == 0) == passes, (name, result.stdout, result.stderr)
        print(f'PASS synthetic audit fixture: {name}')
print(f'PASS {len(cases)} audit-parser fixtures. No Lean execution.')
