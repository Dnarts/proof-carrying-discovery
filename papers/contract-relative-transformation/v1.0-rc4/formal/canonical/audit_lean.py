#!/usr/bin/env python3
"""Fail-closed text audit, including reports printed before a Lean failure.

The report audit does not substitute for successful compilation. In particular,
missing reports are marked incomplete, never assumed axiom-free.
"""
import re
import sys
from pathlib import Path
from collections import Counter

source, log = map(Path, sys.argv[1:3])
lean_status = int(sys.argv[3])
text = log.read_text(errors='replace')
expected = re.findall(r'^#print axioms\s+([^\s]+)', source.read_text(), re.M)
reports = re.findall(
    r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)[ \t]*$",
    text, re.M)
allowed = {'propext', 'Quot.sound'}
problems = []
matched = Counter()
axioms = Counter()
for name, deps in reports:
    keys = [key for key in expected if name == key or name.endswith('.' + key)]
    if len(keys) != 1:
        problems.append(f'unmatched/ambiguous report: {name}')
    else:
        matched[keys[0]] += 1
    dependencies = {a.strip() for a in deps.split(',') if a.strip()}
    axioms.update(dependencies)
    unexpected = dependencies - allowed
    if unexpected:
        problems.append(f'{name}: disallowed axioms {sorted(unexpected)}')
for key in expected:
    if matched[key] != 1:
        problems.append(f'{key}: expected one report, got {matched[key]}')
for pattern, label in [
    (r'warning:', 'Lean warnings'),
    (r'error:', 'Lean errors'),
    (r'uses [\'\"]?sorry|sorryAx', 'placeholder diagnostics'),
    (r'Classical\.choice', 'classical choice diagnostics'),
]:
    n = len(re.findall(pattern, text, re.I))
    if n:
        problems.append(f'{label}: {n} occurrence(s)')
if lean_status:
    problems.append(f'Lean exit status {lean_status}')
print(f'AUDIT {source.name}: {len(reports)}/{len(expected)} axiom reports; '
      f'Lean exit={lean_status}; dependencies={dict(sorted(axioms.items()))}')
if problems:
    for problem in problems:
        print(f'  FAIL: {problem}', file=sys.stderr)
    raise SystemExit(1)
print(f'PASS {source.name}: {len(expected)} axiom reports audited.')
