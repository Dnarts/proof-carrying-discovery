#!/usr/bin/env python3
"""Additional exact fully-qualified name check. Not a kernel verifier."""
import re, sys
from pathlib import Path
from collections import Counter
src, log = map(Path,sys.argv[1:3])
expected = Counter('CRTT.'+src.stem+'.'+n for n in re.findall(r'^#print axioms\s+(\S+)',src.read_text(),re.M))
actual = Counter(re.findall(r"^'([^']+)' (?:depends on axioms:|does not depend on any axioms)",log.read_text(),re.M))
if expected != actual:
    print('FAIL exact qualified names:',src.name,'missing=',dict(expected-actual),'extra=',dict(actual-expected),file=sys.stderr)
    raise SystemExit(1)
print(f'PASS qualified names: {src.name} {sum(actual.values())}/{sum(expected.values())}')
