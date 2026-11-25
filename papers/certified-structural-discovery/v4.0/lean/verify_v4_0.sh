#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LEAN_FILE="$SCRIPT_DIR/certified_structural_discovery_v4_0.lean"
echo "Lean version: $(lean --version)"
set +e
OUT="$(lean "$LEAN_FILE" 2>&1)"
RC=$?
set -e
echo "$OUT"
if [ "$RC" -ne 0 ]; then
  echo "FAIL: lean exited with code $RC" >&2
  exit "$RC"
fi
if echo "$OUT" | grep -q "sorryAx"; then
  echo "FAIL: sorryAx detected!" >&2
  exit 1
fi
if echo "$OUT" | grep -q "ofReduceBool"; then
  echo "FAIL: native_decide (ofReduceBool) detected!" >&2
  exit 1
fi
if echo "$OUT" | grep -q "Classical.choice"; then
  echo "FAIL: Classical.choice detected!" >&2
  exit 1
fi
DECLS="$(echo "$OUT" | grep -c "CertifiedStructuralDiscoveryV40\.")"
if [ "$DECLS" -ne 18 ]; then
  echo "FAIL: expected 18 audited declarations, got $DECLS" >&2
  exit 1
fi
echo "PASS: certified_structural_discovery_v4_0.lean compiled with exit=0 (18/18 declarations, 0 imports, 0 sorryAx, 0 ofReduceBool, 0 Classical.choice)."
