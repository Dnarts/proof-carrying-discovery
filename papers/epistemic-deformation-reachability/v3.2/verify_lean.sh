#!/usr/bin/env bash
set -uo pipefail
FILE="${1:-lean/epistemic_deformation_reachability_v3_2.lean}"
EXPECTED_DECLS="${2:-27}"
TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT

lean "$FILE" >"$TMP" 2>&1
RC=$?
ERRORS="$(grep -c 'error:' "$TMP" || true)"
WARNS="$(grep -c 'warning:' "$TMP" || true)"
SORRY="$(grep -c 'sorryAx' "$TMP" || true)"
NATIVE="$(grep -c 'Lean.ofReduceBool' "$TMP" || true)"
DECLS="$(grep -cE "depends on axioms:|does not depend on any axioms" "$TMP" || true)"

echo "SHA-256 : $(shasum -a 256 "$FILE" | awk '{print $1}')"
echo "exit=$RC | errors=$ERRORS | warnings=$WARNS | sorryAx=$SORRY | ofReduceBool=$NATIVE | decls=$DECLS/$EXPECTED_DECLS"
cat "$TMP"

if [ "$RC" -ne 0 ] || [ "$ERRORS" -ne 0 ] || [ "$WARNS" -ne 0 ] || [ "$SORRY" -ne 0 ] || [ "$NATIVE" -ne 0 ] || [ "$DECLS" -ne "$EXPECTED_DECLS" ]; then
  echo "FAIL-CLOSED: verification gate failed." >&2
  exit 1
fi
echo "PASS: all verification gates satisfied."
