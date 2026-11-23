#!/usr/bin/env bash
set -uo pipefail
LOG="ALL_4_MODULES_v2_4_VERIFICATION.log"
FILES=(
  "epistemic_revision_kernel_v2_4.lean"
  "gate14_port_escalation_v2_4.lean"
  "gate15_intervention_algebra_v2_4.lean"
  "gate16_stochastic_gap_evalue_v2_4.lean"
)
OVERALL=0
{
  echo "=============================================================================="
  echo "UNIFIED VERIFICATION LOG — v2.4 (ALL 4 MODULES, 44 DECLARATIONS)"
  echo "=============================================================================="
  echo "TIMESTAMP_UTC: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "HOST         : $(uname -srm)"
  echo -n "TOOLCHAIN    : "; lean --version
  echo ""
  for f in "${FILES[@]}"; do
    echo "------------------------------------------------------------------------------"
    echo "MODULE: $f"
    shasum -a 256 "$f"
    wc -l "$f"
    OUT=$(lean "$f" 2>&1)
    RC=$?
    echo "EXIT_CODE: $RC"
    if [ $RC -ne 0 ]; then OVERALL=1; fi
    if echo "$OUT" | grep -qiE "warning|error"; then
      echo "WARNINGS_OR_ERRORS: PRESENT"
      OVERALL=1
    else
      echo "WARNINGS_OR_ERRORS: NONE"
    fi
    echo "$OUT"
    echo ""
  done
  echo "=============================================================================="
  echo "OVERALL_EXIT_CODE: $OVERALL"
  echo "=============================================================================="
} > "$LOG" 2>&1
cat "$LOG"
exit $OVERALL
