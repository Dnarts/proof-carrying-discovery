#!/usr/bin/env bash
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
cd -- "$(dirname -- "$0")"
if command -v shasum >/dev/null 2>&1; then
  shasum -a 256 -c SHA256SUMS.txt
  shasum -a 256 -c UPSTREAM_SHA256.txt
else
  sha256sum -c SHA256SUMS.txt
  sha256sum -c UPSTREAM_SHA256.txt
fi
python3 test_audit.py
if ! command -v lean >/dev/null 2>&1; then
  echo 'ERROR: Lean not installed; no kernel verification.' >&2
  exit 127
fi
lean --version
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
for src in AdaptiveObservation.lean InvestigationTransfer.lean InvestigationLibrary.lean MorphismDiscovery.lean BudgetedDiscovery.lean CertifiedPruning.lean ResumeLaws.lean BudgetedPruning.lean ImpasseCompilation.lean LearningDiscovery.lean MetaInvestigation.lean MetaEvidenceAcquisition.lean DecisionEvidence.lean ControllerReplacement.lean; do
  echo "=== LEAN: $src ==="
  lean_status=0
  lean -o "$build/${src%.lean}.olean" "$src" > "$build/${src%.lean}.log" 2>&1 || lean_status=$?
  cat "$build/${src%.lean}.log"
  audit_status=0
  python3 audit_lean.py "$src" "$build/${src%.lean}.log" "$lean_status" || audit_status=$?
  name_status=0
  python3 audit_names.py "$src" "$build/${src%.lean}.log" || name_status=$?
  if (( lean_status != 0 )); then
    exit "$lean_status"
  fi
  if (( name_status != 0 )); then
    exit "$name_status"
  fi
  if (( audit_status != 0 )); then
    exit "$audit_status"
  fi
done
python3 check_pruning.py
python3 check_impasse.py
python3 check_learning.py
python3 check_meta.py
python3 check_evidence.py
python3 check_decision.py
python3 check_replacement.py
printf '\nPASS: manifests, Lean compilation, audited axiom reports and finite cross-check.\n'
