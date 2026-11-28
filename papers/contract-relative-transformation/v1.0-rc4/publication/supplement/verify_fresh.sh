#!/usr/bin/env bash
# Fresh execution of the unchanged canonical runner, never log replay.
set -euo pipefail
if [[ $# != 2 ]]; then
  echo 'Usage: bash verify_fresh.sh <RECONCILED.zip> <new-output-directory>' >&2
  exit 2
fi
archive=$(python3 -c 'import os,sys;print(os.path.abspath(sys.argv[1]))' "$1")
out=$(python3 -c 'import os,sys;print(os.path.abspath(sys.argv[1]))' "$2")
if [[ -e "$out" ]]; then echo 'ERROR: output must not exist' >&2; exit 2; fi
mkdir -p -- "$out"
expected=e09580cdb8a8f900401390db394a7bde07bb328449b50b059f2a8cd3c175c79e
work=''
phase=initialization
finish() {
  status=$?
  trap - EXIT
  set +e
  python3 - "$out" "$status" "$phase" <<'PY'
import datetime, hashlib, json, pathlib, sys
p=pathlib.Path(sys.argv[1]); code=int(sys.argv[2]); phase=sys.argv[3]
logs={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in p.glob('*.log')}
verified=(code==0 and phase=='verified')
(p/'STATUS.json').write_text(json.dumps({'exit_code':code,'phase':phase,'fresh_kernel_verification_passed':verified,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'log_sha256':logs},indent=2)+'\n')
PY
  if [[ -n "$work" ]]; then rm -rf -- "$work"; fi
  exit "$status"
}
trap finish EXIT
{
  printf 'Mode: clean extraction and fresh canonical runner (not replay)\n'
  printf 'Input archive: %s\nExpected SHA-256: %s\n' "$archive" "$expected"
  date -u '+Started UTC: %Y-%m-%dT%H:%M:%SZ'
  uname -a
  python3 --version
  command -v lean || echo 'Lean executable absent on PATH'
} > "$out/ENVIRONMENT.log" 2>&1
work=$(mktemp -d)
phase=archive_integrity
python3 - "$archive" "$expected" "$work" <<'PY' | tee "$out/EXTRACTION.log"
import hashlib,pathlib,stat,sys,zipfile
p=pathlib.Path(sys.argv[1]); expected=sys.argv[2]; dest=pathlib.Path(sys.argv[3]); actual=hashlib.sha256(p.read_bytes()).hexdigest()
print('Archive SHA-256:',actual,flush=True)
if actual!=expected: raise SystemExit('ERROR: wrong archive hash')
with zipfile.ZipFile(p) as z:
    seen=set()
    for i in z.infolist():
        n=pathlib.PurePosixPath(i.filename)
        if (n.is_absolute() or '..' in n.parts or '\\' in i.filename or not n.parts or n.parts[0]!='CRTT-v1.0-FULL-ARCHITECTURE' or stat.S_ISLNK(i.external_attr>>16) or i.filename in seen):
            raise SystemExit('ERROR: unsafe or repeated entry: '+i.filename)
        seen.add(i.filename)
    if z.testzip() is not None: raise SystemExit('ERROR: ZIP CRC')
    z.extractall(dest)
print('Clean extraction PASS')
PY
root="$work/CRTT-v1.0-FULL-ARCHITECTURE"
phase=manifest_verification
(cd "$root" && python3 verify_archive.py) | tee "$out/ARCHIVE_CHECK.log"
phase=canonical_runner
set +e
(cd "$root/canonical" && bash run_verify.sh) 2>&1 | tee "$out/FRESH_KERNEL_CHECK.log"
statuses=("${PIPESTATUS[@]}")
set -e
printf '%s\n' "${statuses[0]}" > "$out/RUNNER_EXIT.txt"
if [[ ${statuses[1]} -ne 0 ]]; then exit "${statuses[1]}"; fi
if [[ ${statuses[0]} -ne 0 ]]; then exit "${statuses[0]}"; fi
phase=success_marker
# Exit status and the complete runner marker must both agree.
grep -Fx 'PASS: T32 complete manifest, Lean compilation, 542 audited reports, finite checks and actual CLI/reference agreement.' "$out/FRESH_KERNEL_CHECK.log" >/dev/null
phase=verified
