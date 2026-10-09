#!/usr/bin/env bash
# Check the real doc, then (full tier) run controls on temp files. C4 must fail D15 first.
# The frozen-logic controls use --check-frozen (no Lean environment load).
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
# One bound for the Lean tasks and both control pools. Validate before Lean.
workers=${AUDIT_WORKERS:-2}
for value in "$workers" "${LEAN_SLOTS:-3}" "${GATE_SLOTS:-${LEAN_SLOTS:-3}}"; do
  case "$value" in
    ''|0*|*[!0-9]*) echo "audit slot counts must be positive integers" >&2; exit 2 ;;
  esac
  if [ "$value" -lt "$workers" ]; then workers=$value; fi
done
if [ "${AUDIT_SERIAL:-0}" = 1 ]; then workers=1; fi
JOBS=$workers
manifest_run() {
  local label=$1; shift
  if [ "${AUDIT_TIMING:-0}" = 1 ]; then
    local flag=-v
    if [ "$(uname -s)" = Darwin ]; then flag=-l; fi
    /usr/bin/time "$flag" -o "$timing_dir/$label.time" "$@"
  else
    "$@"
  fi
}
mkdir -p .lake
gate_slots_init
tmp= timing_dir=
trap 'rm -rf "$tmp" "$timing_dir"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
timing_dir=$(mktemp -d "$PWD/.lake/fgsa-manifest-times.XXXXXX")
gate_with_slot manifest_run main lake env lean --run scripts/V2Manifest.lean --scope fgsa --check
# The frame/deep baselines are required at both tiers, after complete D15.
gate_with_slot manifest_run frame python3 scripts/fgsa-deep.py --frame-check
gate_with_slot manifest_run deep lake env lean --run scripts/V2Manifest.lean \
  --scope fgsa --deep --check
# NEG=0 skips controls when no checker path changed.
if [ "${NEG:-1}" != 1 ]; then echo "controls skipped (NEG=0)"; exit 0; fi
mkdir -p .lake
tmp=$(mktemp -d "$PWD/.lake/fgsa-manifest.XXXXXX")

# Test the freeze helper only on temp paths. It builds the control doc with --write.
gate_with_slot bash scripts/fgsa-freeze.sh --manifest "$tmp/base.md" \
  --frozen "$tmp/base-frozen.md" --frozen-sha "$tmp/base.sha256"
python3 - "$tmp" <<'PY'
import hashlib
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
current = (root / 'base.md').read_bytes()
assert current.endswith(b'\n') and not current.endswith(b'\n\n'), 'EOF is not one newline'
assert current == (root / 'base-frozen.md').read_bytes(), 'frozen bytes differ'
assert (root / 'base.sha256').read_text() == hashlib.sha256(current).hexdigest() + '\n'
print('CONTROL EOF/copy/hash OK')
PY
entry=$(awk '/^[a-z]+ [^ ]+ [0-9a-f]+$/ { print $2; exit }' "$tmp/base.md")
[ -n "$entry" ] || { echo "CONTROL SETUP FAIL: no entry" >&2; exit 1; }

reset_copies() {
  cp "$tmp/base.md" "$current"
  cp "$tmp/base-frozen.md" "$frozen"
  cp "$tmp/base.sha256" "$frozen_sha"
  printf '# Temp allow file\n' > "$allow"
}
rehash() {
  python3 - "$frozen" "$frozen_sha" <<'PY'
import hashlib
import pathlib
import sys

pathlib.Path(sys.argv[2]).write_text(
    hashlib.sha256(pathlib.Path(sys.argv[1]).read_bytes()).hexdigest() + "\n"
)
PY
}
edit_entry() {
  python3 - "$1" "$entry" "$2" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
lines = path.read_text().splitlines(keepends=True)
for i, line in enumerate(lines):
    words = line.split()
    if len(words) == 3 and words[1] == sys.argv[2]:
        if sys.argv[3] == "drop":
            del lines[i]
        else:
            words[2] = ("0" if words[2][0] != "0" else "1") + words[2][1:]
            lines[i] = " ".join(words) + "\n"
        break
else:
    raise SystemExit("CONTROL SETUP FAIL: entry absent")
path.write_text("".join(lines))
PY
}
check_copy() {
  manifest_run "$control_id" lake env lean --run scripts/V2Manifest.lean --scope fgsa "$mode" \
    --manifest "$current" --frozen "$frozen" --allow "$allow" --frozen-sha "$frozen_sha"
}
# Controls of the frozen logic use --check-frozen (no Lean environment load); C4 and C5
# test D15 and use the full --check.
mode=--check-frozen
fail_control() {
  echo "CONTROL $1 FAIL: $2" >&2
  cat "$neg/$1.log" >&2
  exit 1
}
expect_fail() {
  local id=$1 expected=$2 rc=0
  check_copy > "$neg/$id.log" 2>&1 || rc=$?
  printf '%s\n' "$rc" > "$timing_dir/$id.rc"
  cp "$neg/$id.log" "$timing_dir/$id.log"
  [ "$rc" -eq 1 ] || fail_control "$id" "expected exit 1, got $rc"
  grep -F -- "$expected" "$neg/$id.log" > /dev/null ||
    fail_control "$id" "expected reason: $expected"
  echo "CONTROL $id OK"
}
expect_pass() {
  local id=$1 expected=$2 rc=0
  check_copy > "$neg/$id.log" 2>&1 || rc=$?
  printf '%s\n' "$rc" > "$timing_dir/$id.rc"
  cp "$neg/$id.log" "$timing_dir/$id.log"
  [ "$rc" -eq 0 ] || fail_control "$id" "expected exit 0, got $rc"
  grep -F -- "$expected" "$neg/$id.log" > /dev/null ||
    fail_control "$id" "expected message: $expected"
  echo "CONTROL $id OK"
}

# The base is read-only after setup. Each control has separate input and
# output files, so the V2Manifest invocations can run independently.
run_manifest_control() (
  control_id=$1
  current=$neg/current.md
  frozen=$neg/frozen.md
  allow=$neg/allow.txt
  frozen_sha=$neg/frozen.sha256
  mode=--check-frozen
  reset_copies
  case "$control_id" in
    C1)
      edit_entry "$frozen" hash
      rehash
      expect_fail C1 "FROZEN CHANGED $entry:" ;;
    C2)
      edit_entry "$frozen" drop
      rehash
      expect_pass C2 "frozen entries present and unchanged" ;;
    C3)
      edit_entry "$frozen" hash
      rehash
      printf '%s\tcontrol change\tG-F0a control C3\n' "$entry" > "$allow"
      expect_pass C3 "frozen entries present and unchanged" ;;
    C4)
      mode=--check
      edit_entry "$current" drop
      expect_fail C4 "NOT LISTED $entry" ;;
    C5)
      mode=--check
      edit_entry "$current" hash
      frozen=$neg/no-frozen.md
      expect_fail C5 "CHANGED $entry " ;;
    C6)
      mode=--check
      current=$neg/no-current.md
      expect_pass C6 "SKIP: $current does not exist (before G-F0a)" ;;
    C7)
      edit_entry "$frozen" hash
      expect_fail C7 "FROZEN SHA256 MISMATCH $frozen:" ;;
    C8)
      printf 'FGSA.Manifest.Control.Stale\tcontrol stale entry\tG-F0a control C8\n' > "$allow"
      expect_fail C8 "STALE ALLOW FGSA.Manifest.Control.Stale: no frozen entry" ;;
    C9)
      printf '%s\t\tG-F0a control C9\n' "$entry" > "$allow"
      expect_fail C9 "INVALID ALLOW line 1: empty field" ;;
    C10)
      python3 - "$frozen" "$entry" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
lines = path.read_text().splitlines(keepends=True)
for i, line in enumerate(lines):
    words = line.split()
    if len(words) == 3 and words[1] == sys.argv[2]:
        lines.insert(i + 1, f"{words[0]} {words[1]}RemovedControl {words[2]}\n")
        break
else:
    raise SystemExit("CONTROL SETUP FAIL: entry absent")
path.write_text("".join(lines))
PY
      rehash
      expect_fail C10 "FROZEN REMOVED ${entry}RemovedControl" ;;
    C11|C12|C13)
      edit_entry "$frozen" hash
      rehash
      case "$control_id" in
        C11)
          printf '%s\tcontrol change\tG-F0a control C11\texpect=%s\n' \
            "$entry" "$cur_hash" > "$allow"
          expect_pass C11 "frozen entries present and unchanged" ;;
        C12)
          printf '%s\tcontrol change\tG-F0a control C12\texpect=0000000000000000\n' \
            "$entry" > "$allow"
          expect_fail C12 "ALLOW EXPECT $entry: expected 0000000000000000, got $cur_hash" ;;
        C13)
          printf '%s\tcontrol change\tG-F0a control C13\tpin=%s\n' "$entry" "$cur_hash" > "$allow"
          expect_fail C13 \
            "INVALID ALLOW line 1: fourth field must be expect=<hash> or expect=removed" ;;
      esac ;;
    *) echo "unknown manifest control: $control_id" >&2; exit 2 ;;
  esac
)
cur_hash=$(awk -v e="$entry" '$2 == e { print $3; exit }' "$tmp/base.md")
[ -n "$cur_hash" ] || { echo "CONTROL SETUP FAIL: no current hash" >&2; exit 1; }
# Reap each child in its worker. Bash 3.2 can lose an old completed child's
# wait status during a long submission loop (wait then returns 127).
# Use the same bounded executor as the claims controls; gate_with_slot
# still applies the shared gate cap to each child.
gate_slots_init
manifest_workers=$workers
export tmp entry cur_hash timing_dir manifest_workers
export -f manifest_run reset_copies rehash edit_entry check_copy fail_control \
  expect_fail expect_pass run_manifest_control
python3 - <<'PY'
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import os
import subprocess
import sys

root = Path(os.environ['tmp']) / 'controls'
root.mkdir()
labels = sorted(f'C{i}' for i in range(1, 14))

def control(label):
    private = root / label
    private.mkdir()
    log = private / 'control.log'
    env = dict(os.environ, neg=str(private))
    with log.open('w') as out:
        proc = subprocess.run(
            ['bash', '-c', 'set -euo pipefail; source scripts/gate-common.sh; '
             'gate_with_slot run_manifest_control "$1"', 'manifest-control', label],
            env=env, stdout=out, stderr=subprocess.STDOUT)
    return proc.returncode, log

with ThreadPoolExecutor(max_workers=int(os.environ['manifest_workers'])) as pool:
    futures = [pool.submit(control, label) for label in labels]
    failure = 0
    # Output and failure selection use lexical label order in both modes.
    for future in futures:
        code, log = future.result()
        sys.stdout.write(log.read_text())
        sys.stdout.flush()
        if code and not failure:
            failure = code if code > 0 else 1
    raise SystemExit(failure)
PY

gate_with_slot manifest_run deep-controls python3 scripts/fgsa-deep-controls.py
