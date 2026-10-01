#!/usr/bin/env bash
# Check the real doc, then (full tier) run controls on temp files. C4 must fail D15 first.
# The frozen-logic controls use --check-frozen (no Lean environment load).
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean --run scripts/V2Manifest.lean --scope fgsa --check
# The controls are negative controls: the merge tier (NEG=0) skips them (BUILD §7.7).
if [ "${NEG:-1}" != 1 ]; then echo "controls skipped (NEG=0, merge tier)"; exit 0; fi
mkdir -p .lake
tmp=$(mktemp -d "$PWD/.lake/fgsa-manifest.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# Test the freeze helper only on temp paths. It builds the control doc with --write.
bash scripts/fgsa-freeze.sh --manifest "$tmp/base.md" \
  --frozen "$tmp/base-frozen.md" --frozen-sha "$tmp/base.sha256"
entry=$(awk '/^[a-z]+ [^ ]+ [0-9a-f]+$/ { print $2; exit }' "$tmp/base.md")
[ -n "$entry" ] || { echo "CONTROL SETUP FAIL: no entry" >&2; exit 1; }
current=$tmp/current.md
frozen=$tmp/frozen.md
allow=$tmp/allow.txt
frozen_sha=$tmp/frozen.sha256

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
  lake env lean --run scripts/V2Manifest.lean --scope fgsa "$mode" \
    --manifest "$current" --frozen "$frozen" --allow "$allow" --frozen-sha "$frozen_sha"
}
# Controls of the frozen logic use --check-frozen (no Lean environment load); C4 and C5
# test D15 and use the full --check.
mode=--check-frozen
fail_control() {
  echo "CONTROL $1 FAIL: $2" >&2
  cat "$tmp/$1.log" >&2
  exit 1
}
expect_fail() {
  local id=$1 expected=$2 rc=0
  check_copy > "$tmp/$id.log" 2>&1 || rc=$?
  [ "$rc" -eq 1 ] || fail_control "$id" "expected exit 1, got $rc"
  grep -F -- "$expected" "$tmp/$id.log" > /dev/null ||
    fail_control "$id" "expected reason: $expected"
  echo "CONTROL $id OK"
}
expect_pass() {
  local id=$1 expected=$2 rc=0
  check_copy > "$tmp/$id.log" 2>&1 || rc=$?
  [ "$rc" -eq 0 ] || fail_control "$id" "expected exit 0, got $rc"
  grep -F -- "$expected" "$tmp/$id.log" > /dev/null ||
    fail_control "$id" "expected message: $expected"
  echo "CONTROL $id OK"
}

# C1: changed frozen hash, with a valid new checksum, fails append-only.
reset_copies
edit_entry "$frozen" hash
rehash
expect_fail C1 "FROZEN CHANGED $entry:"

# C2: one entry absent from the frozen baseline is a permitted new entry.
reset_copies
edit_entry "$frozen" drop
rehash
expect_pass C2 "frozen entries present and unchanged"

# C3: an allow line permits a changed frozen entry.
reset_copies
edit_entry "$frozen" hash
rehash
printf '%s\tcontrol change\tG-F0a control C3\n' "$entry" > "$allow"
expect_pass C3 "frozen entries present and unchanged"

# C4: removing a current entry fails D15 before the frozen check.
mode=--check
reset_copies
edit_entry "$current" drop
expect_fail C4 "NOT LISTED $entry"

# C5: a current hash mismatch fails D15 even without a frozen copy.
reset_copies
edit_entry "$current" hash
frozen=$tmp/no-frozen.md
expect_fail C5 "CHANGED $entry "
frozen=$tmp/frozen.md
mode=--check-frozen

# C6: a missing current doc skips even if frozen controls exist.
reset_copies
current=$tmp/no-current.md
mode=--check
expect_pass C6 "SKIP: $current does not exist (before G-F0a)"
mode=--check-frozen
current=$tmp/current.md

# C7: a changed frozen file with its old checksum fails the integrity check.
reset_copies
edit_entry "$frozen" hash
expect_fail C7 "FROZEN SHA256 MISMATCH $frozen:"

# C8: allow names must exist in the frozen baseline.
reset_copies
printf 'FGSA.Manifest.Control.Stale\tcontrol stale entry\tG-F0a control C8\n' > "$allow"
expect_fail C8 "STALE ALLOW FGSA.Manifest.Control.Stale: no frozen entry"

# C9: every allow field must be non-empty.
reset_copies
printf '%s\t\tG-F0a control C9\n' "$entry" > "$allow"
expect_fail C9 "INVALID ALLOW line 1: empty field"

# C10: a frozen entry that the current doc no longer has (a removed declaration) fails.
reset_copies
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
expect_fail C10 "FROZEN REMOVED ${entry}RemovedControl"

# C11–C13 (backlog C22): an optional fourth allow field expect=<hash> pins the change.
# The frozen copy gets a changed hash; the current entry keeps its base hash.
cur_hash=$(awk -v e="$entry" '$2 == e { print $3; exit }' "$tmp/base.md")
[ -n "$cur_hash" ] || { echo "CONTROL SETUP FAIL: no current hash" >&2; exit 1; }
reset_copies
edit_entry "$frozen" hash
rehash
printf '%s\tcontrol change\tG-F0a control C11\texpect=%s\n' "$entry" "$cur_hash" > "$allow"
expect_pass C11 "frozen entries present and unchanged"
printf '%s\tcontrol change\tG-F0a control C12\texpect=0000000000000000\n' "$entry" > "$allow"
expect_fail C12 "ALLOW EXPECT $entry: expected 0000000000000000, got $cur_hash"
printf '%s\tcontrol change\tG-F0a control C13\tpin=%s\n' "$entry" "$cur_hash" > "$allow"
expect_fail C13 "INVALID ALLOW line 1: fourth field must be expect=<hash> or expect=removed"
