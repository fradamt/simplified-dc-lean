#!/usr/bin/env bash
# Self-test of the shake-report keep filter: runs scripts/shake-report.sh on
# saved `lake shake` output (SHAKE_RAW) for a fixture file; no Lean, no lake.
# A removal of an import line with `-- shake: keep` is KEPT (exit 0); a removal
# of a line without it is NEW under --fail-on-new (exit 1). Run from anywhere.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake
T=$(mktemp -d "$PWD/.lake/shake-selftest.XXXXXX")
trap 'rm -rf "$T"' EXIT
cat > "$T/Fix.lean" <<'LEAN'
module
public import Fix.Kept -- shake: keep (fixture: a use shake cannot see)
public import Fix.Unkept
-- public import Fix.Commented -- shake: keep (a comment line keeps nothing)
public import Fix.Commented
LEAN
fail=0
check() {  # <name> <expected rc> <expected output pattern> <removed import>
  printf '%s:\n  remove #[%s]\n' "$T/Fix.lean" "$4" > "$T/raw"
  set +e
  out=$(SHAKE_RAW="$T/raw" SHAKE_REPORT="$T/report" bash scripts/shake-report.sh --fail-on-new Fix 2>&1)
  rc=$?
  set -e
  if [ "$rc" = "$2" ] && grep -qE "$3" <<<"$out"; then echo "PASS $1 (exit $rc)"
  else echo "FAIL $1: exit $rc, expected $2 and /$3/"; echo "$out"; fail=1; fi
}
check kept 0 '0 NEW, 0 B1 downgrades, 1 kept' 'public import Fix.Kept'
check unkept 1 '^NEW remove .*Fix.lean public import Fix.Unkept$' 'public import Fix.Unkept'
check comment-only 1 '^NEW remove .*Fix.lean public import Fix.Commented$' 'public import Fix.Commented'
[ "$fail" = 0 ] && echo "PASS shake-report self-test: 3 controls" || { echo "FAIL shake-report self-test"; exit 1; }
