#!/usr/bin/env bash
# Run from the repository root. Freeze gates must use --tier full.
# The three check scripts run in parallel and share one GATE_SLOTS cap.
# check-fgsa-claims.sh runs alone after them: its lake calls are not slot-capped
# (NUC 2026-10-01: 282 s, peak 4.3 GiB; merge tier NEG=0 skips its compiled controls).
# Defaults: Mac 3, Linux 3 (scripts/gate-common.sh); env wins. JOBS is only a per-script pool bound.
# Linux requires a user scope with GATE_MEM (default 16G) and no swap; without it the gate refuses to run.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
gate_args=("$@")
tier=auto; base=; critical_path=0
usage() { echo "usage: bash scripts/gate.sh [--tier merge|full|auto] [--base <ref>] [--jobs N] | --critical-path"; }
while [ $# -gt 0 ]; do
  case "$1" in
    --tier|--base|--jobs)
      [ $# -ge 2 ] || { usage >&2; exit 2; }
      case "$1" in --tier) tier=$2 ;; --base) base=$2 ;; --jobs) JOBS=$2 ;; esac
      shift 2 ;;
    --critical-path) critical_path=1; shift ;;
    --help|-h) usage; exit 0 ;;
    *) usage >&2; exit 2 ;;
  esac
done
case "$tier" in auto|merge|full) ;; *) usage >&2; exit 2 ;; esac
gate_jobs
export JOBS

# Probe the user manager and memory properties before replacing this driver.
# Keep every argument and never retry a failed gate outside its memory scope.
memory_limit="Mac Lean wrapper"
if [ "$(uname -s)" = Linux ]; then
  memory_limit=${GATE_MEM:-16G}
  if [ "${GATE_MEM_SCOPED:-0}" != 1 ]; then
    if command -v systemd-run >/dev/null 2>&1 &&
        systemd-run --user --scope -q -p "MemoryMax=$memory_limit" -p MemorySwapMax=0 true; then
      export GATE_MEM_SCOPED=1
      exec systemd-run --user --scope -q -p "MemoryMax=$memory_limit" -p MemorySwapMax=0 \
        bash scripts/gate.sh "${gate_args[@]}"
    fi
    # Lead ruling (DC 2026-09-30, after the NUC OOM): no gate without the scope.
    echo "REFUSED: cannot create a systemd-run --user scope with MemoryMax=$memory_limit; the gate does not run unlimited" >&2
    exit 2
  else
    memory_limit="$memory_limit, swap=0"
  fi
fi
# BUILD §7.7: the critical-path measurement is separate from the tiers (freeze gates and
# weekly). It runs in the same memory scope; the caller holds the NUC lock.
if [ "$critical_path" = 1 ]; then
  [ "$(uname -s)" = Linux ] || { echo "gate.sh --critical-path: NUC (Linux) only" >&2; exit 2; }
  echo "critical-path: memory=$memory_limit"
  exec bash scripts/critical-path.sh
fi
mkdir -p .lake
GATE_SLOT_DIR=$(mktemp -d "$PWD/.lake/gate-slots.XXXXXX")
gate_slots_init
logs=$(mktemp -d "$PWD/.lake/gate-logs.XXXXXX")
started=$(date +%s)
failed=0

# Include both sides of renames. Also inspect local edits, since a gate may
# run before a commit. Use NUL delimiters for names and disable external diffs.
tier_path() {
  case "$1" in
    scripts/*|*allow*.txt|lakefile.toml|lean-toolchain|lake-manifest.json|Statements/*|*/Statements/*|docs/FGSA-API.md|docs/FGSA-API-frozen.md)
      reason="gate input changed: $1"; return 0 ;;
  esac
  return 1
}
choose_tier() {
  if [ "$tier" != auto ]; then reason="explicit --tier $tier"; return; fi
  if [ -z "$base" ]; then base=$(git merge-base main HEAD); fi
  base=$(git rev-parse --verify "$base^{commit}")
  git diff --no-ext-diff --no-renames --name-only -z "$base..HEAD" > "$logs/paths"
  git diff --no-ext-diff --no-renames --name-only -z HEAD >> "$logs/paths"
  git ls-files --others --exclude-standard -z >> "$logs/paths"
  tier=full
  local path
  while IFS= read -r -d '' path; do
    if tier_path "$path"; then return; fi
  done < "$logs/paths"
  git diff --no-ext-diff --no-textconv --no-renames --unified=0 "$base..HEAD" -- '*.lean' > "$logs/imports.diff"
  git diff --no-ext-diff --no-textconv --no-renames --unified=0 HEAD -- '*.lean' >> "$logs/imports.diff"
  if grep -vE '^(\+\+\+|---)' "$logs/imports.diff" |
      grep -E '^[+-](.*[^[:alnum:]_])?import([^[:alnum:]_]|$)' >/dev/null; then
    reason="an import line changed"; return
  fi
  git ls-files --others --exclude-standard -z -- '*.lean' > "$logs/untracked-lean"
  while IFS= read -r -d '' path; do
    if grep -E '(^|[^[:alnum:]_])import([^[:alnum:]_]|$)' "$path" >/dev/null; then
      reason="an import line was added: $path"; return
    fi
  done < "$logs/untracked-lean"
  if [ ! -f .lake/gate-last-full ]; then reason=".lake/gate-last-full is missing"; return; fi
  local modified now
  if [ "$(uname -s)" = Darwin ]; then modified=$(stat -f %m .lake/gate-last-full)
  else modified=$(stat -c %Y .lake/gate-last-full); fi
  now=$(date +%s)
  if [ "$((now-modified))" -ge 86400 ] || [ "$modified" -gt "$now" ]; then
    reason=".lake/gate-last-full is older than 24 h or has a future date"; return
  fi
  tier=merge; reason="no full-tier changes; full PASS is less than 24 h old"
}
choose_tier
echo "tier: $(printf '%s' "$tier" | tr '[:lower:]' '[:upper:]') ($reason); slots=$GATE_SLOTS memory=$memory_limit"
echo "logs: $logs"
echo "reminder: run bash scripts/check-fg.sh on the Mac (research files required)"

# Do not put the step in an if/|| test: preserve errexit inside its functions.
step() (
  set +e
  name=$1; shift
  start=$(date +%s)
  (set -e; "$@") > "$logs/$name.log" 2>&1
  rc=$?
  end=$(date +%s)
  printf '%s %s\n' "$rc" "$((end-start))" > "$logs/$name.result"
)
summary() {
  local name=$1 rc wall
  read -r rc wall < "$logs/$name.result"
  echo "$name rc=$rc wall=${wall}s"
  if [ "$rc" -ne 0 ]; then
    failed=1
    cat "$logs/$name.log"
  fi
}
finish() {
  local cg peak
  # Peak memory of this gate's own cgroup (the MemoryMax scope on Linux).
  if [ -r /proc/self/cgroup ]; then
    cg=$(sed -n 's/^0:://p' /proc/self/cgroup)
    peak=$(cat "/sys/fs/cgroup$cg/memory.peak" 2>/dev/null) &&
      echo "memory.peak=$((peak / 1048576)) MiB (cgroup $cg)"
  fi
  if [ "$failed" -eq 0 ]; then
    if [ "$tier" = full ]; then touch .lake/gate-last-full; fi
    echo "GATE PASS tier=$tier slots=$GATE_SLOTS memory=$memory_limit wall=$(($(date +%s)-started))s"
  else
    echo "GATE FAIL tier=$tier slots=$GATE_SLOTS memory=$memory_limit wall=$(($(date +%s)-started))s"
  fi
}
build_all() {
  local targets
  targets=$(gate_with_slot lake env lean --run scripts/CheckGenFirst.lean --libraries)
  [ -n "$targets" ] || { echo "CheckGenFirst returned no build targets"; return 1; }
  # Build the full route-check scope before GATE_NO_BUILD is enabled.
  local route_targets
  route_targets=$(gate_with_slot lake env lean --run scripts/CheckFaultXRoute.lean --libraries) || return $?
  [ -n "$route_targets" ] || { echo "CheckFaultXRoute returned no build targets"; return 1; }
  targets="$targets $route_targets"
  # @ selects every default target of the root package, plus check support
  # and every module that CheckGenFirst scans (including facade orphans).
  GATE_NO_BUILD=0 gate_build --wfail @ AvailableChainCheckSupport $targets
}
step build build_all
summary build
if [ "$failed" -ne 0 ]; then finish; exit 1; fi
export GATE_NO_BUILD=1
# A caller's NEG/SKIP_CONE must not weaken the chosen tier or build checks.
export NEG=1 SKIP_CONE=0
if [ "$tier" = merge ]; then NEG=0; fi
checks=(check-build check-fgsa check-fgsa-run)
# Shared slots cap controls and heavy steps across all three scripts.
pids=()
for name in "${checks[@]}"; do step "$name" bash "scripts/$name.sh" & pids+=("$!"); done
for pid in "${pids[@]}"; do wait "$pid"; done
for name in "${checks[@]}"; do summary "$name"; done
step catalog-lock gate_with_slot lake env lean --run scripts/CatalogLock.lean --check
summary catalog-lock
step v2-manifest gate_with_slot lake env lean --run scripts/V2Manifest.lean --check
summary v2-manifest
step gen-manifest gate_with_slot lake env lean --run scripts/V2Manifest.lean --scope gen --check
summary gen-manifest
step fgsa-manifest gate_with_slot bash scripts/check-fgsa-manifest.sh
summary fgsa-manifest
step fgsa-claims gate_with_slot bash scripts/check-fgsa-claims.sh
summary fgsa-claims
audit() {
  local path=$1 out=$2 rc=0 count
  gate_with_slot lake env lean "$path" > "$out" 2>&1 || rc=$?
  cat "$out"
  count=$(grep -c sorryAx "$out" || :)
  echo "sorryAx = $count"
  [ "$rc" -eq 0 ] && [ "$count" = 0 ]
}
for lib in Generic FGSA FGSARun; do
  step "$lib-axioms" audit "AvailableChain$lib/Tests/Axioms.lean" "$logs/$lib.axioms"
  summary "$lib-axioms"
done
finish
exit "$failed"
