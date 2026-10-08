#!/usr/bin/env bash
# Run from the repository root. Freeze gates must use --tier full.
# The three check scripts run in parallel and share one GATE_SLOTS cap.
# check-fgsa-claims.sh runs alone after them: its lake calls are not slot-capped
# (NUC 2026-10-01: 282 s, peak 4.3 GiB; merge tier NEG=0 skips its compiled controls).
# Defaults: Mac 3, Linux 3 (scripts/gate-common.sh); env wins. JOBS is only a per-script pool bound.
# Linux requires a user scope with GATE_MEM (default 16G) and no swap; without it the gate refuses to run.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
gate_args=("$@")
tier=auto; base=; critical_path=0; attest_key=; attest_head=
usage() { echo "usage: bash scripts/gate.sh [--tier merge|full|auto] [--base <ref>] [--jobs N] | --critical-path"; }
while [ $# -gt 0 ]; do
  case "$1" in
    --attest-key)
      [ $# -ge 2 ] || { usage >&2; exit 2; }
      attest_key=$2; shift 2 ;;
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
if [ "${SOURCE_ONLY:-0}" != 0 ]; then
  echo 'GATE REFUSED: SOURCE_ONLY must be unset or 0' >&2
  exit 2
fi
# Signing is opt-in. The operator must keep the private key outside target code.
# Main trusts only keys in its committed full-pass-signers policy file.
if [ -n "$attest_key" ]; then
  [ "$tier" = full ] && [ -n "$base" ] && [ "$critical_path" = 0 ] || {
    echo 'FULL RECEIPT requires --tier full --base <policy-head>' >&2; exit 2;
  }
  [ -z "$(git status --porcelain --untracked-files=all)" ] || {
    echo 'FULL RECEIPT DIRTY TARGET' >&2; exit 2;
  }
  attest_head=$(git rev-parse HEAD)
fi
# Auto tier selection needs a base. Explicit tiers and critical-path mode
# use a base when the caller supplies one.
if [ -z "$base" ] && [ "$tier" = auto ] && [ "$critical_path" = 0 ]; then
  base=$(git merge-base main HEAD) || {
    echo "PRECHECK FAIL base; build not started" >&2
    exit 2
  }
fi
# Refuse a bad base before the Linux memory-scope probe as well.
if [ -n "$base" ]; then
  gate_precheck_step base gate_check_base "$base" || exit $?
fi
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
# FIRST gate step: no build, slot directory, logs or full-pass stamp yet.
gate_precheck "$base" || exit $?
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
export AUDIT_WORKERS=${AUDIT_WORKERS:-$((GATE_SLOTS < 2 ? GATE_SLOTS : 2))}
logs=$(mktemp -d "$PWD/.lake/gate-logs.XXXXXX")
started=$(date +%s)
failed=0

# Include both sides of renames. Also inspect local edits, since a gate may
# run before a commit. Use NUL delimiters for names and disable external diffs.
tier_path() {
  case "$1" in
    scripts/*|*allow*.txt|lakefile.toml|lean-toolchain|lake-manifest.json|Statements/*|*/Statements/*|docs/FGSA-API.md|docs/FGSA-API-frozen.md|docs/PCSA-API.md)
      reason="gate input changed: $1"; return 0 ;;
  esac
  return 1
}
choose_tier() {
  if [ "$tier" != auto ]; then reason="explicit --tier $tier"; return; fi
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
# Fail-fast: stop after the first failing sequential step.
stop_if_failed() {
  if [ "$failed" -ne 0 ]; then echo "fail-fast: later steps skipped"; finish; exit 1; fi
}
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
    if [ -n "$attest_key" ]; then
      python3 scripts/full-pass.py sign "$PWD" "$attest_head" "$base" "$logs" \
        "$attest_key" "$logs/full-pass.json" || return $?
    fi
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
# Every check step by name. Heavy steps share the gate slots (GATE_SLOTS cap).
run_check() {
  case "$1" in
    check-build|check-fgsa|check-fgsa-run) step "$1" bash "scripts/$1.sh" ;;
    catalog-lock) step "$1" gate_with_slot lake env lean --run scripts/CatalogLock.lean --check ;;
    v2-manifest) step "$1" gate_with_slot lake env lean --run scripts/V2Manifest.lean --check ;;
    gen-manifest) step "$1" gate_with_slot lake env lean --run scripts/V2Manifest.lean --scope gen --check ;;
    fgsa-manifest) step "$1" gate_with_slot bash scripts/check-fgsa-manifest.sh ;;
    pcsa-manifest) step "$1" gate_with_slot bash scripts/check-pcsa-manifest.sh ;;
    fgsa-claims) step "$1" gate_with_slot bash scripts/check-fgsa-claims.sh ;;
    *) echo "unknown gate step: $1" >&2; return 2 ;;
  esac
}
# Fail-fast group: the first failing step stops the others (their own process groups).
run_group() {
  if ! gate_parallel_failfast run_check "$logs" "$@"; then
    summary "$GATE_FF_FAILED"
    echo "fail-fast: $GATE_FF_FAILED failed; stopped:${GATE_FF_KILLED:- none}; later steps skipped"
    finish; exit 1
  fi
  local name
  for name in "$@"; do summary "$name"; done
}
tail_steps=(catalog-lock v2-manifest gen-manifest fgsa-manifest pcsa-manifest fgsa-claims)
if [ "$tier" = merge ]; then
  # Merge tier (NEG=0): no step writes the real tree, so the tail joins the
  # parallel group. The longest step goes first. Full tier: the controls write
  # the real tree (check-fgsa NegBuildC23, then lake build), and fgsa-claims
  # copies the built roots, so the tail stays sequential there. Claims controls
  # exceeded 7 GiB on the Mac. No new memory evidence supports overlap or more
  # than the measured two audit workers (U158/U160/U172).
  run_group fgsa-claims fgsa-manifest pcsa-manifest check-build check-fgsa check-fgsa-run \
    catalog-lock v2-manifest gen-manifest
else
  run_group check-build check-fgsa check-fgsa-run
  for name in "${tail_steps[@]}"; do
    run_check "$name"
    summary "$name"
    stop_if_failed
  done
fi
step check-fg-compose gate_with_slot bash scripts/check-fg-compose.sh
summary check-fg-compose
stop_if_failed
audit() {
  local path=$1 out=$2 rc=0 count
  gate_with_slot lake env lean "$path" > "$out" 2>&1 || rc=$?
  cat "$out"
  count=$(grep -c sorryAx "$out" || :)
  echo "sorryAx = $count"
  [ "$rc" -eq 0 ] && [ "$count" = 0 ]
}
# A strict audit: every `#print axioms` command has a result, and each result
# uses only propext, Classical.choice and Quot.sound.
audit_strict() {
  local path=$1 out=$2 want got bad
  audit "$path" "$out" || return 1
  want=$(grep -c '^#print axioms' "$path" 2>/dev/null); want=${want:-0}
  got=$(grep -c "depends on axioms: \[\|does not depend on any axioms" "$out" || :)
  bad=$(tr '\n' ' ' < "$out" | grep -o 'depends on axioms: \[[^]]*\]' | sed 's/.*\[//; s/\]$//' |
    tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -vxE 'propext|Classical\.choice|Quot\.sound' || :)
  if [ -n "$bad" ]; then echo "BAD AXIOMS: $(echo $bad)"; return 1; fi
  if [ "$got" != "$want" ]; then echo "AXIOM RESULTS: $got of $want commands"; return 1; fi
  echo "axioms: $got results; only propext, Classical.choice, Quot.sound"
}
# C14: keep required audit lines tied to their declaration's owning module.
step proof-audit-coverage gate_with_slot python3 scripts/check-proof-coverage.py
summary proof-audit-coverage
stop_if_failed
for lib in Generic FGSA FGSARun; do
  step "$lib-axioms" audit "AvailableChain$lib/Tests/Axioms.lean" "$logs/$lib.axioms"
  summary "$lib-axioms"
  stop_if_failed
done
step FGCompose-axioms audit AvailableChainFGCompose/Tests/Axioms.lean "$logs/FGCompose.axioms"
summary FGCompose-axioms
stop_if_failed
step FGSACompose-axioms audit AvailableChainFGSAProofs/Tests/FGCompose.lean "$logs/FGSACompose.axioms"
summary FGSACompose-axioms
stop_if_failed
step PCSACompose-axioms audit AvailableChainPCSAProofs/Tests/FGCompose.lean "$logs/PCSACompose.axioms"
summary PCSACompose-axioms
stop_if_failed
step FGSafety-axioms audit AvailableChainFGCompose/Tests/SafetyAxioms.lean "$logs/FGSafety.axioms"
summary FGSafety-axioms
stop_if_failed
step FGSASafety-axioms audit AvailableChainFGSAProofs/Tests/FGSafety.lean "$logs/FGSASafety.axioms"
summary FGSASafety-axioms
stop_if_failed
step PCSASafety-axioms audit AvailableChainPCSAProofs/Tests/FGSafety.lean "$logs/PCSASafety.axioms"
summary PCSASafety-axioms
stop_if_failed
# P13: the growth companion audit, the S0 freeze with its inherited-difference
# record, the public-source audit coverage of the safety modules, and the
# blueprint → Lean map (D10, compiled; FULL tier only).
step FGSAGrowth-axioms audit_strict AvailableChainFGSAProofs/Tests/WeakContinuationGrowthAssemblyAxioms.lean \
  "$logs/FGSAGrowth.axioms"
summary FGSAGrowth-axioms
stop_if_failed
step fg-finality-freeze python3 -B scripts/check-fg-finality-freeze.py --check
summary fg-finality-freeze
stop_if_failed
step fg-finality-coverage python3 -B scripts/check-fg-finality-coverage.py
summary fg-finality-coverage
stop_if_failed
if [ "$tier" = full ]; then
  step fgsa-blueprint gate_with_slot python3 -B scripts/check-fgsa-blueprint.py --check
  summary fgsa-blueprint
  stop_if_failed
fi
finish
exit "$failed"
