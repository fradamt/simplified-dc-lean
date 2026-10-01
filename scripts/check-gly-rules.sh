#!/usr/bin/env bash
# Check (i), BUILD §7.3: the GLY §F rules whose enforcement is a grep or a
# mechanical scan. The rules, their scopes and their baselines
# (scripts/baselines/check-gly-rules-<rule>.txt) are in
# scripts/check-gly-rules.py; this driver runs every rule.
# F-7 and F-10 compare with the base commit GLY_BASE (default 7ac5b0c).
# Usage: bash scripts/check-gly-rules.sh [--rule F-n]... [--list-legacy] [--write-baseline]
# Exit 0: no failing finding; 1: a failing finding; 2: an input error.
set -euo pipefail
cd "$(dirname "$0")/.."
# Keep the source/name rules and their compiled CheckGenFirst run first.
gly_source_rules() (
exec python3 scripts/check-gly-rules.py "$@"
)
source scripts/gate-common.sh

gly_faultx_route() {
  local targets
  targets=$(lake env lean --run scripts/CheckFaultXRoute.lean --libraries) || return $?
  [ -n "$targets" ] || { echo "CheckFaultXRoute returned no build targets" >&2; return 2; }
  gate_build $targets || return $?
  lake env lean --run scripts/CheckFaultXRoute.lean || return $?
  python3 scripts/check-faultx-route-controls.py
}

gly_checks() {
  local rc=0 route_rc=0 selected=0 route=0 arg
  gly_source_rules "$@" || rc=$?
  for arg in "$@"; do
    case "$arg" in
      --help|-h) return "$rc" ;;
      --rule|--rule=*) selected=1 ;;
    esac
    case "$arg" in F-24|--rule=F-24) route=1 ;; esac
  done
  if [ "$selected" = 0 ] || [ "$route" = 1 ]; then
    gly_faultx_route || route_rc=$?
  fi
  if [ "$rc" -ne 0 ]; then return "$rc"; fi
  return "$route_rc"
}

# check-build already holds a shared slot. gate_with_slot reuses that slot.
gate_with_slot gly_checks "$@"
