#!/usr/bin/env bash
# Shared gate functions. Bash 3.2 is sufficient. Source from the repo root.

gate_jobs() {
  # Default 3 on the Mac (its Lean wrapper caps the machine at LEAN_SLOTS, 3 by
  # default, and queues the rest), 6 on the NUC. JOBS from the environment wins.
  if [ "$(uname -s)" = Darwin ]; then JOBS=${JOBS:-3}; else JOBS=${JOBS:-6}; fi
  case "$JOBS" in
    ''|0*|*[!0-9]*) echo "JOBS must be a positive integer" >&2; return 2 ;;
  esac
}

gate_options() {
  NEG=${NEG:-1}
  while [ $# -gt 0 ]; do
    case "$1" in
      --no-negative) NEG=0 ;;
      *) echo "unknown option: $1" >&2; return 2 ;;
    esac
    shift
  done
  case "$NEG" in 0|1) ;; *) echo "NEG must be 0 or 1" >&2; return 2 ;; esac
  gate_jobs
}

# Every build in the gate uses this lock, including standalone check scripts.
# Linux uses flock; macOS uses an atomic directory because flock is not built in.
# GATE_NO_BUILD checks freshness without starting a build. The driver sets it
# only after one build of all default, support and CheckGenFirst targets.
gate_build() (
  mkdir -p .lake
  if command -v flock >/dev/null 2>&1; then
    if [ "${GATE_NO_BUILD:-0}" = 1 ]; then
      flock .lake/gate-build.lock lake build --no-build "$@"
    else
      flock .lake/gate-build.lock lake build "$@"
    fi
  else
    while ! mkdir .lake/gate-build.lock.d 2>/dev/null; do sleep 1; done
    trap 'rmdir .lake/gate-build.lock.d' EXIT
    trap 'exit 130' INT
    trap 'exit 143' TERM
    if [ "${GATE_NO_BUILD:-0}" = 1 ]; then
      lake build --no-build "$@"
    else
      lake build "$@"
    fi
  fi
)

# Each control has one subshell, scratch directory and log. Poll the job table
# to refill free slots without wait -n. Collect and print in submission order.
# Never call a control function in an if/|| test: that disables its set -e.
gate_pool_init() {
  pool_root=$1
  pool_pids=(); pool_logs=()
  mkdir -p "$pool_root"
}

gate_pool_add() {
  local running i dir
  while :; do
    running=$(jobs -pr | wc -l | tr -d ' ')
    [ "$running" -lt "$JOBS" ] && break
    sleep 1
  done
  i=${#pool_pids[@]}
  dir=$(mktemp -d "$pool_root/$1.XXXXXX")
  pool_logs[$i]=$dir/control.log
  (
    set -e
    neg=$dir
    "$@"
  ) > "$dir/control.log" 2>&1 &
  pool_pids[$i]=$!
}

gate_pool_wait() {
  local i rc first=0
  for ((i=0; i<${#pool_pids[@]}; i++)); do
    rc=0
    wait "${pool_pids[$i]}" || rc=$?
    cat "${pool_logs[$i]}"
    if [ "$rc" -ne 0 ] && [ "$first" -eq 0 ]; then first=$rc; fi
  done
  pool_pids=(); pool_logs=()
  return "$first"
}

# Serial controls form a barrier. They also get a private directory and log.
gate_control_serial() {
  gate_pool_wait || return $?
  gate_pool_add "$@"
  gate_pool_wait
}
