#!/usr/bin/env bash
# Shared gate functions. Bash 3.2 is sufficient. Source from the repo root.

gate_jobs() {
  # JOBS is a per-script pool bound: default 3 on Mac, 6 on Linux; env wins.
  # It is not machine concurrency. GATE_SLOTS caps all shared heavy steps.
  if [ "$(uname -s)" = Darwin ]; then JOBS=${JOBS:-3}; else JOBS=${JOBS:-6}; fi
  case "$JOBS" in
    ''|0*|*[!0-9]*) echo "JOBS must be a positive integer" >&2; return 2 ;;
  esac
}

gate_slots_init() {
  # One directory per gate, or per standalone check. All children share it.
  # GATE_SLOTS from the environment wins: default 3 on Mac, 3 on Linux (NUC: raise only from a measured peak RSS; peak x slots <= 15 GB).
  if [ "$(uname -s)" = Darwin ]; then GATE_SLOTS=${GATE_SLOTS:-3}
  else GATE_SLOTS=${GATE_SLOTS:-3}; fi
  case "$GATE_SLOTS" in
    ''|0*|*[!0-9]*) echo "GATE_SLOTS must be a positive integer" >&2; return 2 ;;
  esac
  if [ -z "${GATE_SLOT_DIR:-}" ]; then
    mkdir -p .lake || return $?
    GATE_SLOT_DIR=$(mktemp -d "$PWD/.lake/gate-slots.XXXXXX") || return $?
  fi
  mkdir -p "$GATE_SLOT_DIR" || return $?
  export GATE_SLOTS GATE_SLOT_DIR
}

gate_slot_release() {
  if [ -n "${gate_slot:-}" ]; then
    # Removing the PID directory claims the release. Only its remover may
    # remove the slot, so two stale-slot readers cannot remove a new owner.
    if rmdir "$gate_slot/owner.$gate_owner" 2>/dev/null; then
      rmdir "$gate_slot" 2>/dev/null || :
    fi
  fi
}

gate_slot_acquire() {
  local k slot owner pid
  # $$ is the parent PID in a Bash subshell. Bash 3.2 has no BASHPID.
  gate_owner=${BASHPID:-$(exec sh -c 'echo "$PPID"')}
  gate_slot=
  trap 'gate_slot_release' EXIT
  trap 'exit 130' INT
  trap 'exit 143' TERM
  while :; do
    for ((k=1; k<=GATE_SLOTS; k++)); do
      slot=$GATE_SLOT_DIR/slot.$k
      if mkdir "$slot" 2>/dev/null; then
        gate_slot=$slot
        mkdir "$slot/owner.$gate_owner" || return $?
        return 0
      fi
      for owner in "$slot"/owner.*; do
        [ -d "$owner" ] || continue
        pid=${owner##*.}
        case "$pid" in ''|0*|*[!0-9]*) continue ;; esac
        if ! kill -0 "$pid" 2>/dev/null; then
          if rmdir "$owner" 2>/dev/null; then rmdir "$slot" 2>/dev/null || :; fi
        fi
      done
      # An ownerless slot can be between mkdir and PID publication. Keep it
      # occupied: a timeout must not remove a delayed live holder's slot.
    done
    sleep 0.1
  done
}

# The subshell owns one slot until the entire command or function exits.
# Do not use this function in an if/|| test when the command needs set -e.
gate_with_slot() (
  # Nested check drivers share the caller's slot, including with GATE_SLOTS=1.
  if [ "${GATE_SLOT_HELD:-0}" = 1 ]; then "$@"; exit $?; fi
  gate_slots_init || exit $?
  gate_slot_acquire || exit $?
  export GATE_SLOT_HELD=1
  "$@"
)

# A signal exit, or a failure with empty output, is not a valid rejection.
gate_control_check() {
  if [ "$2" -ge 128 ] || { [ "$2" -ne 0 ] && [ -z "$3" ]; }; then
    echo "CONTROL KILLED (rc $2): $1"
    return 1
  fi
  return 0
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
  gate_slots_init
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

# Each control has one shared slot for its whole run, scratch directory and
# log. JOBS bounds this script's jobs, including those waiting for a slot.
# Poll without wait -n. Collect and print in submission order.
# Never call a control function in an if/|| test: that disables its set -e.
gate_pool_init() {
  pool_root=$1
  pool_pids=(); pool_logs=(); pool_names=()
  gate_slots_init
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
  pool_names[$i]=$1
  (
    set -e
    neg=$dir
    gate_with_slot "$@"
  ) > "$dir/control.log" 2>&1 &
  pool_pids[$i]=$!
}

gate_pool_wait() {
  local i rc first=0
  for ((i=0; i<${#pool_pids[@]}; i++)); do
    rc=0
    wait "${pool_pids[$i]}" || rc=$?
    cat "${pool_logs[$i]}"
    # rc 0 with no output is a valid pass (a merge-tier positive-only check).
    if [ "$rc" -ge 128 ] || { [ "$rc" -ne 0 ] && [ ! -s "${pool_logs[$i]}" ]; }; then
      echo "CONTROL KILLED (rc $rc): ${pool_names[$i]}"
      if [ "$rc" -eq 0 ]; then rc=1; fi
    fi
    if [ "$rc" -ne 0 ] && [ "$first" -eq 0 ]; then first=$rc; fi
  done
  pool_pids=(); pool_logs=(); pool_names=()
  return "$first"
}

# Serial controls form a barrier. They also get a private directory and log.
gate_control_serial() {
  gate_pool_wait || return $?
  gate_pool_add "$@"
  gate_pool_wait
}
