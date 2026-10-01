#!/usr/bin/env bash
# Run this checkout's source policy against a tracked copy of a worktree.
# Sources, lakefile and guard list data come from the target; checker code is ours.
# The temporary Git index uses the target HEAD. No worktree or build is created.
set -euo pipefail
if [ $# -ne 1 ]; then
  echo "usage: bash scripts/precheck.sh <worktree>" >&2
  exit 2
fi
main_root=$(cd "$(dirname "$0")/.." && pwd -P)
target_root=$(cd "$1" && pwd -P)
main_head=$(git -C "$main_root" rev-parse --verify HEAD)
target_head=$(git -C "$target_root" rev-parse --verify HEAD)
if [ "$(git -C "$target_root" rev-parse --show-toplevel)" != "$target_root" ]; then
  echo "precheck.sh: target must be a worktree root" >&2
  exit 2
fi

scratch=$(mktemp -d "${TMPDIR:-/tmp}/main-precheck.XXXXXX")
tree=$scratch/tree
check=copy
cleanup() {
  local rc=$?
  trap - EXIT
  if [ "$rc" -ne 0 ]; then
    echo "MAIN POLICY FAIL $check main=${main_head:0:7} target=${target_head:0:7}" >&2
  fi
  rm -rf "$scratch"
  exit "$rc"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
mkdir "$tree"
echo "main policy: main=${main_head:0:7} target=${target_head:0:7}"
# Copy tracked working files, so an uncommitted source edit is checked too.
# Do not copy target scripts, Git state, or build output.
git -C "$target_root" ls-files -z |
  rsync -a --from0 --files-from=- --exclude=/scripts --exclude=/.git --exclude=/.lake \
    "$target_root/" "$tree/"
rsync -a --exclude=__pycache__ --exclude='*.pyc' "$main_root/scripts/" "$tree/scripts/"

if [ -f "$target_root/scripts/check-fgsa-claims.sh" ]; then
  check=guard-lists
  echo '== precheck guard-lists'
  python3 "$main_root/scripts/guard-lists.py" superset \
    --main "$main_root/scripts/check-fgsa-claims.sh" \
    --target "$target_root/scripts/check-fgsa-claims.sh" \
    --allow "$target_root/scripts/guard-lists-allow.txt"
  python3 "$main_root/scripts/guard-lists.py" merge \
    --code "$main_root/scripts/check-fgsa-claims.sh" \
    --data "$target_root/scripts/check-fgsa-claims.sh" \
    --out "$tree/scripts/check-fgsa-claims.sh"
  # The gate repeats the superset check against Git history in the policy copy.
  if [ -f "$target_root/scripts/guard-lists-allow.txt" ]; then
    cp "$target_root/scripts/guard-lists-allow.txt" "$tree/scripts/guard-lists-allow.txt"
  fi
fi

# GLY F-7/F-10 read Git history. Use read-only object stores with a private
# index and refs, instead of adding a worktree to either checkout.
check=git-snapshot
target_objects=$(cd "$target_root" && cd "$(git rev-parse --git-path objects)" && pwd -P)
main_objects=$(cd "$main_root" && cd "$(git rev-parse --git-path objects)" && pwd -P)
git init -q "$tree"
printf '%s\n%s\n' "$target_objects" "$main_objects" > "$tree/.git/objects/info/alternates"
git -C "$tree" read-tree "$target_head"
git -C "$tree" update-ref HEAD "$target_head"

check=precheck
rc=0
(
  cd "$tree"
  source scripts/gate-common.sh
  gate_precheck "$main_head"
) > "$scratch/precheck.log" 2>&1 || rc=$?
cat "$scratch/precheck.log"
if [ "$rc" -ne 0 ]; then
  check=$(sed -n 's/^PRECHECK FAIL \(.*\); build not started$/\1/p' "$scratch/precheck.log")
  check=${check:-precheck}
  exit "$rc"
fi
echo "MAIN POLICY PASS main=${main_head:0:7} target=${target_head:0:7}"
