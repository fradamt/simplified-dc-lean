#!/usr/bin/env bash
# Fails if a .lean file of the two FG libraries uses the token native_decide
# outside a comment. Block comments /- … -/ and line comments -- are removed
# first (Lean block comments nest; the FG files do not nest them).
set -euo pipefail
cd "$(dirname "$0")/.."
files=$(find AvailableChainSimplexFG AvailableChainKitFG AvailableChainSimplexFG.lean \
  AvailableChainKitFG.lean -name '*.lean' 2>/dev/null || true)
[ -n "$files" ] || { echo "NO FILES"; exit 2; }
status=0
for f in $files; do
  if perl -0777 -pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$f" |
      grep -nE '(^|[^A-Za-z0-9_.])native_decide([^A-Za-z0-9_]|$)' >/dev/null; then
    echo "native_decide in $f"; status=1
  fi
done
exit $status
