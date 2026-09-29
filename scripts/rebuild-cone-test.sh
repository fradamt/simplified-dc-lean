#!/usr/bin/env bash
# Check (c), BUILD §7.1 and §7.2 B0: rebuild-cone-test.sh <Module.Name> [<toolchain>]
#
# The primary build check: under the module system (`module`, `public import`,
# `@[expose] public section`, proofs not exported), a proof-only edit must
# rebuild exactly one module. The script works on a throwaway copy of the
# repository (default: the parent of scripts/; CONE_REPO overrides it):
#   1. the copy must be up to date (`lake build --no-build`), else exit 2;
#   2. it makes two proof-only edits in <Module.Name>: one line
#      `have coneProbe : True := trivial` at the start of the first tactic
#      proof (`:= by` at the end of a line) of a theorem, and a new
#      `private theorem` at the end of the file;
#   3. it waits for a free compile slot (fewer than 3 `lean.orig`; BUILD
#      §7.6), runs `lake build`, lists the rebuilt project modules, and
#      deletes the copy.
# Exit 0: exactly one module rebuilt (the edited one). Exit 1: more than one.
# Exit 2: usage error, baseline not built, or the edited build failed.
# <toolchain> (optional) runs `elan run <toolchain> lake`; the tree must be
# built with that toolchain. CONE_TARGETS (optional, space-separated lake
# targets) limits the baseline check and the build to those targets, for a
# tree that is green only in part; the default is the default targets. The
# edits add no axiom and use no `simp [f]` or `rw [f]`, so the equation-lemma
# and axiom triggers (BUILD §7.1) are out of scope here; check (d) covers
# them. Sketch: claude-files/a0/check-sketches/rebuild-cone-test.sh (S4).
set -euo pipefail
[ $# -ge 1 ] && [ $# -le 2 ] || { echo "usage: $0 <Module.Name> [<toolchain>]" >&2; exit 2; }
REPO=$(cd "${CONE_REPO:-$(dirname "$0")/..}" && pwd); MOD=$1; TC=${2:-}
LAKE=(lake); [ -n "$TC" ] && LAKE=(elan run "$TC" lake)
REL=${MOD//.//}.lean
[ -f "$REPO/$REL" ] || { echo "no file $REPO/$REL" >&2; exit 2; }
TMP=$(mktemp -d "${TMPDIR:-/tmp}/cone-test.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
# Throwaway copy. macOS/APFS: clone everything. Elsewhere: copy the tree and
# link the (already built, never written) package directory.
if cp -c -R "$REPO/." "$TMP/" 2>/dev/null; then :; else
  rm -rf "$TMP"/*; rsync -a --exclude .lake/packages --exclude .git "$REPO/" "$TMP/"
  mkdir -p "$TMP/.lake"; ln -s "$REPO/.lake/packages" "$TMP/.lake/packages"
fi
cd "$TMP"
"${LAKE[@]}" build --no-build ${CONE_TARGETS:-} >/dev/null 2>&1 || { echo "baseline: tree not built; run lake build first" >&2; exit 2; }
cp "$REL" "$TMP/.orig.lean"
python3 - "$REL" <<'PY'
import re, sys
p = sys.argv[1]; lines = open(p).read().split('\n')
decl = re.compile(r'^\s*(@\[[^\]]*\]\s*)?((private|protected)\s+)?(theorem|lemma)\b')
other = re.compile(r'^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable)\s+)*(def|abbrev|instance|structure|inductive|example|theorem|lemma)\b')
done = False; i = 0
while i < len(lines) and not done:
    if decl.match(lines[i]):
        j = i
        while j < len(lines):
            if j > i and other.match(lines[j]): break
            if lines[j].rstrip().endswith(':= by'):
                k = j + 1
                while k < len(lines) and not lines[k].strip(): k += 1
                if k < len(lines):
                    ind = re.match(r'\s*', lines[k]).group(0)
                    if len(ind) > len(re.match(r'\s*', lines[j]).group(0)) or ind:
                        lines.insert(j + 1, ind + 'have coneProbe : True := trivial')
                        done = True
                break
            j += 1
        i = j if j > i else i + 1
    else:
        i += 1
lines.append('')
lines.append('private theorem coneProbePrivate : True := trivial')
open(p, 'w').write('\n'.join(lines) + '\n')
print('edit: in-proof line ' + ('added' if done else 'NOT added (no tactic proof found)') + '; private theorem appended')
PY
# Wait for a free compile slot (3 machine-wide; the wrapper also throttles).
while [ "$(pgrep -x lean.orig | wc -l | tr -d ' ')" -ge 3 ]; do sleep 5; done
set +e
OUT=$("${LAKE[@]}" build ${CONE_TARGETS:-} 2>&1); RC=$?
set -e
cp "$TMP/.orig.lean" "$REL"
if [ $RC -ne 0 ]; then echo "$OUT" | grep -E '^error' | head -5; echo "edited build failed" >&2; exit 2; fi
BUILT=$(echo "$OUT" | sed -nE 's/.*Built ([A-Za-z0-9_.«»]+).*/\1/p' | while read -r m; do [ -f "${m//.//}.lean" ] && echo "$m"; done)
N=$(echo "$BUILT" | grep -c . || true)
echo "rebuilt $N module(s):"; echo "$BUILT" | sed 's/^/  /'
[ "$N" -eq 1 ] && { echo "PASS: a proof-only edit in $MOD rebuilt one module"; exit 0; }
echo "FAIL: a proof-only edit in $MOD rebuilt $N modules"; exit 1
