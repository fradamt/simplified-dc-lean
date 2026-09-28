#!/usr/bin/env bash
# Checks the ELABORATED pin table of AvailableChainKitFG/Pins.lean against
# docs/FG-COMPOSITION.md. It builds the two FG libraries (the emitter reads
# the built .olean files, which Lean does not compare with the sources), runs
# scripts/FGPinIds.lean in this run and reads only its output. Threat model:
# the check guards against emitter and parser bugs, stale registry data, stale
# builds and superseded ids, not against a hand-edited manifest; so the
# manifest is never stored.
# 0) The emitter exits 0. Every record matches the strict grammar
#      src <key> <root> <path> <sha256> | <kind> <id>
#    (kind pin, ap, external or notFormalized). The last five lines are the
#    trailers "END <kind> <n> <sorted keys>" for src, pin, ap, external,
#    notFormalized, in this order. No (kind, key) pair repeats, for each
#    kind the sorted record keys are the trailer's keys, and no id is both a
#    pin and a notFormalized id. Else exit 2.
# 1) each src resolves to its REGISTERED version (tsc/: the archive copy by
#    hash; spec: the archived file; vc and dc: the registered Git commit), and
#    that version has the pinned hash;
# 2) each src (key, path, hash) is exactly the row of its key in the §0.1
#    tables (a continuation line counts only when its key column is blank);
# 3) each id is, literally, the id of an entry heading;
# 4) each id has exactly one row in the "## Index" table, and for pin, ap and
#    external ids the status there does not start with SUPERSEDED.
#    notFormalized ids are exempt from the status test (some are
#    historical, some are AP or comp ids that the module does not formalize).
# A failed build prints BUILD FAILED and exits 2.
# FGPINIDS=<file> runs another emitter script (the negative tests only).
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/.."
ETH=/Users/francesco/ethereum
REG=docs/FG-COMPOSITION.md
EMIT=${FGPINIDS:-scripts/FGPinIds.lean}
ID='[a-z][A-Za-z0-9.]*\.v[0-9]+'   # the registry's id grammar
KEY='[A-Za-z0-9]+'
ROOT='(tsc|spec|vc@b97b902|research@9f5ed71)'
FILE='[A-Za-z0-9._/-]+'
HASH='[0-9a-f]{64}'
resolve() {  # root path pinned-hash -> sha256 of the registered version
  local root=$1 path=$2 h=$3 f
  case $root in
    tsc) f="$ETH/research/async-resilient-committees/tip-stability/codex/archive/${path%.*}-${h:0:8}.${path##*.}"
         [ -f "$f" ] || return 1; shasum -a 256 "$f" | cut -c1-64 ;;
    spec) f="$ETH/research/async-resilient-committees/tip-stability/spec/$path"
          [ -f "$f" ] || return 1; shasum -a 256 "$f" | cut -c1-64 ;;
    vc@*) git -C "$ETH/lean/decoupled-consensus/verified-consensus" show "${root#vc@}:$path" 2>/dev/null |
            shasum -a 256 | cut -c1-64 ;;
    research@*) git -C "$ETH/research" show "${root#research@}:$path" 2>/dev/null |
            shasum -a 256 | cut -c1-64 ;;
    *) return 1 ;;
  esac
}
lake build AvailableChainSimplexFG AvailableChainKitFG >/dev/null 2>&1 ||
  { echo "BUILD FAILED"; exit 2; }
[ -s "$REG" ] || { echo "MISSING OR EMPTY: $REG"; exit 2; }
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
lake env lean --run "$EMIT" > "$tmp/out" || { echo "EMITTER FAILED (exit $?)"; exit 2; }
# 0) Grammar, trailers, duplicates and the bound record set.
n=$(wc -l < "$tmp/out" | tr -d ' ')
[ "$n" -gt 5 ] || { echo "NO END TRAILER (empty or truncated manifest)"; exit 2; }
head -n $((n - 5)) "$tmp/out" > "$tmp/body"
tail -n 5 "$tmp/out" > "$tmp/trail"
[ "$(cut -d' ' -f1,2 "$tmp/trail" | tr '\n' ' ')" = \
  "END src END pin END ap END external END notFormalized " ] ||
  { echo "NO END TRAILER (empty or truncated manifest)"; exit 2; }
bad=$(grep -Ev "^END (src|pin|ap|external|notFormalized) [0-9]+( [A-Za-z0-9.]+)*\$" \
  "$tmp/trail" || true)
[ -z "$bad" ] || { echo "MALFORMED TRAILER: $(printf '%s\n' "$bad" | head -1)"; exit 2; }
bad=$(grep -Ev "^(src $KEY $ROOT $FILE $HASH|(pin|ap|external|notFormalized) $ID)\$" \
  "$tmp/body" || true)
[ -z "$bad" ] || { echo "MALFORMED LINE: $(printf '%s\n' "$bad" | head -1)"; exit 2; }
dup=$(cut -d' ' -f1,2 "$tmp/body" | sort | uniq -d)
[ -z "$dup" ] || { echo "DUPLICATE: $(printf '%s\n' "$dup" | head -1)"; exit 2; }
for kind in src pin ap external notFormalized; do
  want=$(grep "^END $kind " "$tmp/trail" | cut -d' ' -f3-)
  have=$({ grep -c "^$kind " "$tmp/body" || true; grep "^$kind " "$tmp/body" |
    cut -d' ' -f2 | sort; } | tr '\n' ' ' | sed 's/ $//')
  [ "$want" = "$have" ] || { echo "TRAILER MISMATCH: $kind"; exit 2; }
done
both=$(comm -12 <(awk '$1 == "pin" { print $2 }' "$tmp/body" | sort) \
  <(awk '$1 == "notFormalized" { print $2 }' "$tmp/body" | sort))
[ -z "$both" ] ||
  { echo "PIN AND NOT FORMALIZED: $(printf '%s\n' "$both" | head -1)"; exit 2; }
nsrc=$(grep -c '^src ' "$tmp/body" || true)
npin=$(grep -c '^pin ' "$tmp/body" || true)
[ "$nsrc" -gt 0 ] && [ "$npin" -gt 0 ] || { echo "EMPTY TABLE: $nsrc sources, $npin pins"; exit 2; }
awk '$1 == "src" { print $2 "|" $3 "|" $4 "|" $5 }' "$tmp/body" > "$tmp/srcs"
awk '$1 != "src"' "$tmp/body" | sort -u > "$tmp/ids"
status=0
while IFS='|' read -r key root path pinned; do
  actual=$(resolve "$root" "$path" "$pinned") ||
    { echo "MISSING REGISTERED VERSION: $key $root $path"; status=1; continue; }
  [ "$pinned" = "$actual" ] ||
    { echo "CHANGED: $key $root/$path pinned $pinned actual $actual"; status=1; }
  # The exact §0.1 row of this key, plus a continuation line (blank key column).
  rows=$(K="$key" awk '/^### 0\.1 Sources/ { s = 1; next } /^### 0\.2/ { exit }
    s && index($0, "│ " ENVIRON["K"] " ") == 1 { n++ } END { print n + 0 }' "$REG")
  [ "$rows" -eq 1 ] || { echo "KEY NOT EXACTLY ONCE IN §0.1: $key ($rows)"; status=1; continue; }
  row=$(K="$key" awk '/^### 0\.1 Sources/ { s = 1; next } !s { next }
    found { if ($0 ~ /^│ +│/) print; exit }
    index($0, "│ " ENVIRON["K"] " ") == 1 { print; found = 1 }' "$REG")
  case $row in *"$(basename "$path")"*) ;; *) echo "PATH NOT IN §0.1 ROW: $key $path"; status=1 ;; esac
  case $row in *"${pinned:0:32}"*"${pinned:32:32}"*) ;; *) echo "HASH NOT IN §0.1 ROW: $key"; status=1 ;; esac
done < "$tmp/srcs"
while read -r tag id; do
  I="$id" awk 'index($0, "### `" ENVIRON["I"] "` ") == 1 { f = 1 } END { exit !f }' "$REG" ||
    { echo "NO REGISTRY ENTRY: $tag $id"; status=1; }
  # The id's row in the Index table (from "## Index" to the next "## ").
  idx=$(I="$id" awk '/^## Index/ { s = 1; next } /^## / { s = 0 }
    s && index($0, "│ " ENVIRON["I"] " ") == 1' "$REG")
  c=$(printf '%s' "$idx" | grep -c '^│' || true)
  [ "$c" -eq 1 ] || { echo "ID NOT EXACTLY ONCE IN INDEX: $tag $id ($c)"; status=1; continue; }
  [ "$tag" != notFormalized ] || continue
  st=$(printf '%s\n' "$idx" | awk -F'│' '{ gsub(/^ +| +$/, "", $4); print $4 }')
  case $st in SUPERSEDED*) echo "SUPERSEDED: $tag $id ($st)"; status=1 ;; esac
done < "$tmp/ids"
nref=$(grep -Ec '^(ap|external) ' "$tmp/ids" || true)
nnf=$(grep -c '^notFormalized ' "$tmp/ids" || true)
echo "checked $nsrc sources, $npin pin ids, $nref active references and $nnf not-formalized ids"
exit $status
