#!/usr/bin/env bash
# Checks the ELABORATED pin table of AvailableChainKitFG/Pins.lean against
# docs/FG-COMPOSITION.md. It builds the two FG libraries (the emitter reads
# the built .olean files, which Lean does not compare with the sources), runs
# scripts/FGPinIds.lean in this run and reads only its output. Threat model:
# the check guards against emitter and parser bugs, stale registry data, stale
# builds and superseded or withdrawn ids, not against a hand-edited manifest;
# so the manifest is never stored.
# 0) The emitter exits 0. Every record matches the strict grammar
#      src <key> <root> <path> <sha256> | <kind> <id> | dep <pin> <id>
#    (kind pin, ap, external, notFormalized or hist). The last seven lines are
#    the trailers "END <kind> <n> <sorted keys>" for src, pin, ap, external,
#    notFormalized, dep, hist, in this order (the key of a dep record is
#    <pin>/<id>). No (kind, key) pair repeats (a repeated hist line fails), for
#    each kind the sorted record keys are the trailer's keys, no id is both a
#    pin and a notFormalized id, every hist id and the first id of every dep
#    record is a pin id, and the dep targets are exactly the ap and external
#    ids. Else exit 2.
# 1) each src resolves to its REGISTERED version (tsc/: the archive copy by
#    hash; spec and blueprint: the archived file; vc and dc: the registered Git
#    commit), and
#    that version has the pinned hash;
# 2) each src (key, path, hash) is exactly the row of its key in the §0.1
#    tables (a continuation line counts only when its key column is blank);
# 3) each id is, literally, the id of an entry heading;
# 4) each id has exactly one row in the "## Index" table. An id NAMED BY A
#    CURRENT PIN (a pin that is not a hist pin: its own id, and each id of a
#    dep record of it) must not have a status there that starts with
#    SUPERSEDED or WITHDRAWN. Ids that only hist pins name are exempt, and so
#    are notFormalized ids (some are historical, some are AP or comp ids that
#    the module does not formalize). Direct dep edges suffice: in Pins.lean
#    (the Cov type) only .ap and .external carry an id. A dep on another pin
#    is an .external id: if that pin is a hist pin, its own WITHDRAWN or
#    SUPERSEDED status fails here; if it is current, its own deps are checked
#    as a current pin's deps. So no transitive closure is needed.
# 5) the hist pins are exactly the ids of the allowlist HIST below. Each
#    allowlist entry has an id, a date and a reason. A hist pin with no
#    allowlist entry fails; an allowlist entry with no hist record fails.
# A failed build prints BUILD FAILED and exits 2.
# `leanIn` names (constants of a library above the FG libraries) are not in
# the manifest. The emitter fails in step 0 when a `leanIn` library is not on
# its allowlist; scripts/check-fgsa.sh checks the names themselves. The pin
# gate for a pin with `leanIn` evidence is check-fg.sh plus check-fgsa.sh.
# Negative tests only: FGPINIDS=<file> runs another emitter script,
# FGREG=<file> reads another registry, FGHISTALLOW=<file> reads another
# allowlist (scripts/check-fg.sh runs these controls).
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/.."
ETH=/Users/francesco/ethereum
REG=${FGREG:-docs/FG-COMPOSITION.md}
# The allowlist of hist pins, one per line: <id> <date YYYY-MM-DD> <reason>.
HIST='
fj.frame.v3 2026-09-29 WITHDRAWN for current use, r212/r213; successor fj.frame.v4
fg.finalLock.v1 2026-09-29 WITHDRAWN for current use, r212/r213; successor fg.finalLock.v2
fj.twoChanges.core.v1 2026-09-29 WITHDRAWN for current use, r212/r213; successor fj.twoChanges.core.v2
'
[ -z "${FGHISTALLOW:-}" ] || HIST=$(cat "$FGHISTALLOW")
EMIT=${FGPINIDS:-scripts/FGPinIds.lean}
ID='[a-z][A-Za-z0-9.]*\.v[0-9]+'   # the registry's id grammar
KEY='[A-Za-z0-9]+'
ROOT='(tsc|spec|blueprint|vc@b97b902|research@9f5ed71)'
FILE='[A-Za-z0-9._/-]+'
HASH='[0-9a-f]{64}'
resolve() {  # root path pinned-hash -> sha256 of the registered version
  local root=$1 path=$2 h=$3 f
  case $root in
    tsc) f="$ETH/research/async-resilient-committees/tip-stability/codex/archive/${path%.*}-${h:0:8}.${path##*.}"
         [ -f "$f" ] || return 1; shasum -a 256 "$f" | cut -c1-64 ;;
    spec) f="$ETH/research/async-resilient-committees/tip-stability/spec/$path"
          [ -f "$f" ] || return 1; shasum -a 256 "$f" | cut -c1-64 ;;
    blueprint) f="$ETH/research/async-resilient-committees/tip-stability/blueprint/$path"
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
KINDS='src pin ap external notFormalized dep hist'
n=$(wc -l < "$tmp/out" | tr -d ' ')
[ "$n" -gt 7 ] || { echo "NO END TRAILER (empty or truncated manifest)"; exit 2; }
head -n $((n - 7)) "$tmp/out" > "$tmp/body"
tail -n 7 "$tmp/out" > "$tmp/trail"
[ "$(cut -d' ' -f1,2 "$tmp/trail" | tr '\n' ' ')" = "$(printf 'END %s ' $KINDS)" ] ||
  { echo "NO END TRAILER (empty or truncated manifest)"; exit 2; }
bad=$(grep -Ev "^END (${KINDS// /|}) [0-9]+( [A-Za-z0-9./]+)*\$" "$tmp/trail" || true)
[ -z "$bad" ] || { echo "MALFORMED TRAILER: $(printf '%s\n' "$bad" | head -1)"; exit 2; }
bad=$(grep -Ev "^(src $KEY $ROOT $FILE $HASH|(pin|ap|external|notFormalized|hist) $ID|dep $ID $ID)\$" \
  "$tmp/body" || true)
[ -z "$bad" ] || { echo "MALFORMED LINE: $(printf '%s\n' "$bad" | head -1)"; exit 2; }
# The record key: the second field, or <pin>/<id> for a dep record.
awk '{ print $1, ($1 == "dep" ? $2 "/" $3 : $2) }' "$tmp/body" > "$tmp/keys"
dup=$(sort "$tmp/keys" | uniq -d)
[ -z "$dup" ] || { echo "DUPLICATE: $(printf '%s\n' "$dup" | head -1)"; exit 2; }
for kind in $KINDS; do
  want=$(grep "^END $kind " "$tmp/trail" | cut -d' ' -f3-)
  have=$({ grep -c "^$kind " "$tmp/keys" || true; { grep "^$kind " "$tmp/keys" || true; } |
    cut -d' ' -f2 | sort; } | tr '\n' ' ' | sed 's/ $//')
  [ "$want" = "$have" ] || { echo "TRAILER MISMATCH: $kind"; exit 2; }
done
awk '$1 == "pin" { print $2 }' "$tmp/body" | sort > "$tmp/pins"
bad=$(comm -23 <(awk '$1 == "hist" { print $2 }' "$tmp/body" | sort) "$tmp/pins")
[ -z "$bad" ] || { echo "HIST ID NOT A PIN ID: $(printf '%s\n' "$bad" | head -1)"; exit 2; }
bad=$(comm -23 <(awk '$1 == "dep" { print $2 }' "$tmp/body" | sort -u) "$tmp/pins")
[ -z "$bad" ] || { echo "DEP OF NO PIN: $(printf '%s\n' "$bad" | head -1)"; exit 2; }
[ "$(awk '$1 == "dep" { print $3 }' "$tmp/body" | sort -u)" = \
  "$(awk '$1 == "ap" || $1 == "external" { print $2 }' "$tmp/body" | sort -u)" ] ||
  { echo "DEP TARGETS ARE NOT THE AP AND EXTERNAL IDS"; exit 2; }
both=$(comm -12 <(awk '$1 == "pin" { print $2 }' "$tmp/body" | sort) \
  <(awk '$1 == "notFormalized" { print $2 }' "$tmp/body" | sort))
[ -z "$both" ] ||
  { echo "PIN AND NOT FORMALIZED: $(printf '%s\n' "$both" | head -1)"; exit 2; }
nsrc=$(grep -c '^src ' "$tmp/body" || true)
npin=$(grep -c '^pin ' "$tmp/body" || true)
[ "$nsrc" -gt 0 ] && [ "$npin" -gt 0 ] || { echo "EMPTY TABLE: $nsrc sources, $npin pins"; exit 2; }
awk '$1 == "src" { print $2 "|" $3 "|" $4 "|" $5 }' "$tmp/body" > "$tmp/srcs"
awk '$1 ~ /^(pin|ap|external|notFormalized)$/' "$tmp/body" | sort -u > "$tmp/ids"
# The ids named by a current pin, as "<id> <pin>": each pin that is not a hist
# pin names itself and the targets of its dep records.
awk '$1 == "hist" { h[$2] = 1; next }
  $1 == "pin" { p[$2] = 1; next }
  $1 == "dep" { d[++n] = $2 " " $3 }
  END { for (i in p) if (!(i in h)) print i, i
        for (k = 1; k <= n; k++) { split(d[k], f, " ")
          if (!(f[1] in h)) print f[2], f[1] } }' "$tmp/body" | sort -u > "$tmp/named"
status=0
tested=''
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
  # One status test per id (an id can be both a pin and an external id).
  case " $tested " in *" $id "*) continue ;; esac
  tested="$tested $id"
  st=$(printf '%s\n' "$idx" | awk -F'│' '{ gsub(/^ +| +$/, "", $4); print $4 }')
  case $st in
    SUPERSEDED*|WITHDRAWN*)
      for p in $(awk -v i="$id" '$1 == i { print $2 }' "$tmp/named"); do
        echo "NOT CURRENT: $id ($st), named by the current pin $p"; status=1
      done ;;
  esac
done < "$tmp/ids"
# 5) The hist pins and the allowlist.
printf '%s\n' "$HIST" | awk 'NF' > "$tmp/allow"
bad=$(grep -Ev "^$ID [0-9]{4}-[0-9]{2}-[0-9]{2} [^ ].*\$" "$tmp/allow" || true)
[ -z "$bad" ] || { echo "MALFORMED ALLOWLIST ENTRY: $(printf '%s\n' "$bad" | head -1)"; status=1; }
awk '{ print $1 }' "$tmp/allow" | sort > "$tmp/allowIds"
dup=$(uniq -d "$tmp/allowIds")
[ -z "$dup" ] || { echo "DUPLICATE ALLOWLIST ENTRY: $(printf '%s\n' "$dup" | head -1)"; status=1; }
awk '$1 == "hist" { print $2 }' "$tmp/body" | sort > "$tmp/hist"
for i in $(comm -23 "$tmp/hist" <(sort -u "$tmp/allowIds")); do
  echo "HIST PIN NOT ON THE ALLOWLIST: $i"; status=1
done
for i in $(comm -13 "$tmp/hist" <(sort -u "$tmp/allowIds")); do
  echo "ALLOWLIST ENTRY WITHOUT A HIST RECORD: $i"; status=1
done
nref=$(grep -Ec '^(ap|external) ' "$tmp/ids" || true)
nnf=$(grep -c '^notFormalized ' "$tmp/ids" || true)
ndep=$(grep -c '^dep ' "$tmp/body" || true)
nhist=$(grep -c '^hist ' "$tmp/body" || true)
echo "checked $nsrc sources, $npin pin ids ($nhist historical), $nref active references, \
$ndep dependency edges and $nnf not-formalized ids"
exit $status
