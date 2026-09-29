#!/usr/bin/env bash
# FGSA checks: build (--wfail), root imports, native evaluation outside
# comments, the direct-import allowlist with its directory rules, the Q1/Q5
# boundary grep, the axiom check (with build coverage and the import-closure
# check), the lease-instance check, and the negative controls of these checks.
# Import headers are parsed after comment removal (G13 Astra M2, Opus m1).
# Run: bash scripts/check-fgsa.sh. Exit 0 when every check passes.
set -euo pipefail
cd "$(dirname "$0")/.."
for f in scripts/CheckFGSAAxioms.lean scripts/CheckFGSALease.lean; do
  [ -f "$f" ] || { echo "MISSING CHECK SCRIPT: $f"; exit 2; }
done

# Remove comments with a small tokenizer that knows strings, character
# literals, raw strings (r"...", r#"..."#) and nested block comments. A "--"
# in a string does not start a comment, and a "/-" in a line comment does not
# open a block comment.
strip_comments='
  local $/; my $s = <STDIN>; my $o = ""; my $d = 0;
  while ((pos($s) // 0) < length $s) {
    if ($d > 0) {
      if    ($s =~ /\G\/-/gc)   { $d++ }
      elsif ($s =~ /\G-\//gc)   { $d--; $o .= " " }
      elsif ($s =~ /\G(\n)/gc)  { $o .= $1 }
      else                      { $s =~ /\G./gcs }
    }
    elsif ($s =~ /\G--[^\n]*/gc)                         { }
    elsif ($s =~ /\G\/-/gc)                              { $d = 1 }
    elsif ($s =~ /\Gr(#*)".*?"\1/gcs)                    { $o .= "\"\"" }
    elsif ($s =~ /\G"(?:\\.|[^"\\])*"/gcs)               { $o .= "\"\"" }
    elsif ($s =~ /\G([\w\p{N}.!?][\w\p{N}.!?\x27]*)/gc)  { $o .= $1 }
    elsif ($s =~ /\G\x27(?:\\.|[^\\\x27])\x27/gc)        { $o .= "c" }
    else                                                 { $s =~ /\G(.)/gcs; $o .= $1 }
  }
  print $o;'
# The modules of the import header of a file, one per line, after comment
# removal: [module] then [public] [meta] import [all] <Name>, any whitespace.
header_imports='
  local $/; my $s = <STDIN>;
  $s =~ s/^\s+//; $s =~ s/^module\s+//;
  while ($s =~ s/^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][A-Za-z0-9_.]*)\s*//) {
    print "$1\n";
  }'
imports_of() { perl -CSD -e "$strip_comments" < "$1" | perl -CSD -e "$header_imports"; }

# Root imports under base directory $1: every source file is a root import.
check_root_imports() {
  local base=$1 missing
  missing=$(comm -23 \
    <(cd "$base" && find AvailableChainFGSA -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort) \
    <(imports_of "$base/AvailableChainFGSA.lean" | sort))
  [ -z "$missing" ] || { echo "NOT IMPORTED BY THE ROOT: $missing"; return 1; }
}

# The direct-import allowlist (plan, Global Constraints "Imports") under base
# directory $1. Internal imports follow the layers: Model/ imports Model/;
# Statements/ imports Model/ and Statements/; Proofs/ imports Model/,
# Statements/ and Proofs/; Tests/ and the root import any FGSA module. The root
# imports only FGSA modules. External: AvailableChainModel.*,
# AvailableChainGridCO.Model.Protocol, AvailableChainSA.Model.Protocol,
# AvailableChainSimplexFG.*, Mathlib.*; AvailableChainGridCO.Proofs.* only in
# Proofs/; AvailableChainKitFG.* only in Statements/ and Proofs/.
check_direct_imports() {
  local base=$1 bad=0 f rel layer m
  for f in $(cd "$base" && find AvailableChainFGSA -name '*.lean' | sort) AvailableChainFGSA.lean; do
    rel=${f#AvailableChainFGSA/}
    if [ "$f" = AvailableChainFGSA.lean ]; then layer=root; else layer=${rel%%/*}; fi
    for m in $(imports_of "$base/$f"); do
      case "$layer:$m" in
        root:AvailableChainFGSA.*|Tests:AvailableChainFGSA.*) continue ;;
        Model:AvailableChainFGSA.Model.*) continue ;;
        Statements:AvailableChainFGSA.Model.*|Statements:AvailableChainFGSA.Statements.*) continue ;;
        Proofs:AvailableChainFGSA.Model.*|Proofs:AvailableChainFGSA.Statements.*) continue ;;
        Proofs:AvailableChainFGSA.Proofs.*) continue ;;
        root:*) ;;
        Model:*|Statements:*|Proofs:*|Tests:*)
          case "$m" in
            AvailableChainFGSA.*) ;;
            AvailableChainModel.*|AvailableChainGridCO.Model.Protocol) continue ;;
            AvailableChainSA.Model.Protocol|AvailableChainSimplexFG.*|Mathlib.*) continue ;;
            AvailableChainGridCO.Proofs.*) [ "$layer" = Proofs ] && continue ;;
            AvailableChainKitFG.*)
              { [ "$layer" = Statements ] || [ "$layer" = Proofs ]; } && continue ;;
          esac ;;
      esac
      echo "IMPORT NOT ALLOWED: $f imports $m"; bad=1
    done
  done
  return $bad
}

# Q1/Q5 boundary (plan, Global Constraints) on comment-free text.
check_boundary() {
  local base=$1 bad=0 f
  for f in $(cd "$base" && find AvailableChainFGSA -name '*.lean') AvailableChainFGSA.lean; do
    if perl -CSD -e "$strip_comments" < "$base/$f" |
        grep -nE 'ProtocolSpec|Generic\.Run|(^|[^A-Za-z0-9_])(Run|Env)([^A-Za-z0-9_]|$)|World|Interface|Claims|pendingRow'; then
      echo "ENGINE REFERENCE in $f"; bad=1
    fi
  done
  return $bad
}

echo "== lake build --wfail AvailableChainFGSA"
lake build --wfail AvailableChainFGSA
echo "== root imports"
check_root_imports . || exit 2
echo "== native evaluation"
status=0
for f in $(find AvailableChainFGSA -name '*.lean') AvailableChainFGSA.lean; do
  if perl -CSD -e "$strip_comments" < "$f" |
      grep -nE '(^|[^A-Za-z0-9_.])native_decide([^A-Za-z0-9_]|$)|\+native|native := true|ofReduceBool|ofReduceNat' >/dev/null; then
    echo "native evaluation in $f"; status=1
  fi
done
[ $status -eq 0 ] || exit 1
echo "== direct imports"
check_direct_imports . || exit 1
echo "== Q1/Q5 boundary"
check_boundary . || exit 1
echo "== axioms, build coverage, import closure"
lake env lean --run scripts/CheckFGSAAxioms.lean
echo "== lease instances"
lake env lean --run scripts/CheckFGSALease.lean

echo "== negative controls"
neg=$(mktemp -d "$PWD/.lake/fgsa-neg.XXXXXX")
trap 'rm -rf "$neg"' EXIT
# expect_fail NAME CODE OUT PATTERN...: the check failed with CODE and printed
# every PATTERN (fixed strings).
expect_fail() {
  local name=$1 code=$2 out=$3 p; shift 3
  if [ "$code" -eq 0 ]; then echo "$out"; echo "NEGATIVE CONTROL NOT DETECTED: $name"; exit 1; fi
  for p in "$@"; do
    if ! printf '%s\n' "$out" | grep -qF -- "$p"; then
      echo "$out"; echo "NEGATIVE CONTROL $name: missing \"$p\""; exit 1
    fi
  done
  echo "rejected, as expected: $name"
}
# A scratch copy of the source tree for the import controls.
mk_tree() { rm -rf "$neg/tree"; mkdir -p "$neg/tree"; cp -R AvailableChainFGSA AvailableChainFGSA.lean "$neg/tree/"; }
run() { set +e; out=$("$@" 2>&1); code=$?; set -e; }

mk_tree
printf 'module\npublic import AvailableChainLStar.Model.Protocol\n' > "$neg/tree/AvailableChainFGSA/Model/NegA.lean"
echo 'public import AvailableChainFGSA.Model.NegA' >> "$neg/tree/AvailableChainFGSA.lean"
run check_direct_imports "$neg/tree"
expect_fail "unlisted library" $code "$out" \
  "IMPORT NOT ALLOWED: AvailableChainFGSA/Model/NegA.lean imports AvailableChainLStar.Model.Protocol"

mk_tree
printf 'module\npublic import AvailableChainKitFG.Correspondence\n' > "$neg/tree/AvailableChainFGSA/Model/NegB.lean"
printf 'module\npublic import AvailableChainFGSA.Proofs.Carrier\n' > "$neg/tree/AvailableChainFGSA/Statements/NegB.lean"
run check_direct_imports "$neg/tree"
expect_fail "wrong-layer import" $code "$out" \
  "IMPORT NOT ALLOWED: AvailableChainFGSA/Model/NegB.lean imports AvailableChainKitFG.Correspondence" \
  "IMPORT NOT ALLOWED: AvailableChainFGSA/Statements/NegB.lean imports AvailableChainFGSA.Proofs.Carrier"

mk_tree
printf 'module\npublic import /- dependency -/ AvailableChainFramework.Profile\npublic\n  import\n  AvailableChainSAPC.Model.Choice\n' \
  > "$neg/tree/AvailableChainFGSA/Proofs/NegC.lean"
run check_direct_imports "$neg/tree"
expect_fail "import after a comment and a line break" $code "$out" \
  "imports AvailableChainFramework.Profile" "imports AvailableChainSAPC.Model.Choice"

mk_tree
printf 'module\n@[expose] public section\ntheorem negOrphan : False := sorry\nend\n' \
  > "$neg/tree/AvailableChainFGSA/Tests/NegOrphan.lean"
echo '/- public import AvailableChainFGSA.Tests.NegOrphan -/' >> "$neg/tree/AvailableChainFGSA.lean"
run check_root_imports "$neg/tree"
expect_fail "orphan module behind a commented import (root check)" $code "$out" \
  "NOT IMPORTED BY THE ROOT: AvailableChainFGSA.Tests.NegOrphan"

# The compiled checks: the orphan file (with a sorry) against the build, and a
# forbidden library in the import closure.
cat > "$neg/FGSAClosureNeg.lean" <<'LEAN'
import AvailableChainSAPC.Model.Choice
LEAN
lake env lean -o "$neg/FGSAClosureNeg.olean" "$neg/FGSAClosureNeg.lean"
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSAAxioms.lean --root FGSAClosureNeg --files "$0/tree/AvailableChainFGSA"' "$neg"
expect_fail "orphan module and forbidden closure (axiom script)" $code "$out" \
  "NOT IN THE BUILD: AvailableChainFGSA.Tests.NegOrphan" \
  "FORBIDDEN LIBRARY IN THE IMPORT CLOSURE: AvailableChainSAPC"

# Lease controls: a direct default-instance call; an alias wrapper with its own
# policy parameter in another namespace (Astra M1); a generic wrapper whose
# policy binder has an alias type (Opus m2); an imported wrapper that fixes the
# default instance inside.
cat > "$neg/FGSALeaseNeg.lean" <<'LEAN'
import AvailableChainFGSA
namespace AvailableChain.FGSA
/-- A GridCO gate at the default instance `gridLeasePolicy`. -/
def leaseNegControl (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  GridCO.gate p st r
end AvailableChain.FGSA
namespace AvailableChain.LeaseAuditAlias
def gate (_policy : GridCO.LeasePolicy) (p : GridCO.Params)
    (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  @GridCO.gate GridCO.gridLeasePolicy p 1 st r
end AvailableChain.LeaseAuditAlias
namespace AvailableChain.FGSA
def badGate (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  AvailableChain.LeaseAuditAlias.gate GridCO.slowLeasePolicy p st r
end AvailableChain.FGSA
namespace AvailableChain.GridCO
abbrev PolicyAlias : Type := LeasePolicy
def sneakyGate [PolicyAlias] (p : Params) (st : State 1) (r : Nat) : State 1 :=
  @gate gridLeasePolicy p 1 st r
end AvailableChain.GridCO
namespace AvailableChain.FGSA
def badGate2 (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  @GridCO.sneakyGate GridCO.slowLeasePolicy p st r
end AvailableChain.FGSA
LEAN
cat > "$neg/FGSALeaseLib.lean" <<'LEAN'
import AvailableChainFGSA
namespace AvailableChain.GridCO
/-- An imported wrapper with no policy parameter that fixes the default. -/
def fixedGate (p : Params) (st : State 1) (r : Nat) : State 1 :=
  @gate gridLeasePolicy p 1 st r
end AvailableChain.GridCO
LEAN
cat > "$neg/FGSALeaseUse.lean" <<'LEAN'
import FGSALeaseLib
namespace AvailableChain.FGSA
def badGate3 (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  GridCO.fixedGate p st r
end AvailableChain.FGSA
LEAN
for m in FGSALeaseNeg FGSALeaseLib FGSALeaseUse; do
  lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean -o "$0/$1.olean" "$0/$1.lean"' "$neg" "$m"
done
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSALease.lean FGSALeaseNeg FGSALeaseUse' "$neg"
expect_fail "lease controls" $code "$out" \
  "leaseNegControl: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy" \
  "AvailableChain.LeaseAuditAlias.gate: has a policy parameter" \
  "AvailableChain.GridCO.sneakyGate: has a policy parameter" \
  "AvailableChain.GridCO.fixedGate: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy"
echo "all FGSA checks pass"
