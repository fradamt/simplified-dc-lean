#!/usr/bin/env bash
# FGSA checks: build (--wfail), root imports, native evaluation outside
# comments, the direct-import allowlist with its directory rules, the Q1/Q5
# boundary grep, the axiom check (with build coverage and the import-closure
# check), the lease-instance check, the ext-name check of the FG pin table, and
# the negative controls of these checks.
# Import headers are parsed after comment removal (G13 Astra M2, Opus m1). The
# parser fails closed, and the axiom script checks the same allowlist again on
# the compiled import data (G13 fold MINOR-2). Source files: `find -L` with
# `-iname '*.lean'` (symbolic links followed, extension in any case).
# Run: bash scripts/check-fgsa.sh. Exit 0 when every check passes.
set -euo pipefail
cd "$(dirname "$0")/.."
for f in scripts/CheckFGSAAxioms.lean scripts/CheckFGSALease.lean scripts/CheckFGSAExt.lean; do
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
# Fail closed: if the rest of the file still has the token `import` or
# `prelude` (for example after a `prelude` line or a module name with `«`), it
# prints the line `!UNPARSED`.
header_imports='
  local $/; my $s = <STDIN>;
  $s =~ s/^\s+//; $s =~ s/^module\s+//;
  while ($s =~ s/^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][A-Za-z0-9_.]*)\s*//) {
    print "$1\n";
  }
  print "!UNPARSED\n" if $s =~ /(?<![\w.\x27!?])(?:import|prelude)(?![\w\x27!?])/;'
imports_of() { perl -CSD -e "$strip_comments" < "$1" | perl -CSD -e "$header_imports"; }
# The FGSA source files under base directory $1, relative to it.
source_files() { (cd "$1" && find -L AvailableChainFGSA -iname '*.lean' | sort); }

# Root imports under base directory $1: every source file is a root import.
check_root_imports() {
  local base=$1 missing
  missing=$(comm -23 \
    <(source_files "$base" | sed -E 's/\.[lL][eE][aA][nN]$//; s|/|.|g' | sort) \
    <(imports_of "$base/AvailableChainFGSA.lean" | sort))
  [ -z "$missing" ] || { echo "NOT IMPORTED BY THE ROOT: $missing"; return 1; }
  if imports_of "$base/AvailableChainFGSA.lean" | grep -qx '!UNPARSED'; then
    echo "UNPARSED IMPORT HEADER: AvailableChainFGSA.lean"; return 1
  fi
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
  for f in $(source_files "$base") AvailableChainFGSA.lean; do
    rel=${f#AvailableChainFGSA/}
    if [ "$f" = AvailableChainFGSA.lean ]; then layer=root; else layer=${rel%%/*}; fi
    for m in $(imports_of "$base/$f"); do
      if [ "$m" = '!UNPARSED' ]; then echo "UNPARSED IMPORT HEADER: $f"; bad=1; continue; fi
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
  for f in $(source_files "$base") AvailableChainFGSA.lean; do
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
for f in $(source_files .) AvailableChainFGSA.lean; do
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
# The `leanIn "AvailableChainFGSA"` names of AvailableChainKitFG/Pins.lean get
# the checks of a `.lean` name (existence, the library of the declaring module,
# the three standard axioms) in this environment; see scripts/CheckFGSAExt.lean.
# FGPinIds.lean rejects a library that is not on its allowlist. The pin gate for
# a pin with `leanIn` evidence is check-fg.sh plus this script.
echo "== ext names of the FG pin table"
lake build --wfail AvailableChainSimplexFG AvailableChainKitFG
extrecs=$(mktemp)
lake env lean --run scripts/FGPinIds.lean --ext > "$extrecs"
lake env lean --run scripts/CheckFGSAExt.lean "$extrecs"
rm -f "$extrecs"

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
printf 'module\n@[expose] public section\ntheorem negOrphanC : False := sorry\nend\n' \
  > "$neg/tree/AvailableChainFGSA/Tests/NegOrphanC.LEAN"
echo '/- public import AvailableChainFGSA.Tests.NegOrphan -/' >> "$neg/tree/AvailableChainFGSA.lean"
run check_root_imports "$neg/tree"
expect_fail "orphan modules behind a commented import and with a .LEAN name (root check)" \
  $code "$out" "NOT IMPORTED BY THE ROOT: AvailableChainFGSA.Tests.NegOrphan" \
  "AvailableChainFGSA.Tests.NegOrphanC"

# The compiled checks: the orphan file (with a sorry) against the build, and a
# forbidden library in the import closure.
cat > "$neg/FGSAClosureNeg.lean" <<'LEAN'
import AvailableChainSAPC.Model.Choice
LEAN
lake env lean -o "$neg/FGSAClosureNeg.olean" "$neg/FGSAClosureNeg.lean"
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSAAxioms.lean --root FGSAClosureNeg --files "$0/tree/AvailableChainFGSA"' "$neg"
expect_fail "orphan modules and forbidden closure (axiom script)" $code "$out" \
  "NOT IN THE BUILD: AvailableChainFGSA.Tests.NegOrphan " \
  "NOT IN THE BUILD: AvailableChainFGSA.Tests.NegOrphanC " \
  "FORBIDDEN LIBRARY IN THE IMPORT CLOSURE: AvailableChainSAPC"

# Header forms and file names that an earlier parser missed (G13 fold MINOR-2;
# the auditor's files in scripts/fgsa-controls/): a module name with «», a
# `prelude` line, a .LEAN file, and a linked directory. Each imports L*, which
# the allowlist forbids. First the text checks, then the compiled check (the
# four modules compiled as FGSA modules, over a copy of the FGSA build).
mk_tree
cp scripts/fgsa-controls/AdvG.lean scripts/fgsa-controls/AdvP.lean \
  scripts/fgsa-controls/AdvCase.LEAN "$neg/tree/AvailableChainFGSA/Model/"
mkdir -p "$neg/sub" && cp scripts/fgsa-controls/Sub/X.lean "$neg/sub/"
ln -s "$neg/sub" "$neg/tree/AvailableChainFGSA/Model/Sub"
printf 'public import AvailableChainFGSA.Model.%s\n' AdvG AdvP AdvCase Sub.X \
  >> "$neg/tree/AvailableChainFGSA.lean"
run check_direct_imports "$neg/tree"
expect_fail "header forms and file names (text allowlist)" $code "$out" \
  "UNPARSED IMPORT HEADER: AvailableChainFGSA/Model/AdvG.lean" \
  "UNPARSED IMPORT HEADER: AvailableChainFGSA/Model/AdvP.lean" \
  "IMPORT NOT ALLOWED: AvailableChainFGSA/Model/AdvCase.LEAN imports AvailableChainLStar.Model.Protocol" \
  "IMPORT NOT ALLOWED: AvailableChainFGSA/Model/Sub/X.lean imports AvailableChainLStar.Model.Protocol"
run check_boundary "$neg/tree"
expect_fail "Q1/Q5 grep in a .LEAN file and a linked directory" $code "$out" \
  "ENGINE REFERENCE in AvailableChainFGSA/Model/AdvCase.LEAN" \
  "ENGINE REFERENCE in AvailableChainFGSA/Model/Sub/X.lean"
mkdir -p "$neg/c"
cp -R .lake/build/lib/lean/AvailableChainFGSA .lake/build/lib/lean/AvailableChainFGSA.* "$neg/c/"
for m in AdvG:AdvG.lean AdvP:AdvP.lean AdvCase:AdvCase.LEAN Sub/X:Sub/X.lean; do
  mkdir -p "$neg/c/AvailableChainFGSA/Model/Sub"
  lake env lean -o "$neg/c/AvailableChainFGSA/Model/${m%%:*}.olean" "$neg/tree/AvailableChainFGSA/Model/${m#*:}"
done
run lake env bash -c 'LEAN_PATH="$0/c:$LEAN_PATH" lean --run scripts/CheckFGSAAxioms.lean --root AvailableChainFGSA.Model.AdvG --root AvailableChainFGSA.Model.AdvP --root AvailableChainFGSA.Model.AdvCase --root AvailableChainFGSA.Model.Sub.X --files "$0/tree/AvailableChainFGSA"' "$neg"
expect_fail "header forms and file names (compiled allowlist)" $code "$out" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSA.Model.AdvG imports AvailableChainLStar.Model.Protocol" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSA.Model.AdvP imports AvailableChainLStar.Model.Protocol" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSA.Model.AdvCase imports AvailableChainLStar.Model.Protocol" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSA.Model.Sub.X imports AvailableChainLStar.Model.Protocol"

# Lease controls: a direct default-instance call; the anchored gate and tick
# (`gateFrom`, `clockFrom`) at the grid policy (spec sync C1); an alias wrapper
# with its own policy parameter in another namespace (Astra M1); a generic
# wrapper whose policy binder has an alias type (Opus m2); an imported wrapper
# that fixes the default instance inside.
cat > "$neg/FGSALeaseNeg.lean" <<'LEAN'
import AvailableChainFGSA
namespace AvailableChain.FGSA
/-- A GridCO gate at the default instance `gridLeasePolicy`. -/
def leaseNegControl (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  GridCO.gate p st r
/-- The anchored GridCO gate at `gridLeasePolicy`. -/
def leaseNegGateFrom (p : GridCO.Params) (a : Block) (st : GridCO.State 1) (r : Nat) :
    GridCO.State 1 :=
  @GridCO.gateFrom GridCO.gridLeasePolicy p 1 a st r
/-- The anchored GridCO tick at `gridLeasePolicy`. -/
def leaseNegClockFrom (p : GridCO.Params) (a : Block) (st : GridCO.State 1) (t : Int) :
    GridCO.State 1 :=
  @GridCO.clockFrom GridCO.gridLeasePolicy p 1 a st t
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
namespace LeaseMk
/-- Outside `AvailableChain`: a new policy value built with the constructor. -/
def mkGate (p : AvailableChain.GridCO.Params) (st : AvailableChain.GridCO.State 1) (r : Nat) :
    AvailableChain.GridCO.State 1 :=
  @AvailableChain.GridCO.gate ⟨false⟩ p 1 st r
end LeaseMk
LEAN
cat > "$neg/FGSALeaseUse.lean" <<'LEAN'
import FGSALeaseLib
namespace AvailableChain.FGSA
def badGate3 (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  GridCO.fixedGate p st r
def badGate4 (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  LeaseMk.mkGate p st r
end AvailableChain.FGSA
LEAN
for m in FGSALeaseNeg FGSALeaseLib FGSALeaseUse; do
  lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean -o "$0/$1.olean" "$0/$1.lean"' "$neg" "$m"
done
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSALease.lean FGSALeaseNeg FGSALeaseUse' "$neg"
expect_fail "lease controls" $code "$out" \
  "leaseNegControl: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy" \
  "leaseNegGateFrom: AvailableChain.GridCO.gateFrom at AvailableChain.GridCO.gridLeasePolicy" \
  "leaseNegClockFrom: AvailableChain.GridCO.clockFrom at AvailableChain.GridCO.gridLeasePolicy" \
  "AvailableChain.LeaseAuditAlias.gate: has a policy parameter" \
  "AvailableChain.GridCO.sneakyGate: has a policy parameter" \
  "AvailableChain.GridCO.fixedGate: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy" \
  "LeaseMk.mkGate: mentions AvailableChain.GridCO.LeasePolicy.mk (reach)"

# Imported definitions (G13 fold MINOR-1; the auditor's AdvLib/AdvUse in
# scripts/fgsa-controls/): a let-bound and a beta-bound default policy, a
# private wrapper, an irreducible alias of the policy type, and a wrapper
# outside the namespace AvailableChain (the reachability backstop).
cp scripts/fgsa-controls/AdvLib.lean scripts/fgsa-controls/AdvUse.lean "$neg/"
for m in AdvLib AdvUse; do
  lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean -o "$0/$1.olean" "$0/$1.lean"' "$neg" "$m"
done
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSALease.lean AdvUse' "$neg"
expect_fail "lease controls in imported definitions" $code "$out" \
  "AvailableChain.GridCO.fixedLet: AvailableChain.GridCO.gate at #0" \
  "AvailableChain.GridCO.fixedBeta: AvailableChain.GridCO.gate at #0" \
  "AdvLib.0.AvailableChain.GridCO.fixedPriv: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy" \
  "AvailableChain.FGSA.useIrr: AvailableChain.GridCO.genI at cast" \
  "Evil.fixedGate: mentions AvailableChain.GridCO.gridLeasePolicy (reach)"
# Ext-name controls: a name that does not exist; a name outside the library (a
# KitFG constant under AvailableChainFGSA); an unknown library, which fails in
# the manifest step (step 0) of check-fg-pins.sh, in the FG environment.
printf 'ext AvailableChainFGSA AvailableChain.FGSA.noSuchName\nEND ext 1\n' > "$neg/extA"
run lake env lean --run scripts/CheckFGSAExt.lean "$neg/extA"
expect_fail "ext name that does not exist" $code "$out" \
  "EXT NAME NOT FOUND: AvailableChain.FGSA.noSuchName"
printf 'ext AvailableChainFGSA AvailableChain.KitFG.finalLock\nEND ext 1\n' > "$neg/extB"
run lake env lean --run scripts/CheckFGSAExt.lean "$neg/extB"
expect_fail "ext name outside its library" $code "$out" \
  "EXT NAME OUTSIDE AvailableChainFGSA: AvailableChain.KitFG.finalLock"
sed 's/^def table : List Pin := pins$/def table : List Pin := pins ++ [{ id := "neg.ctl.v1", sources := [], clauses := [⟨"control", .leanIn "AvailableChainFGSAX" [`AvailableChain.FGSA.gateStep]⟩] }]/' \
  scripts/FGPinIds.lean > "$neg/FGPinIdsC.lean"
grep -q 'AvailableChainFGSAX' "$neg/FGPinIdsC.lean" ||
  { echo "NEGATIVE CONTROL unknown ext library: the table line did not change"; exit 1; }
run env FGPINIDS="$neg/FGPinIdsC.lean" bash scripts/check-fg-pins.sh
expect_fail "unknown ext library (check-fg-pins.sh step 0)" $code "$out" \
  "UNKNOWN EXT LIBRARY: AvailableChainFGSAX (pin neg.ctl.v1, name AvailableChain.FGSA.gateStep)" \
  "EMITTER FAILED"
echo "all FGSA checks pass"
