#!/usr/bin/env bash
# Run all controls, or one named rule: bash scripts/check-layers-selftest.sh B4
# All fixture files are in a temporary directory. No Lean build is needed.
set -euo pipefail
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
exec "${PYTHON:-python3}" -u -B - "$script_dir" "$@" <<'PY'
import hashlib
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import tomllib

scripts = Path(sys.argv[1])
repo = scripts.parent
checker = scripts / "check-layers.py"
api = runpy.run_path(str(checker), run_name="check_layers_selftest")
rule_ids = api["RULE_IDS"]
selected = sys.argv[2:]
if len(selected) > 1 or (selected and selected[0] not in rule_ids):
    raise SystemExit("usage: check-layers-selftest.sh [RULE-ID]")

G = "AvailableChainGeneric"
K = "AvailableChainKitFG"
F = "AvailableChainFGSA"
R = "AvailableChainFGSARun"
C = "AvailableChainFGSAClaims"
P = "AvailableChainFGSAProofs"
I = "AvailableChainFGSAInhabit"
X = "AvailableChainRegistry"
SP = G + ".Statements.Pure"
SV = G + ".Statements.V2"
SA = G + ".Statements.AC"
PP = G + ".Proofs.Pure"
PV = G + ".Proofs.V2"
PA = G + ".Proofs.AC"

# Each control adds precisely one finding, with the named rule ID. Targets
# need not exist: this is a text check, not an elaboration check.
controls = {
    "B4": (F + ".Model.Control", F + ".Proofs.Helper"),
    "B6-FACADE": (X + ".Control", "AvailableChainFramework"),
    "B6-MATHLIB": (X + ".Proofs.Control", "Mathlib"),
    "B6-TACTIC": (K + ".Control", "Mathlib.Tactic"),
    "B7-TESTS": (X, X + ".Tests.Helper"),
    "B7-BODY": (X, None),
    "B7-GLOBS": (X + ".Control", None),
    "GLY-SPURE": (SP + ".Control", "AvailableChainModel.Generic.Run"),
    "GLY-SV2": (SV + ".Control", "AvailableChainModel.Generic.Run"),
    "GLY-SAC": (SA + ".Control", "AvailableChainSA.Statements.Contract"),
    "GLY-PPURE": (PP + ".Control", "AvailableChainEngineV2.Engine.Run"),
    "GLY-PV2": (PV + ".Control", "AvailableChainSA.Model.Protocol"),
    "GLY-PAC": (PA + ".Control", "AvailableChainSAPC.Model.Protocol"),
    "GLY-FG": (G, "AvailableChainSimplexFG.Objects"),
    "GLY-AC-USE": (X + ".Control", SA + ".Reads"),
    "GLY-KITFG-DEF": (K + ".ViewLock", SP + ".Walk"),
    "GLY-KITFG-PROOF": (K + ".Control", PP + ".Walk"),
    "GLY-LOCKED": ("AvailableChainFramework.Hooks", SP + ".Walk"),
    "GLY-NOGEN": ("AvailableChainSimplexFG.Control", SP + ".Quorum"),
    "GLY-WALK": ("AvailableChainGridCO.Model.Walk", "AvailableChainModel.Generic.Run"),
    "FG-GRID": (K + ".Control", "AvailableChainGridCO.Proofs.Map"),
    "RUN": (R + ".Proofs.Control", "AvailableChainKit.Engine.Clock"),
    "CLAIMS": (C + ".Statements.Control", "AvailableChainModel.Generic.Run"),
    "LANE": (P + ".Proofs.F1.Control", P + ".Proofs.F2.Helper"),
    "SHARED": (P + ".Proofs.Shared.Control", P + ".Proofs.F1.Helper"),
    "ASSEMBLY": (P + ".Proofs.Assembly.Control", P + ".Proofs.F1.Helper"),
    "CLAIM-USE": (X + ".Control", C + ".Claims.F1"),
    "LANE-CLAIMS": (P + ".Proofs.F1.Control", P + ".Proofs.Shared.Claims"),
    "EXPORT-USE": (X + ".Control", P + ".Proofs.F1.Export"),
    "INHABIT": (I + ".Control", "AvailableChainFramework.Hooks"),
    "TEST-USE": (X + ".Proofs.Control", X + ".Tests.Helper"),
    "TEST-SCOPE": (X + ".Tests.Control", "AvailableChainModel.Objects.Blocks"),
    "PHASES": (X + ".Control", C + ".Statements.PhasesInternal"),
    "CHECK-SUPPORT": (X + ".Control", "AvailableChainCheckSupport.GeneratedOwner"),
}
assert controls.keys() == rule_ids, (controls.keys() ^ rule_ids)

config = tomllib.loads((repo / "lakefile.toml").read_text())
lib_names = sorted({lib["name"] for lib in config["lean_lib"]} | api["FUTURE_LIBS"])
tests_libs = {x + "Tests" for x in (C, P, I)}


def put(root, relative, text):
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def module(root, name, dep=None, form="public import", body="", src=""):
    relative = Path(src).joinpath(*name.split(".")).with_suffix(".lean")
    return put(root, relative, "module\n" + (f"{form} {dep}\n" if dep else "") + body)


def setup(root):
    text = 'name = "check-layers-fixture"\n'
    for name in lib_names:
        support = name == "AvailableChainCheckSupport"
        suffix = ".+" if support else ".*"
        text += f'\n[[lean_lib]]\nname = {json.dumps(name)}\n'
        if name in tests_libs:  # F0.0b Tests targets: submodules of the owner.
            text += f'roots = []\nglobs = [{json.dumps(name.removesuffix("Tests") + ".Tests.+")}]\n'
        else:
            text += f'globs = [{json.dumps(name + suffix)}]\n'
        if support:
            text += 'srcDir = "scripts"\n'
    put(root, "lakefile.toml", text)
    for relative in ("scripts/CatalogLock.lean", "scripts/baselines/kitfg-def-modules.txt"):
        put(root, relative, (repo / relative).read_text(encoding="utf-8"))


def run(root, expected_code, expected=None, extra=()):
    command = [sys.executable, "-B", str(checker), "--root", str(root), *extra]
    result = subprocess.run(command, text=True, capture_output=True)
    found = {tuple(line.split()) for line in result.stdout.splitlines()}
    assert result.returncode == expected_code, (command, result.returncode, result.stdout, result.stderr)
    if expected is not None:
        assert found == set(expected), (command, "expected", expected, "found", found, result.stderr)
    return found


def snapshot():
    # Read-only fingerprint of the worktree, including untracked files.
    # Build output and Git metadata are outside the self-test's scope.
    result = {}
    for current, dirs, files in os.walk(repo):
        dirs[:] = [name for name in dirs if not name.startswith(".")]
        for name in files:
            path = Path(current) / name
            if not name.startswith("."):
                result[str(path.relative_to(repo))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


before = snapshot()
with tempfile.TemporaryDirectory(prefix="check-layers-selftest-") as temporary:
    temp = Path(temporary)
    for rule in selected or controls:
        root = temp / rule
        setup(root)
        run(root, 0, set())  # Missing future libraries/modules pass vacuously.
        importer, dep = controls[rule]
        module(root, importer, dep)
        if rule == "B6-TACTIC":
            module(root, K + ".Consumer", importer)
        elif rule == "B7-BODY":
            module(root, importer, body="def value : Nat := 0\n")
            dep = "<body:def>"
        elif rule == "B7-GLOBS":
            path = root / "lakefile.toml"
            path.write_text(path.read_text().replace(f'globs = ["{X}.*"]\n', ""))
            importer, dep = X, f"<globs:{X}.*>"
        run(root, 1, {(rule, importer, dep)})
        print(f"PASS {rule}: python3 scripts/check-layers.py --root <temp> -> exit 1; one exact finding")

    if not selected:
        # Real-file header controls. Each spelling must produce the same
        # edge, including newlines, nested comments and quoted identifiers.
        forms = ["import", "public import", "meta import", "public meta import",
                 "import all", "meta import all", "public import all", "public meta import all",
                 "public\n/- outer /- inner -/ end -/ meta\nimport\nall"]
        for index, form in enumerate(forms):
            root = temp / f"header-{index}"
            setup(root)
            module(root, X + ".Control", "«Mathlib»", form=form,
                   body='/- import AvailableChainCheckSupport.Fake -/\n'
                        'def text := "import AvailableChainCheckSupport.Fake"\n')
            run(root, 1, {("B6-MATHLIB", X + ".Control", "Mathlib")})
        print("PASS header syntax: 9 forms -> exit 1; comments and body text ignored")

        # Positive controls cover the narrow allowances. Use separate trees
        # so a proof's importer does not change the leaf-tactic test.
        positives = [
            (SP + ".Quorum", "AvailableChainModel.Objects.Blocks"),
            (SP + ".Other", SP + ".Quorum"),
            (SP + ".Walk", "AvailableChainGridCO.Model.Walk"),
            (PP + ".Walk", "AvailableChainGridCO.Model.Walk"),
            (PP + ".Numeric", SP + ".Quorum"),
            (SV + ".Reads", "AvailableChainKitV2.ClockLaws"),
            (SV + ".Reads", "AvailableChainEngineV2.Conditions.Interface"),
            (SA + ".Reads", "AvailableChainSA.Model.Protocol"),
            (PV + ".Receipt", "AvailableChainKitV2.Receipt"),
            (PA + ".Votes", "AvailableChainGridCO.Model.Protocol"),
            (K + ".StoreInvDef", SP + ".Quorum"),
            (K + ".ViewLock", SP + ".Quorum"),
            (K + ".HonestRows", SP + ".Quorum"),
            (K + ".WeightsBridge", SP + ".Quorum"),
            (K + ".QuorumFacts", PP + ".Quorum"),
            ("AvailableChainFramework.Hooks", SP + ".Quorum"),
            ("AvailableChainFramework.Catalog.Control", SV + ".Reads"),
            ("AvailableChainGridCO.Model.Walk", "AvailableChainModel.Objects.Blocks"),
            (F + ".Proofs.Control", "AvailableChainGridCO.Proofs.StoreFacts"),
            (K + ".Control", "AvailableChainGridCO.Proofs.StoreFacts"),
            (R + ".Proofs.Control", F + ".Proofs.StoreInv"),
            (C + ".Statements.Control", R + ".Statements.Control"),
            (C + ".Statements.Control", K + ".HonestRows"),
            (P + ".Proofs.F1.Control", P + ".Proofs.F1.Helper"),
            (P + ".F1.Control", P + ".Shared.Reads"),
            (P + ".Proofs.F1.Control", C + ".Statements.ChannelProps"),
            (P + ".Proofs.F1.Export", C + ".Claims.F1"),
            (P + ".F1.Export", C + ".Claims.F1"),
            (P + ".Proofs.Assembly.Control", P + ".Proofs.F1.Export"),
            (P + ".Assembly.Control", P + ".F1.Export"),
            (P + ".Proofs.Shared.Control", F + ".Proofs.StoreInv"),
            (P + ".Proofs.F4.Control", C + ".Statements.PhasesInternal"),
            (P + ".Finality.Control", C + ".Statements.PhasesInternal"),
            (I + ".Control", C + ".Statements.ChannelProps"),
            (X + ".Tests.Control", X + ".Proofs.Control"),
            (X + ".Tests.Control", "Mathlib.Tactic"),
            (X + ".Proofs.Leaf", "Mathlib.Tactic"),
            (X, X + ".Proofs.Helper"),
            (X + ".Control", "AvailableChainCheckSupportExtra.Helper"),
            # L42: the exact modules that may import Claims/*.
            (C, C + ".Claims.Clean"),
            (C + ".FGSAClaims", C + ".Claims.Clean"),
            (C + ".Tests.Axioms", C + ".Claims.Clean"),
            (P + ".Proofs.Shared.Claims", C + ".Claims.Clean"),
            (P + ".Proofs.Shared.Claims", C + ".Claims"),
            # R-F1 D6: the modules that may import Shared.Claims.
            (P + ".Proofs.F1.Export", P + ".Proofs.Shared.Claims"),
            (P + ".Proofs.Assembly.Control", P + ".Proofs.Shared.Claims"),
            (P + ".Tests.Axioms", P + ".Proofs.Shared.Claims"),
            (P, P + ".Proofs.Shared.Claims"),
        ]
        for index, (importer, dep) in enumerate(positives):
            root = temp / f"positive-{index}"
            setup(root)
            module(root, importer, dep)
            run(root, 0, set())
        print(f"PASS allowed imports: {len(positives)} cases -> exit 0")

        # Boundary tests can match more than one rule. They ensure that a
        # specific exception or a file-name component cannot widen a set.
        boundaries = [
            (R + ".Proofs.Control", R, "B6-FACADE"),
            (C + ".Statements.Control", C, "B6-FACADE"),
            (P + ".F1.Control", P, "B6-FACADE"),
            (I + ".Control", I, "B6-FACADE"),
            (SP + ".Control", "Lean.Elab.Command", "GLY-SPURE"),
            (SV + ".Control", "AvailableChainKitV2.Other", "GLY-SV2"),
            (SV + ".Control", "AvailableChainKitV2.ClockLaws.Extra", "GLY-SV2"),
            (SP + ".Control", "AvailableChainGridCO.Model.Walk", "GLY-SPURE"),
            (SP + ".Walk", "AvailableChainGridCO.Model.WalkExtra", "GLY-SPURE"),
            (PP + ".Control", "AvailableChainGridCO.Model.Walk", "GLY-PPURE"),
            (SV + ".Control", SP + ".Walk", "GLY-SV2"),
            (K + ".StoreInvDef", PP + ".Quorum", "GLY-KITFG-DEF"),
            (K + ".HonestRows", SV + ".Reads", "GLY-KITFG-DEF"),
            (K + ".Proof", SP + ".Walk", "GLY-KITFG-PROOF"),
            (K + ".WeightsBridge", PP + ".Quorum", "GLY-KITFG-PROOF"),
            ("AvailableChainFramework.Catalog.Control", PP + ".Quorum", "GLY-LOCKED"),
            ("AvailableChainFramework.V2.Control", SA + ".Reads", "GLY-LOCKED"),
            ("AvailableChainGridCO.Model.Control", SP + ".Quorum", "GLY-NOGEN"),
            (F + ".Proofs.Control", "AvailableChainGridCO.Proofs.StoreFacts.Extra", "FG-GRID"),
            (R + ".Proofs.Control", "AvailableChainModel.Generic.Run", "RUN"),
            (C + ".Statements.Control", R + ".Proofs.Control", "CLAIMS"),
            (P + ".F1.Control", P + ".F2.Model.Hidden", "LANE"),
            (P + ".Shared.Control", P + ".F1.Statements.Hidden", "SHARED"),
            (P + ".Shared.Control", P + ".Assembly.Control", "SHARED"),
            (P + ".Shared.Control", P + ".F1.Export", "SHARED"),
            (P + ".F1.Export", C + ".Claims.F2", "CLAIM-USE"),
            (P + ".F1.Control", P + ".F1.Export", "EXPORT-USE"),
            (P + ".Assembly.Control", C + ".Claims.F1", "CLAIM-USE"),
            (I + ".Control", P + ".F1.Control", "INHABIT"),
            (P + ".Proofs.F5.Control", C + ".Statements.PhasesInternal", "PHASES"),
            # L42 negatives: any other module that imports Claims/* is rejected;
            # the Shared.Claims exception covers Claims/* only.
            (C + ".Statements.Control", C + ".Claims.Clean", "CLAIM-USE"),
            (C + ".FGSAClaims.Extra", C + ".Claims.Clean", "CLAIM-USE"),
            (C + ".Tests.Control", C + ".Claims.Clean", "CLAIM-USE"),
            (P + ".Proofs.Shared.Other", C + ".Claims.Clean", "CLAIM-USE"),
            (P + ".Proofs.Shared.Other", C + ".Claims.Clean", "SHARED"),
            (P + ".Shared.Claims", C + ".Claims.Clean", "CLAIM-USE"),
            (P + ".Proofs.Shared.Claims", P + ".Proofs.F1.Helper", "SHARED"),
        ]
        for index, (importer, dep, rule) in enumerate(boundaries):
            root = temp / f"boundary-{index}"
            setup(root)
            module(root, importer, dep)
            result = run(root, 1)
            assert (rule, importer, dep) in result, (rule, result)
        print(f"PASS rule boundaries: {len(boundaries)} cases -> exit 1")

        # R-F1 D6 is transitive: a lane helper that imports Shared.Claims
        # taints every lane module that imports the helper.
        root = temp / "lane-claims-transitive"
        setup(root)
        module(root, P + ".Proofs.F1.Helper", P + ".Proofs.Shared.Claims")
        module(root, P + ".Proofs.F1.Control", P + ".Proofs.F1.Helper")
        module(root, P + ".Proofs.F1.Export", P + ".Proofs.F1.Helper")
        run(root, 1, {("LANE-CLAIMS", P + ".Proofs.F1.Helper", P + ".Proofs.Shared.Claims"),
                      ("LANE-CLAIMS", P + ".Proofs.F1.Control", P + ".Proofs.F1.Helper")})
        root = temp / "lane-claims-via-shared"
        setup(root)
        module(root, P + ".Proofs.Shared.Mid", P + ".Proofs.Shared.Claims")
        module(root, P + ".F2.Control", P + ".Shared.Mid")
        module(root, P + ".Shared.Mid", C + ".Claims.F2")
        found = run(root, 1)
        assert ("LANE-CLAIMS", P + ".F2.Control", P + ".Shared.Mid") in found, found
        assert not any(f[0] == "LANE-CLAIMS" and f[1].startswith(P + ".Proofs.Shared") for f in found), found
        print("PASS lane claims transitive: helper and importer rejected; Export and Shared exempt")

        root = temp / "test-tactic-leaf"
        setup(root)
        module(root, X + ".Tests.Control", "Mathlib.Tactic")
        module(root, X + ".Tests.Consumer", X + ".Tests.Control")
        run(root, 1, {("B6-TACTIC", X + ".Tests.Control", "Mathlib.Tactic"),
                      ("TEST-USE", X + ".Tests.Consumer", X + ".Tests.Control")})
        print("PASS test tactic must be a leaf: exit 1")

        # srcDir, root facades, explicit roots, glob-only files, scripts and
        # undeclared .lean files must all have the intended scan scope.
        root = temp / "discovery"
        setup(root)
        path = root / "lakefile.toml"
        path.write_text(path.read_text() + '\n[[lean_lib]]\nname = "Custom"\n'
                        'srcDir = "src"\nroots = ["CustomRoot"]\n'
                        'globs = ["Custom.*"]\n')
        module(root, "CustomRoot", "Mathlib", src="src")
        module(root, "Custom.Hidden", "Mathlib", src="src")
        module(root, "CustomRoot.Pending.Hidden", "Mathlib", src="src")
        module(root, "AvailableChainCheckSupport.Helper", "Lean", src="scripts")
        module(root, "Helper", "AvailableChainCheckSupport.Helper", src="scripts")
        module(root, "Unlisted", "AvailableChainCheckSupport.Helper")
        module(root, "Ignored", "Mathlib", src=".lake/packages/example")
        expected = {("B6-MATHLIB", name, "Mathlib") for name in
                    ("CustomRoot", "Custom.Hidden", "CustomRoot.Pending.Hidden")}
        expected.add(("CHECK-SUPPORT", "Unlisted", "AvailableChainCheckSupport.Helper"))
        run(root, 1, expected)
        print("PASS discovery: roots/srcDir/globs/facades/support/unlisted files -> exit 1")

        # An exact baseline accepts a legacy edge, still prints it, rejects
        # a new edge, and shrinks when --write-baseline runs after removal.
        root = temp / "baseline"
        setup(root)
        module(root, X + ".Control", "Mathlib")
        first = {("B6-MATHLIB", X + ".Control", "Mathlib")}
        run(root, 1, first)
        run(root, 0, first, extra=("--write-baseline",))
        baseline = root / "scripts/baselines/check-layers.txt"
        content = baseline.read_bytes()
        run(root, 0, first)
        run(root, 0, first, extra=("--write-baseline",))
        assert baseline.read_bytes() == content
        module(root, X + ".New", "Mathlib")
        run(root, 1, first | {("B6-MATHLIB", X + ".New", "Mathlib")})
        module(root, X + ".Control")
        module(root, X + ".New")
        run(root, 0, set(), extra=("--write-baseline",))
        assert all(line.startswith("#") for line in baseline.read_text().splitlines())
        print("PASS baseline: new=1, write=0, legacy=0, added=1, shrink=0; deterministic")

        baseline.write_text("UNKNOWN Importer Target\n")
        run(root, 2)
        print("PASS invalid baseline: exit 2")

assert snapshot() == before, "self-test changed the worktree"
print(f"PASS self-test: {len(selected) if selected else len(controls)} rule controls; worktree unchanged")
PY
