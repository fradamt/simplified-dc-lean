#!/usr/bin/env python3
"""Compile isolated fixtures; run the real checker and check each refusal reason."""

import os
from pathlib import Path
import subprocess
import tempfile


REPO = Path(__file__).resolve().parents[1]
os.chdir(REPO)


def command(args, **kwargs):
    return subprocess.run(args, text=True, capture_output=True, **kwargs)


with tempfile.TemporaryDirectory(prefix="proof-eqns-neg.", dir=REPO / ".lake") as scratch:
    root = Path(scratch)
    source = root / "tree"
    source.mkdir()
    env_result = command(["lake", "env", "printenv", "LEAN_PATH"])
    assert env_result.returncode == 0, env_result.stderr
    lean_path = str(source) + os.pathsep + env_result.stdout.strip()
    lean = ["lake", "env", "env", f"LEAN_PATH={lean_path}", "lean"]
    prefix = "AvailableChainCoverageControl"

    def compile_module(module, body):
        file = source / (module.replace(".", "/") + ".lean")
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(body)
        result = command(lean + ["-o", str(file.with_suffix(".olean")), str(file)])
        assert result.returncode == 0, (module, result.stdout, result.stderr)

    for case, equation in (
        ("Valid", "theorem P_def : P = True := by simp [P]"),
        ("Missing", ""),
        ("Private", "private theorem P_def : P = True := rfl"),
        ("WrongType", "theorem P_def : True := True.intro"),
        ("Reflexive", "theorem P_def : P = P := rfl"),
    ):
        module = f"{prefix}.Statements.{case}"
        compile_module(module, "module\npublic import Init\npublic section\n"
                       f"namespace {case}\ndef P : Prop := True\n{equation}\nend {case}\n")
    compile_module(f"{prefix}.Statements.Exposed",
                   "module\npublic import Init\n@[expose] public section\n"
                   "namespace Exposed\ndef P : Prop := True\nend Exposed\n")
    compile_module(f"{prefix}.Statements.Binders",
                   "module\npublic import Init\npublic section\nnamespace Binders\n"
                   "def P {α : Type u} (x : α) := x = x\n"
                   "theorem P_def {α : Type u} (x : α) : P x ↔ x = x := by simp [P]\n"
                   "end Binders\n")
    compile_module(f"{prefix}.Statements.Alias",
                   "module\npublic import Init\npublic section\nnamespace Alias\n"
                   "def SortAlias := Prop\ndef P : SortAlias := True\nend Alias\n")
    compile_module(f"{prefix}.Statements.Other",
                   f"module\npublic import {prefix}.Statements.Missing\n"
                   f"import all {prefix}.Statements.Missing\npublic section\n"
                   "theorem Missing.P_def : Missing.P = True := by simp [Missing.P]\n")
    compile_module(f"{prefix}.Proofs.Leak",
                   "module\npublic import Init\n@[expose] public section\n"
                   "def Leak.f (n : Nat) : Nat := n + 1\n"
                   "theorem Leak.test (n : Nat) : Leak.f n = n + 1 := Leak.f.eq_def n\n")
    for case, line in (
        ("Valid", "#print axioms Valid.P"),
        ("Commented", "-- #print axioms Valid.P\n/- #print axioms Valid.P -/"),
        ("Short", "open Valid\n#print axioms P"),
    ):
        compile_module(f"{prefix}.Tests.{case}",
                       f"module\npublic import {prefix}.Statements.Valid\n{line}\n")
    compile_module("OtherCoverageControl.Tests.Axioms",
                   f"module\npublic import {prefix}.Statements.Valid\n#print axioms Valid.P\n")

    def check(label, module, rc, reason, audit=None):
        args = lean + ["--run", "scripts/CheckProofEqns.lean", "--baseline",
                       "scripts/baselines/check-proof-eqns.txt", module]
        if audit:
            data = root / "coverage.txt"
            data.write_text(f"{prefix}.Statements.Valid Valid.P {audit}\n")
            args += ["--coverage", str(data)]
        result = command(args)
        output = result.stdout + result.stderr
        assert result.returncode == rc and reason in output, (label, result.returncode, output)
        print(f"CONTROL {label}: PASS (rc {rc}; {reason})", flush=True)

    # The audit module source is under the fixture root. Link that library for
    # the source parser, without changing any production library file.
    link = REPO / prefix
    assert not link.exists()
    link.symlink_to(source / prefix, target_is_directory=True)
    try:
        check("home equation", f"{prefix}.Statements.Valid", 0, "0 unaccepted")
        check("exposed predicate", f"{prefix}.Statements.Exposed", 0, "0 unaccepted")
        check("inferred Prop / binders / iff", f"{prefix}.Statements.Binders", 0, "0 unaccepted")
        for case in ("Missing", "Private"):
            check(case, f"{prefix}.Statements.{case}", 1, "STATEMENT DEF MISSING")
        check("unrelated theorem", f"{prefix}.Statements.WrongType", 1, "STATEMENT DEF WRONG TYPE")
        check("reflexive theorem", f"{prefix}.Statements.Reflexive", 1, "STATEMENT DEF WRONG TYPE")
        check("hidden Prop alias", f"{prefix}.Statements.Alias", 1, "STATEMENT DEF MISSING")
        check("wrong home", f"{prefix}.Statements.Other", 1, "STATEMENT DEF WRONG MODULE")
        check("equation export", f"{prefix}.Proofs.Leak", 1, "EQ EXPORT")
        for case, rc, reason in (("Valid", 0, "0 unaccepted"),
                                 ("Commented", 1, "AUDIT LINE MISSING"),
                                 ("Short", 1, "AUDIT LINE MISSING")):
            audit = f"{prefix}.Tests.{case}"
            check(f"audit {case}", audit, rc, reason, audit)
        audit = "OtherCoverageControl.Tests.Axioms"
        check("audit wrong library", audit, 1, "AUDIT MODULE NOT COVERED", audit)
    finally:
        link.unlink()
