#!/usr/bin/env python3
"""Negative controls for DCK scopes, strict audits and scoped proof coverage."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile

import check_common as C
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


D = load('dev', 'scripts/dev-check.py')
S = load('scopes', 'scripts/check-sleep-scopes.py')
P = load('coverage', 'scripts/check-proof-coverage.py')
ROOT = Path(__file__).resolve().parents[1]


def rejected(label, diagnostic, action):
    try:
        action()
    except ValueError as error:
        if diagnostic not in str(error):
            raise AssertionError(f'{label}: wrong failure: {error}') from error
        print(f'CONTROL {label}: PASS ({error})', flush=True)
    else:
        raise AssertionError(label + ': accepted invalid fixture')


def section_bytes(text):
    lines = text.splitlines(keepends=True)
    return {key: ''.join(lines[start:end]) for key, (start, end) in P.sections(text).items()}


def main():
    graph = C.import_graph()
    scope = ROOT / 'scripts/dev-scope-s1.txt'
    original = scope.read_text()
    required = D.validate_scope(scope, graph)
    with tempfile.TemporaryDirectory(prefix='dev-controls-', dir=ROOT / '.lake') as tmp:
        tmp = Path(tmp)
        fixture = tmp / 'scope.txt'
        omitted = sorted(required)[0]
        fixture.write_text(original.replace(omitted + '\n', '', 1))
        rejected('omitted REQUIRED', 'OMITTED S1 MODULE',
                 lambda: D.validate_scope(fixture, graph))
        fixture.write_text(original + '\n[EXPECTED-FAIL]\n' + omitted + ' W3\n')
        rejected('EXPECTED-FAIL at s1', 'UNKNOWN SECTION',
                 lambda: D.validate_scope(fixture, graph))
        fixture.write_text(original)
        changed = {**graph, omitted: [*graph[omitted], D.SHARED + '.Claims'],
                   D.SHARED + '.Claims': []}
        rejected('REQUIRED imports DEFERRED', 'REQUIRED IMPORTS DEFERRED',
                 lambda: D.validate_scope(fixture, changed))
        package = (ROOT / 'scripts/dev-pkg/sleep-ppc.txt').read_text()
        fixture.write_text(package.replace(omitted + '\n', '', 1))
        rejected('omitted package module', 'OMITTED PACKAGE MODULE',
                 lambda: D.validate_package(fixture, required, graph))
        fixture.write_text(package.replace(
            '[GREEN]', '[GREEN]\nAvailableChainMissing.NoSuchModule'))
        rejected('unknown package target', 'UNKNOWN PACKAGE TARGET',
                 lambda: D.validate_package(fixture, required, graph))
        # A package target outside S1 is allowed, and a REQUIRED target may be
        # EXPECTED-FAIL in this level only. This guards the r8 domain rule.
        fixture.write_text(package.replace(omitted + '\n', '', 1).replace(
            '[EXPECTED-FAIL]', '[EXPECTED-FAIL]\n' + omitted + ' W3').replace(
            '[TARGETS]', '[TARGETS]\nAvailableChainModel.Generic.Env'))
        fixture.write_text(fixture.read_text().replace(
            '[GREEN]', '[GREEN]\nAvailableChainModel.Generic.Env'))
        green = D.validate_package(fixture, required, graph)
        assert 'AvailableChainModel.Generic.Env' in green and omitted not in green
        print('CONTROL package target outside S1 / owned EXPECTED-FAIL: PASS', flush=True)
        fixture.write_text(fixture.read_text().replace(
            '[GREEN]\nAvailableChainModel.Generic.Env', '[GREEN]'))
        rejected('omitted outside-S1 package target', 'OMITTED PACKAGE MODULE',
                 lambda: D.validate_package(fixture, required, graph))
        rejected('active imports PC-SA', 'ACTIVE IMPORTS PC-SA', lambda: S.check_active(
            {'AvailableChainFGSA': ['AvailableChainPCSA']}, ['AvailableChainFGSA']))
        rejected('deferred source proof', 'DEFERRED FORBIDDEN PROOF', lambda:
                 S.check_deferred('AvailableChainPCSA.Proofs.Control',
                                  'theorem bad : True := sorry'))
        rejected('deferred adapter extension', 'DEFERRED GLOBAL EXTENSION', lambda:
                 S.check_deferred('AvailableChainPCSAProofs.Proofs.Shared.FGCompose',
                                  'infix:50 \"bad\" => Nat.add'))
        sorry_dir = tmp / 'sorry-build'
        sorry_dir.mkdir()
        (sorry_dir / 'lean-toolchain').write_text((ROOT / 'lean-toolchain').read_text())
        (sorry_dir / 'lakefile.toml').write_text(
            'name = "dev-negative"\nversion = "0.1.0"\n'
            'defaultTargets = ["DevSorry"]\n[[lean_lib]]\nname = "DevSorry"\n')
        (sorry_dir / 'DevSorry.lean').write_text('theorem devSorry : True := by sorry\n')
        result = subprocess.run(['lake', 'build', '--wfail'], cwd=sorry_dir,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert result.returncode and 'sorry' in result.stdout, result.stdout
        print('CONTROL sorry module: PASS (lake build --wfail rejected sorry)', flush=True)
        axiom = tmp / 'Axiom.lean'
        axiom.write_text('axiom devUnexpected : True\n#print axioms devUnexpected\n')
        result = subprocess.run(['lake', 'env', 'lean', str(axiom)], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert result.returncode == 0, result.stdout
        rejected('non-standard axiom', 'BAD AXIOMS: devUnexpected',
                 lambda: D.strict_results(axiom.read_text(), result.stdout))
        rejected('missing axiom result', 'AXIOM RESULTS',
                 lambda: D.strict_results('#print axioms missing\n', ''))
        inventory = tmp / 'coverage.txt'
        original_inventory = (ROOT / 'scripts/proof-audit-coverage.txt').read_text()
        inventory.write_text(original_inventory)
        key = D.SHARED_AUDIT
        before = section_bytes(original_inventory)
        # Make the selected section stale. The real scoped writer must repair it
        # and preserve every byte of each section outside the selected key.
        inventory.write_text(P.replace_sections(original_inventory, {
            key: before[key].replace('fgsa_store_cumulative', 'devStaleName')}))
        subprocess.run(['python3', '-B', 'scripts/check-proof-coverage.py', '--write',
                        '--audits', key, '--inventory', str(inventory)], cwd=ROOT, check=True)
        after = section_bytes(inventory.read_text())
        assert set(before) == set(after) == set(P.AUDITS)
        assert all(before[k] == after[k] for k in before if k != key)
        assert before[key] == after[key]
        print('CONTROL scoped write preserves all other sections: PASS', flush=True)
        result = subprocess.run(['python3', '-B', 'scripts/check-proof-coverage.py',
                                 '--audits', 'AvailableChainUnknown.Tests.Axioms'], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert result.returncode and 'unknown coverage key' in result.stdout, result.stdout
        print('CONTROL unknown coverage key: PASS (rejected before Lean import)', flush=True)
    print('DCK controls: PASS', flush=True)


if __name__ == '__main__':
    main()

