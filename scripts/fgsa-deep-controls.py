#!/usr/bin/env python3
"""Compiled, isolated controls for FG-SA deep and frame checks."""
from copy import deepcopy
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile

spec = importlib.util.spec_from_file_location('fgsa_deep', 'scripts/fgsa-deep.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


def require_failure(label, action, reason):
    try:
        result = action()
    except (ValueError, OSError) as exc:
        result = [str(exc)]
    assert result and any(reason in msg for msg in result), (label, result, reason)
    print(f'CONTROL {label}: PASS ({reason})')


def record(before, after):
    return dict(old_digest=before, new_digest=after, cause='isolated compiled body control',
                census_class='B', plan_revision='S0-F/00c control only')


PROBE = r'''
def main (args : List String) : IO UInt32 := do
  let [dir] := args | return 2
  initSearchPath (← findSysroot)
  searchPathRef.modify fun paths => System.FilePath.mk dir :: paths
  let env ← importModules #[{ module := `DeepStatements }] {}
  let root := `AvailableChain.FGSA.DeepControl.claim
  unless !(← runCore env (generated `AvailableChain.FGSA.DeepControl.reader)) do
    throw (IO.userError "control reader must be public")
  let shallow ← runCore env (entryHex .fgsa root)
  let some (.thmInfo claim) := env.find? root | return 2
  IO.FS.writeFile (System.FilePath.mk dir / "proof-value") (deepExpr claim.value)
  let snapshot ← deepSnapshot env #[root]
  IO.FS.writeFile (System.FilePath.mk dir / "snapshot.json") snapshot.compress
  IO.FS.writeFile (System.FilePath.mk dir / "shallow") shallow
  return 0
'''


def check_wiring(root=Path('.')):
    # Both required positive commands must run before the NEG exit.
    shell = (root / 'scripts/check-fgsa-manifest.sh').read_text()
    boundary = shell.index('if [ "${NEG:-1}"')
    assert shell.index('fgsa-deep.py --frame-check') < boundary
    assert shell.index('--scope fgsa --deep --check') < boundary
    gate = (root / 'scripts/gate.sh').read_text()
    assert 'fgsa-manifest) step "$1" bash scripts/check-fgsa-manifest.sh ;;' in gate
    group = ('run_group fgsa-claims check-fg-compose check-fgsa check-build check-fgsa-run '
             '\\\n  fgsa-manifest\n')
    assert group in gate
    assert gate.index(group) > gate.index('fi\n# Longest measured FULL steps first.')
    print('CONTROL merge/full mandatory frame and deep wiring: PASS')


def main():
    with tempfile.TemporaryDirectory(prefix='fgsa-deep-controls-') as scratch:
        tmp = Path(scratch)
        # Reuse the exact production extraction/digest functions. This is the same
        # probe pattern as record-fgsa-port-pcsa-baseline.py; never edit repo sources.
        helper = Path('scripts/V2Manifest.lean').read_text().split('def main (args : List String)')[0]
        probe = tmp / 'DeepProbe.lean'
        probe.write_text(helper + PROBE)
        snapshots, shallow = {}, {}
        for variant in ('base', 'body', 'proof', 'private', 'constructor'):
            target = tmp / variant
            target.mkdir()
            model = ('namespace AvailableChain.FGSA.DeepControl\n'
                     f'private def hidden : Nat := {2 if variant == "private" else 1}\n'
                     f'def reader : Nat := hidden{" + 1" if variant == "body" else ""}\n'
                     f'structure Carrier where\n  value : {"Bool" if variant == "constructor" else "Nat"}\n'
                     'end AvailableChain.FGSA.DeepControl\n')
            (target / 'DeepModel.lean').write_text(model)
            proof = 'Eq.refl reader' if variant != 'proof' else 'Eq.symm (Eq.refl reader)'
            (target / 'DeepStatements.lean').write_text('import DeepModel\n'
                'namespace AvailableChain.FGSA.DeepControl\n'
                f'theorem claim (_x : Carrier) : reader = reader := {proof}\n'
                'end AvailableChain.FGSA.DeepControl\n')
            for module in ('DeepModel', 'DeepStatements'):
                # Lake env supplies the repository and toolchain imports; add only
                # the isolated fixture directory to the inherited search path.
                env = dict(os.environ)
                env['LEAN_PATH'] = str(target) + os.pathsep + env.get('LEAN_PATH', '')
                command = ['lake', 'env', 'lean', f'--root={target}', '-o',
                           str(target / (module + '.olean')), str(target / (module + '.lean'))]
                result = subprocess.run(command, env=env, capture_output=True, text=True)
                assert result.returncode == 0, (command, result.stdout, result.stderr)
            result = subprocess.run(['lake', 'env', 'lean', '--run', str(probe), str(target)],
                                    capture_output=True, text=True)
            assert result.returncode == 0, (result.stdout, result.stderr)
            snapshots[variant] = check.strict_json(target / 'snapshot.json')
            shallow[variant] = (target / 'shallow').read_text()
        base, body, proof, private = (snapshots[v] for v in ('base', 'body', 'proof', 'private'))
        name = next(iter(base['entries']))
        before, after = base['entries'][name]['digest'], body['entries'][name]['digest']
        assert shallow['base'] == shallow['body'] == shallow['proof'] == shallow['private']
        print('CONTROL unchanged shallow hash for public/private body and proof edits: PASS')
        assert not check.check_deep(base, base, {})
        print('CONTROL deep unchanged positive: PASS')
        require_failure('public model body', lambda: check.check_deep(base, body, {}), 'DEEP UNEXPLAINED')
        require_failure('private cross-module body', lambda: check.check_deep(base, private, {}), 'DEEP UNEXPLAINED')
        require_failure('constructor field type',
            lambda: check.check_deep(base, snapshots['constructor'], {}), 'DEEP UNEXPLAINED')
        assert not check.check_deep(base, proof, {})
        assert base == proof
        assert (tmp / 'base/proof-value').read_text() != (tmp / 'proof/proof-value').read_text()
        print('CONTROL theorem proof only: PASS (identical complete snapshot)')
        exact = {name: record(before, after)}
        assert not check.check_deep(base, body, exact)
        print('CONTROL exact recorded exception: PASS')
        require_failure('stale exception', lambda: check.check_deep(base, base, exact), 'STALE EXCEPTION')
        wrong = {name: record(before, '0' * 64)}
        require_failure('wrong new digest', lambda: check.check_deep(base, body, wrong), 'EXCEPTION DIGEST MISMATCH')
        wrong = {name: record('0' * 64, after)}
        require_failure('wrong old digest', lambda: check.check_deep(base, body, wrong), 'EXCEPTION DIGEST MISMATCH')
        allow = tmp / 'allow.json'
        bad = deepcopy(exact)
        bad[name]['cause'] = ''
        allow.write_text(json.dumps(dict(format_version=1, exceptions=bad)))
        require_failure('unexplained exception', lambda: check.exceptions(allow, 64), 'UNEXPLAINED EXCEPTION')
        allow.write_text('{"format_version":1,"exceptions":{},"exceptions":{}}')
        require_failure('duplicate exception JSON', lambda: check.exceptions(allow, 64), 'DUPLICATE JSON KEY')
        ghost = {'Absent.Control': record(before, after)}
        require_failure('unknown stale exception', lambda: check.check_deep(base, base, ghost), 'STALE EXCEPTION')
        missing = deepcopy(base)
        missing['entries'][name]['dependencies'].pop()
        require_failure('incomplete closure', lambda: check.validate_graph(missing), 'INCOMPLETE ROOT')
        path = check.changed_path(name, base, body)
        assert 'claim -> AvailableChain.FGSA.DeepControl.reader' in path, path
        print('CONTROL changed dependency path: PASS')

        # The compiled snapshots also pass through the production CLI used by
        # V2Manifest, including file loading, SHA checks and exception parsing.
        fixture_manifest = tmp / 'fixture.md'
        fixture_manifest.write_text('### `DeepStatements`\n\n```text\n'
            f'theorem {name} {shallow["base"]}\n```\n')
        baseline = tmp / 'baseline.json'
        baseline_sha = tmp / 'baseline.sha256'
        stored = dict(base, provenance=check.provenance(fixture_manifest))
        check.write_baseline(baseline, baseline_sha, stored)
        for label, variant, allowances, status, reason in (
                ('body CLI rejected', 'body', {}, 1, 'DEEP UNEXPLAINED'),
                ('exact CLI accepted', 'body', exact, 0, 'DEEP PASS'),
                ('stale CLI rejected', 'base', exact, 1, 'STALE EXCEPTION'),
                ('proof CLI accepted', 'proof', {}, 0, 'DEEP PASS')):
            allow.write_text(json.dumps(dict(format_version=1, exceptions=allowances)))
            result = subprocess.run(['python3', 'scripts/fgsa-deep.py', '--check',
                '--snapshot', str(tmp / variant / 'snapshot.json'),
                '--manifest', str(fixture_manifest), '--baseline', str(baseline),
                '--sha', str(baseline_sha), '--allow', str(allow)],
                capture_output=True, text=True)
            assert result.returncode == status and reason in result.stdout + result.stderr, result
            print(f'CONTROL {label}: PASS')

        current = check.manifest(check.MANIFEST)
        frame = check.read_baseline(check.FRAME, check.FRAME_SHA)['entries']
        now = check.frame_entries(current)
        assert not check.check_frame(frame, now, check.exceptions(check.FRAME_ALLOW, 16))
        print('CONTROL frame complete-current positive: PASS')
        moved = deepcopy(current)
        moved_name = next(n for n in frame if n.endswith('TGeomNext'))
        moved[moved_name]['module'] = 'Moved.Outside.Frame.Selection'
        require_failure('frame moved module in complete manifest',
            lambda: check.check_frame(frame, moved, {}), 'FRAME KIND/MODULE CHANGED')
        name = next(iter(frame))
        changed = deepcopy(now)
        changed[name]['digest'] = '0' * 16
        require_failure('frame changed entry', lambda: check.check_frame(frame, changed, {}), 'FRAME UNEXPLAINED')
        removed = deepcopy(now)
        del removed[name]
        require_failure('frame removed entry', lambda: check.check_frame(frame, removed, {}), 'FRAME UNEXPLAINED')
        for label, baseline, sha_path in (('frame', check.FRAME, check.FRAME_SHA),
                ('deep', check.DEEP, check.DEEP.with_suffix('.sha256'))):
            require_failure(label + ' missing baseline',
                lambda: check.read_baseline(tmp / 'missing.json', sha_path), 'No such file')
            require_failure(label + ' missing SHA',
                lambda: check.read_baseline(baseline, tmp / 'missing.sha256'), 'No such file')
            wrong_sha = tmp / 'wrong.sha256'
            wrong_sha.write_text('0' * 64 + '\n')
            require_failure(label + ' wrong SHA',
                lambda: check.read_baseline(baseline, wrong_sha), 'BASELINE SHA256 MISMATCH')
        require_failure('missing exception file', lambda: check.exceptions(tmp / 'missing.json', 64),
                        'No such file')
        check_wiring()
    print('FGSA deep/frame controls: PASS')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true')
    if parser.parse_args().source_only:
        check_wiring()
    else:
        main()
