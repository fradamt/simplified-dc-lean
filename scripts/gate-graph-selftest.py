#!/usr/bin/env python3
"""Run the production gate graph with stub checks. No Lean, build, or FULL gate."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest.mock import patch

sys.dont_write_bytecode = True
REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / 'scripts'))
from audit_pool import AuditPool

HEAVY = ('fgsa-claims', 'check-fg-compose', 'check-fgsa', 'check-build',
         'check-fgsa-run', 'fgsa-manifest', 'pcsa-manifest')
CHEAP = ('build', 'fg-finality-freeze', 'fg-finality-coverage', 'catalog-lock',
         'v2-manifest', 'gen-manifest', 'fgsa-old-reads', 'proof-audit-coverage',
         'Generic-axioms', 'FGSA-axioms', 'FGSARun-axioms', 'FGCompose-axioms',
         'FGSACompose-axioms', 'PCSACompose-axioms', 'FGSafety-axioms',
         'FGSASafety-axioms', 'PCSASafety-axioms', 'FGSAGrowth-axioms', 'fgsa-blueprint')
AXIOMS = {
    'Generic': 'AvailableChainGeneric/Tests/Axioms.lean',
    'FGSA': 'AvailableChainFGSA/Tests/Axioms.lean',
    'FGSARun': 'AvailableChainFGSARun/Tests/Axioms.lean',
    'FGCompose': 'AvailableChainFGCompose/Tests/Axioms.lean',
    'FGSACompose': 'AvailableChainFGSAProofs/Tests/FGCompose.lean',
    'PCSACompose': 'AvailableChainPCSAProofs/Tests/FGCompose.lean',
    'FGSafety': 'AvailableChainFGCompose/Tests/SafetyAxioms.lean',
    'FGSASafety': 'AvailableChainFGSAProofs/Tests/FGSafety.lean',
    'PCSASafety': 'AvailableChainPCSAProofs/Tests/FGSafety.lean',
    'FGSAGrowth': 'AvailableChainFGSAProofs/Tests/WeakContinuationGrowthAssemblyAxioms.lean',
}
STUB = r'''
import fcntl, json, os, sys, time
from pathlib import Path
name = sys.argv[1]
heavy = name in json.loads(os.environ['STUB_HEAVY'])
def event(kind):
    with Path(os.environ['STUB_EVENTS']).open('a') as out:
        fcntl.flock(out, fcntl.LOCK_EX)
        out.write(json.dumps(dict(name=name, kind=kind, time=time.monotonic(),
                                 neg=os.environ.get('NEG'))) + '\n')
event('start')
delay = 8 if name == 'check-fg-compose' and os.environ.get('STUB_FAIL') else 0.8
time.sleep(delay if heavy else 0.01)
event('end')
if name.endswith('-axioms'):
    print('Stub does not depend on any axioms')
sys.exit(9 if name == os.environ.get('STUB_FAIL') else 0)
'''


def write(path, text, executable=False):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    if executable:
        path.chmod(0o755)


def records(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def peak(events, names):
    active = maximum = 0
    for event in events:
        if event['name'] not in names:
            continue
        active += 1 if event['kind'] == 'start' else -1
        maximum = max(maximum, active)
    return maximum


def graph(root, tier, slots, fail=''):
    scripts = root / 'scripts'
    scripts.mkdir(parents=True)
    (root / '.lake').mkdir()
    for name in ('gate.sh', 'gate-common.sh'):
        shutil.copy2(REPO / 'scripts' / name, scripts / name)
    # Test the driver after precheck. Real source prechecks run separately.
    with (scripts / 'gate-common.sh').open('a') as out:
        out.write('\ngate_precheck() { echo "STUB PRECHECK PASS"; }\n')
    write(scripts / 'stub.py', STUB)
    for name in HEAVY:
        script = name if name.startswith('check-') else 'check-' + name
        write(scripts / (script + '.sh'),
              '#!/usr/bin/env bash\nset -euo pipefail\nsource scripts/gate-common.sh\n'
              f'gate_with_slot python3 scripts/stub.py {name}\n')
    for script, name in (('check-fg-finality-freeze.py', 'fg-finality-freeze'),
                         ('check-fg-finality-coverage.py', 'fg-finality-coverage'),
                         ('check-proof-coverage.py', 'proof-audit-coverage'),
                         ('check-fgsa-blueprint.py', 'fgsa-blueprint')):
        write(scripts / script, f'import runpy,sys\nsys.argv = ["stub", {name!r}]\n'
              'runpy.run_path("scripts/stub.py")\n')
    for path in AXIOMS.values():
        write(root / path, '#print axioms Stub\n')
    # Lake only selects stub checks. No toolchain is called.
    write(root / 'bin/lake', '#!/usr/bin/env python3\n'
          'import os,subprocess,sys\n'
          f'axioms = {AXIOMS!r}\n'
          'a = sys.argv[1:]\n'
          'if "--libraries" in a: print("Stub"); sys.exit(0)\n'
          'if a[0] == "build": name = "build"\n'
          'elif "scripts/CatalogLock.lean" in a: name = "catalog-lock"\n'
          'elif "scripts/CheckFGSAOldReads.lean" in a: name = "fgsa-old-reads"\n'
          'elif "scripts/V2Manifest.lean" in a:\n'
          '    name = "gen-manifest" if "gen" in a else "v2-manifest"\n'
          'else: name = next(k + "-axioms" for k,v in axioms.items() if v in a)\n'
          'sys.exit(subprocess.call([sys.executable,"scripts/stub.py",name]))\n', True)
    # Portable harness: no Linux scope is needed for these stub commands.
    write(root / 'bin/uname', '#!/usr/bin/env bash\necho Darwin\n', True)
    events = root / 'events'
    env = dict(os.environ, PATH=str(root / 'bin') + os.pathsep + os.environ['PATH'],
               GATE_SLOTS=str(slots), LEAN_SLOTS=str(slots), GATE_FF_GRACE='2',
               STUB_EVENTS=str(events), STUB_HEAVY=json.dumps(HEAVY), STUB_FAIL=fail,
               SOURCE_ONLY='0', NEG='0' if tier == 'full' else '1', SKIP_CONE='1')
    for key in ('GATE_SLOT_DIR', 'GATE_SLOT_HELD', 'GATE_NO_BUILD'):
        env.pop(key, None)
    result = subprocess.run(['bash', 'scripts/gate.sh', '--tier', tier], cwd=root,
                            env=env, capture_output=True, text=True)
    seen = records(events)
    starts = [e['name'] for e in seen if e['kind'] == 'start']
    expected = list(CHEAP if tier == 'full' else CHEAP[:-1])
    early = fail in expected
    assert starts[:len(expected)] == (expected[:expected.index(fail) + 1]
                                    if early else expected), (starts, result)
    maximum = peak(seen, HEAVY)
    assert maximum <= slots, (maximum, result)
    heavy_starts = starts[len(expected):] if not early else []
    if slots == 1:
        assert heavy_starts == list(HEAVY), heavy_starts
    elif not early:
        assert set(heavy_starts[:2]) == set(HEAVY[:2]), heavy_starts
    logs = next((root / '.lake').glob('gate-logs.*'))
    if fail:
        assert result.returncode == 1 and f'GATE FAIL tier={tier}' in result.stdout, result
        if fail != 'build':
            assert 'fail-fast:' in result.stdout, result
        assert not (root / '.lake/gate-last-full').exists()
        if early:
            assert not set(starts) & set(HEAVY), starts
        else:
            assert 'stopped:' in result.stdout, result
            assert not all((logs / (n + '.result')).exists() for n in HEAVY), result
            assert set(heavy_starts) == set(HEAVY[:2]), heavy_starts
            assert not any(e['name'] == 'check-fg-compose' and e['kind'] == 'end'
                           for e in seen), seen
    else:
        assert result.returncode == 0 and f'GATE PASS tier={tier}' in result.stdout, result
        assert set(starts[len(expected):]) == set(HEAVY), starts
        assert maximum == slots, (maximum, result)
        assert all(e['neg'] == ('1' if tier == 'full' else '0')
                   for e in seen if e['name'] in HEAVY)
        if tier == 'full':
            spec = importlib.util.spec_from_file_location('receipt', REPO / 'scripts/full-pass.py')
            receipt = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(receipt)
            assert {p.stem for p in logs.glob('*.result')} == set(receipt.STEPS)
            with patch.object(receipt, 'clean_head'), patch.object(receipt, 'git',
                              return_value='policy'), patch.object(receipt.subprocess, 'run'):
                receipt.sign(root, 'head', 'policy', logs, root / 'key', logs / 'receipt.json')
                for bad in ('missing', 'extra'):
                    target = logs / ('build.result' if bad == 'missing' else 'extra.result')
                    if bad == 'missing':
                        saved = target.read_text()
                        target.unlink()
                    else:
                        target.write_text('0 0\n')
                    try:
                        receipt.sign(root, 'head', 'policy', logs, root / 'key', logs / 'bad.json')
                    except ValueError as exc:
                        assert 'STEP SET' in str(exc), exc
                    else:
                        raise AssertionError('receipt accepted ' + bad)
                    if bad == 'missing':
                        target.write_text(saved)
                    else:
                        target.unlink()
            print('receipt exact step set and missing/extra rejection: PASS')
    print(f'graph {tier} slots={slots} {fail or "pass"}: peak={maximum} rc={result.returncode}')
    print('start order: ' + ' -> '.join(starts))
    if fail:
        print('\n'.join(line for line in result.stdout.splitlines()
                        if line.startswith(('fail-fast:', 'GATE '))))


def copy_control(root):
    source, target = root / 'source', root / 'private'
    for path in ('AvailableChainFGSA/Tests/Keep.lean', '.lake/build/keep.olean',
                 '.lake/config/keep', '.lake/packages/dependency/keep'):
        write(source / path, 'unchanged\n')
    write(source / '.lake/gate-logs.live/log', 'excluded\n')
    write(source / '.git/config', 'excluded\n')
    subprocess.run(['bash', '-c', 'set -e; source "$1"; gate_copy_control_tree "$2" "$3"',
                    'copy-control', str(REPO / 'scripts/gate-common.sh'),
                    str(source), str(target)], check=True)
    assert not (target / '.git').exists()
    assert set(p.name for p in (target / '.lake').iterdir()) == {'build', 'config', 'packages'}
    for path in ('AvailableChainFGSA/Tests/Keep.lean', '.lake/build/keep.olean',
                 '.lake/config/keep', '.lake/packages/dependency/keep'):
        assert not (target / path).is_symlink()
        assert (source / path).stat().st_ino != (target / path).stat().st_ino
        assert int((source / path).stat().st_mtime) == int((target / path).stat().st_mtime)
        (target / path).write_text('private edit\n')
        assert (source / path).read_text() == 'unchanged\n'
    fallback = root / 'rsync'
    subprocess.run(['bash', '-c',
                    'set -e; source "$1"; cp() { return 1; }; '
                    'gate_copy_control_tree "$2" "$3"', 'copy-fallback',
                    str(REPO / 'scripts/gate-common.sh'), str(source), str(fallback)], check=True)
    for path in ('.lake/build/keep.olean', '.lake/packages/dependency/keep'):
        (fallback / path).write_text('fallback edit\n')
        assert (source / path).read_text() == 'unchanged\n'
    # Exercise the actual C23 function, including its diagnostic and cleanup assertions.
    text = (REPO / 'scripts/check-fgsa.sh').read_text()
    function = text[text.index('control_glob_build() {'):text.index('control_closure() {')]
    write(source / 'bin/lake', '#!/usr/bin/env bash\n'
          'test -f AvailableChainFGSA/Tests/NegBuildC23.lean || exit 2\n'
          'echo private-build > .lake/build/keep.olean\n'
          'echo private-package > .lake/packages/dependency/keep\n'
          'echo "AvailableChainFGSA.Tests.NegBuildC23 rejected"\nexit 1\n', True)
    (source / '.lake/control').mkdir()
    harness = ('set -euo pipefail\nsource "$1"\nneg=$PWD/.lake/control\n'
               'run() { set +e; out=$("$@" 2>&1); code=$?; set -e; }\n'
               'expect_fail() { test "$2" = 1; [[ $3 == *"$4"* ]]; }\n' + function +
               '\ncontrol_glob_build\n')
    subprocess.run(['bash', '-c', harness, 'c23-control', str(REPO / 'scripts/gate-common.sh')],
                   cwd=source, env=dict(os.environ, PATH=str(source / 'bin') + os.pathsep +
                                       os.environ['PATH']), check=True)
    assert not (source / 'AvailableChainFGSA/Tests/NegBuildC23.lean').exists()
    assert (source / '.lake/build/keep.olean').read_text() == 'unchanged\n'
    assert (source / '.lake/packages/dependency/keep').read_text() == 'unchanged\n'
    print('private source/build/config/packages (clone and rsync); C23 cleanup: PASS')


def pool_slots(root, slots):
    root.mkdir()
    events = root / 'events'
    stub = root / 'stub.py'
    write(stub, STUB)
    env = dict(os.environ, GATE_SLOTS=str(slots), GATE_SLOT_DIR=str(root / 'slots'),
               STUB_EVENTS=str(events), STUB_HEAVY=json.dumps(['a', 'b', 'c']), STUB_FAIL='')
    env.pop('GATE_SLOT_HELD', None)
    pool = AuditPool(root, 3, slot_script=REPO / 'scripts/gate-common.sh')
    pool.run_pool([(n, [sys.executable, str(stub), n], dict(env=env, cwd=root))
                   for n in ('a', 'b', 'c')])
    maximum = peak(records(events), {'a', 'b', 'c'})
    assert maximum == slots, maximum
    assert not list((root / 'slots').glob('slot.*'))
    print(f'audit pool workers=3 slots={slots}: peak={maximum}; slots released: PASS')


with tempfile.TemporaryDirectory(prefix='gate-graph-') as temp:
    root = Path(temp)
    for tier, slots, fail in (('full', 1, ''), ('full', 2, ''), ('full', 2, 'build'),
                              ('full', 2, 'fg-finality-freeze'),
                              ('full', 2, 'fgsa-claims'), ('merge', 2, '')):
        graph(root / f'{tier}-{slots}-{fail or "pass"}', tier, slots, fail)
    copy_control(root / 'copy')
    for slots in (1, 2):
        pool_slots(root / f'pool-{slots}', slots)
print('gate-graph-selftest: PASS')
