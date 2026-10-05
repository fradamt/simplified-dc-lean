#!/usr/bin/env python3
"""Fast negative controls for policy data, scope, and signed FULL receipts."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
sys.dont_write_bytecode = True
import tempfile

from check_inventory import parse_names
import import_policy as P

REPO = Path(__file__).resolve().parent.parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, REPO / 'scripts' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


scope = load('precheck-scope')
full = load('full-pass')
layers = load('check-layers')
guards = load('guard-lists')
coverage = load('check-proof-coverage')


def refused(label, reason, action):
    try:
        action()
    except (ValueError, OSError) as error:
        assert reason in str(error), (label, str(error))
        print(f'CONTROL {label}: PASS ({reason})')
    else:
        raise AssertionError(f'accepted {label}')


for text in ('()', "('__import__(\"os\")',)", "('valid', 2)", "['valid']"):
    refused('inventory data', 'inventory' if text == '()' else 'inventory',
            lambda: parse_names(text, 'inventory'))
assert parse_names("('AvailableChain.FGSA.Run.Base₂',)", 'unicode')
refused('duplicate inventory', 'duplicate inventory',
        lambda: parse_names("('valid', 'valid')", 'inventory'))
for name in guards.LISTS:
    body = "#!/bin/bash\nexec python3 - <<'PY'\n"
    body += '\n'.join(f'{key} = ' + ("('a', 'a')" if key == name else "('a',)")
                      for key in guards.LISTS) + '\nPY\n'
    refused('duplicate guard ' + name, 'duplicate ' + name,
            lambda: guards.read_guard(body, 'control'))
refused('duplicate import entries', 'duplicate import-policy entry',
        lambda: P.expand(['Init.**', 'Init.**']))
refused('duplicate JSON keys', 'duplicate import-policy key',
        lambda: P.read_policy('{"groups": {}, "groups": {}, "profiles": {}}'))
refused('duplicate raw import rows', 'duplicate import-policy entry',
        lambda: P.read_policy('{"groups":{"x":["Init", "Init"]},"profiles":{}}'))
refused('duplicate expanded import rows', 'duplicate expanded import-policy entry',
        lambda: P.expand(['@foundation', 'Init.**']))
for name in ('../Wrong', '@missing', 'AvailableChain*'):
    refused('import-policy data', 'import-policy', lambda: P.expand([name]))
for lib in P.POLICY['profiles']:
    assert P.allowed(lib, 'Model', lib + '.Model.Control')
    for layer, dep in [('Model', lib + '.Proofs.Control'),
                       ('root', 'Mathlib.Data.Nat.Basic'),
                       ('Proofs', 'AvailableChainKit.Engine.Clock')]:
        assert not P.allowed(lib, layer, dep), (lib, layer, dep)
print('CONTROL shared import layer refusals: PASS')
for text in ('', 'ALLOWED_PATHS:\n```text\n\n```',
             'ALLOWED_PATHS:\n```text\n../outside\n```',
             'ALLOWED_PATHS:\n```text\n/a\n```',
             'ALLOWED_PATHS:\n```text\n**\n```',
             'ALLOWED_PATHS:\n```text\n.\n```'):
    refused('brief syntax', 'ALLOWED_PATHS', lambda: scope.allowed_paths(text))


def call(args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, stderr=subprocess.STDOUT)


with tempfile.TemporaryDirectory(prefix='policy-controls-') as tmp:
    root = Path(tmp).resolve()
    # Exercise the gate entry point before any precheck, build or allocation.
    gate = root / 'gate/scripts'
    gate.mkdir(parents=True)
    for name in ('gate.sh', 'gate-common.sh'):
        shutil.copy2(REPO / 'scripts' / name, gate / name)
    result = subprocess.run(['bash', str(gate / 'gate.sh'), '--tier', 'full'],
                            env=dict(os.environ, SOURCE_ONLY='1'), capture_output=True, text=True)
    assert result.returncode == 2 and 'GATE REFUSED: SOURCE_ONLY' in result.stderr
    assert not (gate.parent / '.lake').exists()
    print('CONTROL gate refuses inherited SOURCE_ONLY before work: PASS')
    data = root / 'coverage'
    for label, raw in (
        ('audit key', "{'A': {'O': ('n',)}, 'A': {'O': ('m',)}}"),
        ('owner key', "{'A': {'O': ('n',), 'O': ('m',)}}"),
        ('name', "{'A': {'O': ('n', 'n')}}"),
        ('name across owners', "{'A': {'O': ('n',), 'P': ('n',)}}"),
    ):
        data.write_text(raw)
        refused('duplicate coverage ' + label, 'duplicate proof coverage',
                lambda: coverage.read_coverage(data))
    data.write_text(repr({'A': {'O': ("B'_resetF", 'block?_proposal', "clock_gate'")}}))
    assert len(coverage.read_coverage(data)) == 3
    print('CONTROL coverage primes and question marks: PASS')
    generated = root / 'generated'
    generated.mkdir()
    (generated / 'AvailableChainCheckSupport').mkdir()
    for name in ('generate-import-policy.py', 'import_policy.py', 'import-policy.json',
                 'import-policy.sh', 'AvailableChainCheckSupport/ImportPolicy.lean'):
        shutil.copy2(REPO / 'scripts' / name, generated / name)
    command = [sys.executable, str(generated / 'generate-import-policy.py'), '--check']
    call(command)
    with (generated / 'import-policy.sh').open('a') as output:
        output.write('# stale generated data\n')
    result = subprocess.run(command, capture_output=True, text=True)
    assert result.returncode != 0 and 'IMPORT POLICY DRIFT' in result.stderr
    print('CONTROL stale generated import policy: PASS')

    # Exact KitFG names must refer to a real module in the chosen checkout.
    source = root / 'layers'
    source.mkdir()
    shutil.copy2(REPO / 'lakefile.toml', source / 'lakefile.toml')
    (source / 'scripts/baselines').mkdir(parents=True)
    shutil.copy2(REPO / 'scripts/CatalogLock.lean', source / 'scripts/CatalogLock.lean')
    data = source / 'scripts/baselines/kitfg-def-modules.txt'
    for name, reason in [('AvailableChainKitFG.ViewLock', 'invalid short'),
                         ('Missing', 'missing KitFG'), ('ViewLock.Extra', 'invalid short')]:
        data.write_text(name + '\n')
        refused('KitFG definition ' + name, reason, lambda: layers.load_context(source))
    data.write_text('ViewLock\n')
    (source / 'AvailableChainKitFG').mkdir()
    (source / 'AvailableChainKitFG/ViewLock.lean').write_text('module\n')
    assert layers.load_context(source).definitions == {'AvailableChainKitFG.ViewLock'}
    print('CONTROL KitFG short existing module: PASS')

    # A private fixture repository supplies the trusted policy and exact HEAD.
    repo = root / 'repo'
    repo.mkdir()
    call(['git', 'init', '-q', str(repo)])
    (repo / 'scripts').mkdir()
    for name in ('precheck.sh', 'full-pass.py'):
        shutil.copy2(REPO / 'scripts' / name, repo / 'scripts' / name)
    (repo / 'allowed').mkdir()
    (repo / 'allowed/a').write_text('base\n')
    (repo / 'forbidden-source').write_text('base\n')
    key = root / 'key'
    call(['ssh-keygen', '-q', '-t', 'ed25519', '-N', '', '-f', str(key)])
    (repo / 'scripts/full-pass-signers').write_text(
        full.IDENTITY + ' ' + key.with_suffix('.pub').read_text())
    call(['git', 'add', '.'], repo)
    tree = call(['git', 'write-tree'], repo).decode().strip()
    head = subprocess.check_output(['git', '-c', 'user.name=Control',
        '-c', 'user.email=control@example.invalid', 'commit-tree', tree],
        cwd=repo, input=b'isolated policy fixture\n').decode().strip()
    call(['git', 'update-ref', 'HEAD', head], repo)
    brief = root / 'brief'
    brief.write_text('ALLOWED_PATHS:\n```text\nallowed/\n```\n')
    (repo / 'allowed/a').write_text('edit\n')
    scope.check(repo, head, brief)
    (repo / 'outside').write_text('untracked\n')
    refused('untracked scope', 'DIFF SCOPE REFUSED', lambda: scope.check(repo, head, brief))
    call(['git', 'add', 'outside'], repo)
    refused('staged scope', 'DIFF SCOPE REFUSED', lambda: scope.check(repo, head, brief))
    call(['git', 'reset', '-q', '--', 'outside'], repo)
    (repo / 'outside').unlink()
    (repo / 'forbidden-source').rename(repo / 'allowed/b')
    refused('rename source scope', 'DIFF SCOPE REFUSED',
            lambda: scope.check(repo, head, brief))
    (repo / 'allowed/b').rename(repo / 'forbidden-source')
    (repo / 'forbidden-source').unlink()
    refused('deletion scope', 'DIFF SCOPE REFUSED', lambda: scope.check(repo, head, brief))
    call(['git', 'checkout', '--', 'forbidden-source'], repo)
    # A rename is checked as a deletion and an addition, including its old path.
    (repo / 'allowed/a').rename(repo / 'outside')
    refused('rename scope', 'DIFF SCOPE REFUSED', lambda: scope.check(repo, head, brief))
    (repo / 'outside').unlink()
    call(['git', 'checkout', '--', 'allowed/a'], repo)
    receipt = root / 'receipt'
    refused('missing receipt', 'MISSING', lambda: full.verify(repo, repo, receipt))
    record = dict(version=1, head=head, policy=head, tier='full', result='PASS')
    receipt.write_text(json.dumps(record))
    refused('forged unsigned receipt', 'SIGNATURE REFUSED',
            lambda: full.verify(repo, repo, receipt))
    # Sign through the same producer as gate.sh. Missing/failed steps must refuse.
    logs = root / 'logs'
    logs.mkdir()
    refused('empty FULL step set', 'FAILED OR MISSING STEP SET',
            lambda: full.sign(repo, head, head, logs, key, receipt))
    (logs / 'build.result').write_text('0 1\n')
    refused('partial FULL step set', 'FAILED OR MISSING STEP SET',
            lambda: full.sign(repo, head, head, logs, key, receipt))
    for step in full.STEPS:
        (logs / (step + '.result')).write_text('0 1\n')
    (logs / 'build.result').write_text('1 1\n')
    refused('failed FULL step', 'FAILED OR MISSING STEP',
            lambda: full.sign(repo, head, head, logs, key, receipt))
    (logs / 'build.result').unlink()
    refused('missing FULL step', 'FAILED OR MISSING STEP',
            lambda: full.sign(repo, head, head, logs, key, receipt))
    (logs / 'build.result').write_text('0 1\n')
    (logs / 'unexpected.result').write_text('0 1\n')
    refused('extra FULL step', 'FAILED OR MISSING STEP SET',
            lambda: full.sign(repo, head, head, logs, key, receipt))
    (logs / 'unexpected.result').unlink()
    full.sign(repo, head, head, logs, key, receipt)
    full.verify(repo, repo, receipt)
    output = call(['bash', str(repo / 'scripts/precheck.sh'),
                   '--full-pass', str(receipt), str(repo)]).decode()
    assert 'MAIN POLICY COPY SKIPPED: verified exact-head FULL PASS' in output
    print('CONTROL precheck verified FULL mode: PASS')
    signed = receipt.read_bytes()
    for field, value, reason in [('head', '0' * 40, 'WRONG HEAD'),
                                  ('tier', 'merge', 'NOT FULL PASS'),
                                  ('policy', '0' * 40, 'WRONG POLICY HEAD'),
                                  ('result', 'FAIL', 'NOT FULL PASS')]:
        receipt.write_text(json.dumps(dict(record, **{field: value})))
        refused('receipt ' + field, reason, lambda: full.verify(repo, repo, receipt))
    receipt.write_bytes(signed + b' ')
    refused('forged signed payload', 'SIGNATURE REFUSED',
            lambda: full.verify(repo, repo, receipt))
    receipt.write_bytes(signed)
    (repo / 'allowed/a').write_text('dirty\n')
    refused('dirty exact head', 'DIRTY TARGET', lambda: full.verify(repo, repo, receipt))
    call(['git', 'checkout', '--', 'allowed/a'], repo)
    # An ignored source can change a Lake glob without changing the commit.
    (repo / '.git/info/exclude').write_text('hidden.lean\n')
    (repo / 'hidden.lean').write_text('def hidden : Nat := 0\n')
    refused('ignored source', 'IGNORED SOURCE', lambda: full.verify(repo, repo, receipt))
    (repo / 'hidden.lean').unlink()
    # Local trust edits do not add an issuer; only main's committed file is read.
    other_key = root / 'other-key'
    call(['ssh-keygen', '-q', '-t', 'ed25519', '-N', '', '-f', str(other_key)])
    receipt.with_suffix('.sig').unlink()
    call(['ssh-keygen', '-Y', 'sign', '-f', str(other_key), '-n', full.NAMESPACE,
          str(receipt)])
    refused('untrusted issuer', 'SIGNATURE REFUSED', lambda: full.verify(repo, repo, receipt))

print('policy-controls: PASS')
