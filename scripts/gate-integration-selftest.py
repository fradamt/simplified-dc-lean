#!/usr/bin/env python3
"""Check each provisional eligibility class without a Lean process."""
import importlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from integration_scope import select

REPO = Path(__file__).resolve().parents[1]


def write(root, path, text):
    target = root / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text)


def commit(root):
    subprocess.run(['git', 'add', '.'], cwd=root, check=True)
    subprocess.run(['git', '-c', 'user.name=Control', '-c',
                    'user.email=control@example.invalid', 'commit', '-qm', 'control'],
                   cwd=root, check=True)
    return subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()


with tempfile.TemporaryDirectory(prefix='gate-integration-') as scratch:
    seed = Path(scratch) / 'seed'
    seed.mkdir()
    subprocess.run(['git', 'init', '-q', str(seed)], check=True)
    subprocess.run(['git', 'symbolic-ref', 'HEAD', 'refs/heads/p0-control'], cwd=seed, check=True)
    (seed / 'scripts').mkdir()
    for name in ('checker-paths.txt', 'gate.sh', 'check-fgsa-claims.sh', 'check-fg-compose.sh',
                 'check-fgsa-manifest.sh', 'check-fgsa-run.sh', 'check-fgsa.sh'):
        shutil.copy2(REPO / 'scripts' / name, seed / 'scripts' / name)
    snapshot = dict(entries={'old': {'digest': 'abc'}}, nodes={'old': {'kind': 'theorem'}},
                    node_order=['old'], format_version=1, pins={'toolchain': 'fixed'})
    files = {
        'scripts/fgsa-claims-expected.txt': "('Old.name',)\n",
        'scripts/claims-model-scope.txt': 'AvailableChainFGSA.Model.Objects Old.name\n',
        'scripts/gly-f13-allow.txt': 'Old.exemption\n',
        'scripts/baselines/check-layers.txt': 'old finding\n',
        'scripts/unported-libraries.txt': 'AvailableChainPCSA\n',
        'scripts/fixture.py': 'value = 1\n',
        'lean-toolchain': 'fixed\n', 'lakefile.toml': 'name = "control"\n',
        'lake-manifest.json': '{}\n',
        'AvailableChainFGSAProofs/Proofs/Shared/Keep.lean': 'module\n',
        'AvailableChainGeneric.lean': 'module\npublic import AvailableChainGeneric.Keep\n',
        'AvailableChainGeneric/Keep.lean': 'module\npublic section\ndef Old.name := 1\n',
        'AvailableChainGeneric/Extract.lean': 'module\npublic import Init\n\npublic section\nnamespace Old\ndef moved := 1\nend Old\n',
        'AvailableChainFGSA/Tests/Control.lean': 'module\n',
        'docs/api/gen-deep.json': json.dumps(snapshot),
    }
    for path, text in files.items():
        write(seed, path, text)
    base = commit(seed)

    def candidate(label, edits, reviewed=(), eligible=False, extractions=()):
        root = Path(scratch) / label
        shutil.copytree(seed, root)
        for path, text in edits.items():
            if text is None:
                (root / path).unlink()
            else:
                write(root, path, text)
        commit(root)
        try:
            result = select(root, base, reviewed=reviewed, extractions=extractions)
        except (ValueError, subprocess.CalledProcessError) as error:
            assert not eligible, (label, error)
            print(f'CONTROL integration {label}: REFUSED ({error})')
            return root
        assert eligible, ('ineligible candidate accepted', label, result)
        assert result['base'] == base and result['head'] != base
        assert result['main_accepted'] is False and result['full_receipt'] is False
        assert bool(result['deferred_controls']) == (not reviewed)
        assert result['neg'] == int(bool(reviewed))
        assert len(result['reviewed_extractions']) == len(extractions)
        for record in result['reviewed_extractions']:
            assert record['base'] == base and record['head'] == result['head']
            assert record['before_sha256'] == record['target_sha256']
        assert not (root / '.lake/gate-last-full').exists()
        print(f'CONTROL integration {label}: eligible; no FULL stamp')
        return root

    added = dict(snapshot)
    added['entries'] = dict(snapshot['entries'], new={'digest': 'def'})
    added['nodes'] = dict(snapshot['nodes'], new={'kind': 'theorem'})
    added['node_order'] = ['old', 'new']
    claims = (seed / 'scripts/check-fgsa-claims.sh').read_text()
    ast_added = claims.replace("ORDER = ('Recurrence',", "ORDER = ('NewLane', 'Recurrence',")
    eligible = candidate('additions', {
        'scripts/fgsa-claims-expected.txt': "('Old.name', 'New.name')\n",
        'scripts/claims-model-scope.txt': files['scripts/claims-model-scope.txt'] +
            'AvailableChainFGSA.Model.RowCore New.name\n',
        'docs/api/gen-deep.json': json.dumps(added),
        'scripts/check-fgsa-claims.sh': ast_added,
        'AvailableChainFGSAProofs/Proofs/Shared/New.lean': 'module\n',
        'AvailableChainFGSAProofs/Tests/PackageG0.lean': 'module\n',
    }, eligible=True)
    candidate('source-addition', {'AvailableChainGeneric/Keep.lean':
              files['AvailableChainGeneric/Keep.lean'] + 'def New.name : Nat := 2\n'}, eligible=True)
    candidate('facade-import-addition', {'AvailableChainGeneric.lean':
              files['AvailableChainGeneric.lean'] + 'public import AvailableChainGeneric.New\n',
              'AvailableChainGeneric/New.lean': 'module\npublic section\ndef New.name := 2\n'}, eligible=True)
    extraction = {
        'AvailableChainGeneric/Extract.lean': 'module\npublic import Init\n\npublic import AvailableChainGeneric.Moved\n',
        'AvailableChainGeneric/Moved.lean': files['AvailableChainGeneric/Extract.lean'],
    }
    pair = 'AvailableChainGeneric/Extract.lean:AvailableChainGeneric/Moved.lean'
    candidate('reviewed-extraction', extraction, extractions=[pair], eligible=True)
    candidate('unreviewed-extraction', extraction)
    candidate('extraction-changed-body', dict(extraction, **{
        'AvailableChainGeneric/Moved.lean': files['AvailableChainGeneric/Extract.lean'].replace(':= 1', ':= 2')}),
        extractions=[pair])
    candidate('extraction-removed-import', dict(extraction, **{
        'AvailableChainGeneric/Extract.lean': 'module\npublic import AvailableChainGeneric.Moved\n'}),
        extractions=[pair])
    candidate('extraction-existing-target', {'AvailableChainGeneric/Extract.lean':
        'module\npublic import AvailableChainGeneric.Keep\n'},
        extractions=['AvailableChainGeneric/Extract.lean:AvailableChainGeneric/Keep.lean'])
    for label, edits in (
        ('declaration-removal', {'AvailableChainGeneric/Keep.lean': 'module\npublic section\n'}),
        ('replaced-file', {'AvailableChainGeneric/Keep.lean': 'module\n'}),
        ('facade-import-removal', {'AvailableChainGeneric.lean': 'module\n'}),
        ('existing-body-change', {'AvailableChainGeneric/Keep.lean':
            files['AvailableChainGeneric/Keep.lean'].replace(':= 1', ':= 2')}),
        ('ambiguous-edit', {'AvailableChainGeneric/Keep.lean':
            files['AvailableChainGeneric/Keep.lean'] + 'set_option maxRecDepth 0\n'}),
        ('body-insertion', {'AvailableChainGeneric/Extract.lean':
            files['AvailableChainGeneric/Extract.lean'].replace('end Old', '  + 2\nend Old')}),
        ('scope-removal-existing-file', {'AvailableChainGeneric/Extract.lean':
            files['AvailableChainGeneric/Extract.lean'].replace('namespace Old\n', '').replace('end Old\n', '')}),
        ('checker-logic', {'scripts/check-fgsa-claims.sh': ast_added.replace('workers = audit_workers()', 'workers = 1')}),
        ('parser', {'scripts/new-parser.py': 'print("unsafe")\n'}),
        ('control-fixture', {'AvailableChainFGSA/Tests/Control.lean': 'module\n-- changed\n'}),
        ('toolchain', {'lean-toolchain': 'changed\n'}),
        ('dependency', {'lake-manifest.json': '{"dependency": 1}\n'}),
        ('lakefile', {'lakefile.toml': 'name = "changed"\n'}),
        ('scope-removal', {'AvailableChainFGSAProofs/Proofs/Shared/Keep.lean': None}),
        ('scope-switch', {'scripts/unported-libraries.txt': ''}),
        ('inventory-removal', {'scripts/fgsa-claims-expected.txt': "('New.name',)\n"}),
        ('map-change', {'scripts/claims-model-scope.txt': 'AvailableChainFGSA.Model.Objects New.name\n'}),
        ('snapshot-change', {'docs/api/gen-deep.json': json.dumps(dict(added, entries={'old': {}, 'new': {}}))}),
        ('snapshot-removal', {'docs/api/gen-deep.json': json.dumps(dict(added, entries={'new': {}}))}),
        ('snapshot-pins', {'docs/api/gen-deep.json': json.dumps(dict(added, pins={'toolchain': 'changed'}))}),
        ('snapshot-duplicates', {'docs/api/gen-deep.json': '{"entries": {}, "entries": {}}'}),
        ('unknown-data', {'scripts/new-data.txt': 'New.name\n'}),
        ('baseline-growth', {'scripts/baselines/check-layers.txt': 'old finding\nnew finding\n'}),
        ('allow-growth', {'scripts/gly-f13-allow.txt': 'Old.exemption\nNew.exemption\n'}),
        ('exclusion-growth', {'scripts/new-exclusions.txt': 'New.module\n'}),
        ('wildcard', {'scripts/claims-model-scope.txt': files['scripts/claims-model-scope.txt'] + 'AvailableChainFGSA.Model.* New.name\n'}),
        ('constant-expression', {'scripts/check-fgsa-claims.sh': claims.replace("ORDER = ('Recurrence',", "ORDER = (str('NewLane'), 'Recurrence',")}),
        ('constant-removal', {'scripts/check-fgsa-claims.sh': claims.replace("ORDER = ('Recurrence',", "ORDER = ('NewLane',")}),
        ('unknown-constant', {'scripts/check-fgsa-claims.sh': ast_added.replace("'Classical.choice'", "'New.permission'") + '\n# outside heredoc\n'}),
    ):
        candidate(label, edits)
    reviewed = candidate('reviewed-allow', {'scripts/gly-f13-allow.txt': 'Old.exemption\nNew.exemption\n'},
                         reviewed=['scripts/gly-f13-allow.txt'], eligible=True)
    candidate('reviewed-baseline', {'scripts/baselines/check-layers.txt': 'old finding\nnew finding\n'},
              reviewed=['scripts/baselines/check-layers.txt'], eligible=True)
    candidate('review-does-not-permit-logic', {'scripts/fixture.py': 'value = 2\n'}, reviewed=['scripts/fixture.py'])
    candidate('review-does-not-permit-allow-code', {'scripts/new-allow.py': 'print("unsafe")\n'}, reviewed=['scripts/new-allow.py'])
    candidate('review-does-not-permit-removal', {'scripts/gly-f13-allow.txt': 'New.exemption\n'}, reviewed=['scripts/gly-f13-allow.txt'])
    for label, operation in (
        ('dirty', lambda: write(eligible, 'scripts/untracked.py', 'pass\n')),
        ('main', lambda: subprocess.run(['git', 'branch', '-M', 'main'], cwd=reviewed, check=True)),
    ):
        operation()
        try:
            select(eligible if label == 'dirty' else reviewed, base)
        except ValueError:
            print(f'CONTROL integration {label}: REFUSED')
        else:
            raise AssertionError(label)
    receipt = importlib.import_module('full-pass')
    logs = Path(scratch) / 'logs'
    logs.mkdir()
    (logs / 'integration.json').write_text('{}')
    try:
        receipt.sign(seed, base, base, logs, seed / 'key', logs / 'full-pass.json')
    except ValueError as error:
        assert 'provisional integration' in str(error), error
    else:
        raise AssertionError('integration logs signed')
    try:
        receipt.verify(seed, seed, logs / 'integration.json')
    except ValueError:
        pass
    else:
        raise AssertionError('provisional result accepted as FULL receipt')
    assert not (logs / 'full-pass.json').exists()
    print('CONTROL integration cannot sign or verify a FULL receipt: PASS')

    # Exercise real G0 module selection and recording with a fake build function.
    g0 = Path(scratch) / 'g0'
    shutil.copytree(seed, g0)
    write(g0, 'AvailableChainFGSAProofs/Tests/Positive.lean', 'module\n')
    write(g0, 'AvailableChainFGSAProofs/Tests/Negative.lean', 'module\n')
    write(g0, 'AvailableChainPCSA/Tests/Unported.lean', 'module\n')
    write(g0, 'scripts/gate-common.sh',
          'gate_with_slot() { "$@"; }\n'
          'gate_build() { printf "%s\\n" "$@" > g0-calls; return "${G0_RC:-0}"; }\n')
    commit(g0)
    for rc in (0, 7):
        result = subprocess.run(['python3', '-B', str(REPO / 'scripts/integration_g0.py')],
            cwd=g0, env=dict(os.environ, GATE_NO_BUILD='1', GATE_LOG_DIR=str(logs), G0_RC=str(rc)))
        assert result.returncode == rc, result
        record = json.loads((logs / 'package-g0.json').read_text())
        modules = {row['module'] for row in record['results']}
        assert modules == {'AvailableChainFGSA.Tests.Control',
                           'AvailableChainFGSAProofs.Tests.Positive',
                           'AvailableChainFGSAProofs.Tests.Negative'}, modules
        assert all(row['rc'] == rc for row in record['results'])
        assert (g0 / 'g0-calls').read_text().startswith('--wfail\n')
    print('CONTROL package G0: positive/negative module coverage and failed freshness: PASS')
print('gate-integration-selftest: PASS')
