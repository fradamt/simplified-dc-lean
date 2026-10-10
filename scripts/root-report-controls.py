#!/usr/bin/env python3
"""Source-only controls for phase-aware root validation and graph reports."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile


def load(name):
    spec = importlib.util.spec_from_file_location(name, 'scripts/' + name + '.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


deep = load('fgsa-deep')


def graph(edges):
    data = dict(format_version=2, entries={}, nodes={}, node_order=sorted(edges), pins=deep.pins())
    for name, deps in edges.items():
        data['nodes'][name] = dict(digest='1' * 64, kernel_name=name, module='Control', kind='def',
                                   type=['Nat'], body=['1'], dependencies=deps)
    for name in edges:
        data['entries'][name] = dict(digest=deep.root_digest(data, name),
                                     module='Control', kind='def')
    deep.validate_graph(data)
    return data


def scoped_report_controls(tmp):
    scoped = graph({'A': ['B'], 'B': [], 'C': []})
    scoped['checkpoint'] = dict(name='g-s1', modules=['Control'])
    baseline, snapshot, manifest, roots, output = [tmp / n for n in
        ('scoped-base.json', 'scoped-now.json', 'scoped.md', 'scoped-roots.json', 'scoped-out.json')]
    for path in (baseline, snapshot):
        path.write_text(deep.render(scoped))
    manifest.write_text('### `Control`\n' + ''.join(
        'def ' + n + ' ' + '1' * 16 + '\n' for n in scoped['entries']))
    command = ['python3', '-B', 'scripts/fgsa-deep.py', '--baseline', str(baseline),
               '--snapshot', str(snapshot), '--manifest', str(manifest),
               '--roots', str(roots), '--output', str(output), '--checkpoint', 'g-s1']
    failures = []
    for mode in ('--attribute', '--check'):
        for label, subject, reason in [
            ('absent G-S1 reference name',
             dict(name='Missing.Required', status='existing', module='Deferred'),
             'required root absent from reference graph'),
            ('omitted G-S1 module', dict(name='A', status='existing'),
             'G-S1 subjects require exact module identities')]:
            roots.write_text(json.dumps([subject]))
            result = subprocess.run(command + [mode], capture_output=True, text=True)
            rows = deep.strict_json(output)['unresolved']
            passed = (result.returncode == 1 and reason in result.stderr and
                      len(rows) == 1 and rows[0]['state'] == 'error')
            print('CONTROL ' + mode + ' ' + label + ': ' + ('PASS' if passed else 'FAIL'))
            if not passed:
                failures.append((mode, label, result.returncode, rows))
    assert not failures, failures


def main():
    base = graph({'A': ['B'], 'B': [], 'C': []})
    with tempfile.TemporaryDirectory(prefix='root-report-controls-') as scratch:
        tmp = Path(scratch)
        scoped_report_controls(tmp)
        baseline, snapshot, manifest, roots, report = [tmp / n for n in
            ('base.json', 'now.json', 'manifest.md', 'roots.json', 'report.json')]
        for path in (baseline, snapshot):
            path.write_text(deep.render(base))
        manifest.write_text('### `Control`\n' + ''.join(
            'def ' + n + ' ' + '1' * 16 + '\n' for n in base['entries']))
        command = ['python3', '-B', 'scripts/fgsa-deep.py', '--baseline', str(baseline),
                   '--snapshot', str(snapshot), '--manifest', str(manifest),
                   '--roots', str(roots), '--output', str(report)]
        for mode in ('--attribute', '--check'):
            for label, subject, phase, reason in [
                ('missing existing', dict(name='Missing.Required', status='existing'),
                 'baseline', 'required root absent'),
                ('wrong module', dict(name='A', status='existing', module='Wrong'),
                 'baseline', 'root module mismatch'),
                ('unknown name', dict(name='Missing.Unknown'), 'baseline', 'required root absent'),
                ('planned at G-S2', dict(name='Missing.Planned', status='planned'),
                 'g-s2', 'required root absent'),
                ('planned at G-S3', dict(name='Missing.Planned', status='planned'),
                 'g-s3', 'required root absent')]:
                roots.write_text(json.dumps([subject]))
                result = subprocess.run(command + [mode, '--checkpoint', phase],
                                        capture_output=True, text=True)
                assert result.returncode == 1 and reason in result.stderr, result
                assert deep.strict_json(report)['unresolved'][0]['state'] == 'error'
                print('CONTROL ' + mode + ' ' + label + ': PASS')
            roots.write_text(json.dumps([dict(name='Missing.Planned', status='planned')]))
            result = subprocess.run(command + [mode], capture_output=True, text=True)
            assert result.returncode == 0, result
            assert deep.strict_json(report)['unresolved'][0]['state'] == 'pending'
        scoped = graph({'A': ['B'], 'B': [], 'C': []})
        scoped['checkpoint'] = dict(name='g-s1', modules=['Control'])
        reference = graph({'A': ['B'], 'B': [], 'C': [], 'Deferred.Required': []})
        for section in ('nodes', 'entries'):
            reference[section]['Deferred.Required']['module'] = 'Deferred'
        subjects = [dict(name='Deferred.Required', status='existing', module='Deferred')]
        report = deep.diff_report(reference, scoped, subjects, checkpoint='g-s1')
        deep.require_roots(report)
        assert report['unresolved'][0]['state'] == 'pending'
        report = deep.diff_report(reference, scoped, subjects, checkpoint='g-s2')
        try:
            deep.require_roots(report)
        except ValueError as exc:
            assert 'final checkpoint import scope' in str(exc)
        else:
            raise AssertionError('accepted a deferred G-S1 subject at final measurement')
        # Presence in the reference alone is insufficient current evidence.
        removed = graph({'B': [], 'C': []})
        report = deep.diff_report(base, removed, [dict(name='A', status='existing')])
        try:
            deep.require_roots(report)
        except ValueError as exc:
            assert 'required root absent' in str(exc)
        else:
            raise AssertionError('accepted a required root present only in the reference')
        print('CONTROL planned before final, deferred at G-S1, target absence: PASS')
        baseline.write_text(deep.render(removed))
        roots.write_text(json.dumps([dict(name='A', status='existing', module='Control')]))
        for mode in ('--attribute', '--check'):
            result = subprocess.run(command + [mode], capture_output=True, text=True)
            assert result.returncode == 1 and 'absent from reference graph' in result.stderr
        print('CONTROL existing root absent from reference: PASS')
    now = graph({'A': ['C'], 'B': [], 'C': []})
    report = deep.diff_report(base, now, [dict(name='A')])
    assert [n['name'] for n in report['nodes']] == ['A']
    row, = report['entries']
    assert row['closure_added'] == ['C'] and row['closure_removed'] == ['B']
    assert row['closure_paths'] == [dict(name='B', side='base', path=['A', 'B']),
                                    dict(name='C', side='target', path=['A', 'C'])]
    assert base['nodes']['B'] == now['nodes']['B'] and base['nodes']['C'] == now['nodes']['C']
    assert base['nodes']['A']['body'] == now['nodes']['A']['body']
    assert [n['name'] for n in row['changed_nodes']] == ['A']
    print('CONTROL unchanged B/C closure removal/addition with side paths: PASS')
    diff = load('api-diff')
    combined = diff.combine([base, base])
    assert combined['entries'] == base['entries'] and combined['nodes'] == base['nodes']
    try:
        diff.combine([base, now])
    except ValueError as exc:
        assert 'CONFLICTING SNAPSHOT NODE/ROOT: A' in str(exc), exc
    else:
        raise AssertionError('accepted conflicting multi-snapshot inputs')
    print('CONTROL conflicting multi-snapshot input: PASS')


if __name__ == '__main__':
    main()
