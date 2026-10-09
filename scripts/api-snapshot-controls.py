#!/usr/bin/env python3
"""Compiled negative controls for current API and catalog snapshots."""
import importlib.util
from pathlib import Path
import subprocess
import shutil
import tempfile


def run(tool, *args, want=0, reasons=()):
    result = subprocess.run(['lake', 'env', 'lean', '--run', 'scripts/' + tool + '.lean',
                             *map(str, args)], capture_output=True, text=True)
    output = result.stdout + result.stderr
    assert result.returncode == want, (tool, args, result)
    assert all(reason in output for reason in reasons), (reasons, output)
    print('CONTROL', tool, ' '.join(reasons) or 'write/check parity', 'PASS', flush=True)


def main():
    with tempfile.TemporaryDirectory(prefix='api-snapshot-controls-') as scratch:
        root = Path(scratch)
        for scope in ('v2', 'gen', 'fgsa'):
            path = root / (scope + '.md')
            original = {'v2': 'V2', 'gen': 'GEN', 'fgsa': 'FGSA'}[scope]
            shutil.copyfile('docs/' + original + '-API.md', path)
            lines = path.read_text().splitlines(keepends=True)
            entries = [(i, line.split()) for i, line in enumerate(lines)
                       if len(line.split()) == 3 and line.split()[0] in
                       ('def', 'theorem', 'inductive', 'structure', 'constructor',
                        'field', 'opaque', 'axiom', 'abbrev')]
            assert len(entries) >= 5
            reasons = []
            for pos, (i, words) in enumerate(entries[:5]):
                if pos == 0:
                    lines[i] = ''
                    reasons.append('NOT LISTED ' + words[1])
                elif pos == 1:
                    words[2] = '0' * 16 if words[2] != '0' * 16 else '1' * 16
                    lines[i] = ' '.join(words) + '\n'
                    reasons.append('CHANGED ' + words[1])
                elif pos == 2:
                    words[0] = 'wrongkind'
                    lines[i] = ' '.join(words) + '\n'
                    reasons.append('WRONG KIND ' + words[1])
                elif pos == 3:
                    lines[i] += lines[i]
                    reasons.append('DUPLICATE ENTRY ' + words[1])
                else:
                    lines[i] += f'def Missing.Control.{scope} 0000000000000000\n'
                    reasons += ['UNKNOWN Missing.Control.' + scope,
                                'EXTRA ENTRY Missing.Control.' + scope]
            # A heading move must fail independently of digest equality.
            import re
            heading = max(i for i, line in enumerate(lines)
                          if i < entries[-1][0] and line.startswith('### `'))
            lines[heading] = '### `Moved.Control.Module`\n'
            reasons.append('WRONG MODULE ')
            path.write_text(''.join(lines))
            run('V2Manifest', '--scope', scope, '--check', '--manifest', path,
                want=1, reasons=reasons)
            path.unlink()
            run('V2Manifest', '--scope', scope, '--check', '--manifest', path,
                want=2, reasons=['cannot read'])
        lock = root / 'catalog.lock'
        shutil.copyfile('docs/catalog.lock', lock)
        lines = lock.read_text().splitlines()
        first = lines.pop(0).rsplit(' ', 1)[0]
        changed, digest = lines[0].rsplit(' ', 1)
        lines[0] = changed + ' ' + ('0' * 16 if digest != '0' * 16 else '1' * 16)
        lines.append('Control.NoLongerCompiled 0000000000000000')
        lock.write_text('\n'.join(lines) + '\n')
        run('CatalogLock', '--check', '--lock', lock, want=1,
            reasons=['ADDED ' + first, 'CHANGED ' + changed, 'REMOVED Control.NoLongerCompiled'])
        run('CatalogLock', '--write', '--lock', lock)
        run('CatalogLock', '--check', '--lock', lock)
        # An addition alone must fail; this was previously accepted.
        lines = lock.read_text().splitlines()
        lock.write_text('\n'.join(lines[1:]) + '\n')
        run('CatalogLock', '--check', '--lock', lock, want=1, reasons=['ADDED '])
        spec = importlib.util.spec_from_file_location('snapshot', 'scripts/api-snapshot.py')
        snapshot = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(snapshot)
        try:
            snapshot.source_modules(('NoSuchLibrary.Control',))
        except ValueError as exc:
            assert 'MISSING SOURCE SCOPE' in str(exc)
        else:
            raise AssertionError('accepted a missing source library')
        print('CONTROL source scope completeness: PASS')
        missing_map = root / 'missing-map.json'
        missing_map.write_text('{"theorem":"Missing.Control.MappedRoot"}')
        try:
            snapshot.extract('fgsa-claims', blueprint=missing_map)
        except ValueError as exc:
            assert 'MISSING MAPPED ROOT Missing.Control.MappedRoot' in str(exc), exc
        else:
            raise AssertionError('accepted a missing blueprint root')
        print('CONTROL missing mapped root: PASS')


if __name__ == '__main__':
    main()
