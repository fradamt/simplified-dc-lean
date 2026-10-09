#!/usr/bin/env python3
"""Recount the FG-SA port source census from the unchanged API manifests."""
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent


def records(root=ROOT):
    text = (root / 'docs/FGSA-PORT-CENSUS.md').read_text()
    return json.loads(re.search(r'```json\n(.*?)\n```', text, re.S).group(1))


def manifest(path):
    entries = {}
    module = None
    for line in path.read_text().splitlines():
        heading = re.fullmatch(r'### `([^`]+)`', line)
        if heading:
            module = heading[1]
        match = re.fullmatch(r'([a-z]+) (\S+) ([0-9a-f]{16})', line)
        if match:
            if match[2] in entries:
                raise ValueError(f'duplicate manifest entry: {match[2]}')
            entries[match[2]] = dict(kind=match[1], digest=match[3], module=module)
    return entries


def check(root=ROOT):
    current = manifest(root / 'docs/FGSA-API.md')
    frozen = manifest(root / 'docs/FGSA-API-frozen.md')
    rows = records(root)
    seen = set()
    declarations = set()
    for row in rows:
        name = row['declaration']
        if name in declarations:
            raise ValueError(f'duplicate source declaration: {name}')
        declarations.add(name)
        if row['class'] not in ('A', 'B', 'C-i'):
            raise ValueError(f'invalid class: {name}')
        source = (root / row['path']).read_text().splitlines()
        short = name.rsplit('.', 1)[-1]
        if not re.search(r'\b(?:def|abbrev|structure|inductive|theorem)\s+' +
                         re.escape(short) + r'\b', source[row['line'] - 1]):
            raise ValueError(f'source declaration/line mismatch: {name}')
        expanded = [dict(name=n, kind=e['kind'], frozen=n in frozen)
                    for n, e in current.items()
                    if n == name or n == name + '_def' or n.startswith(name + '.')]
        if expanded != row['manifest_entries']:
            raise ValueError(f'manifest expansion mismatch: {name}')
        if current[name]['module'] != row['path'][:-5].replace('/', '.'):
            raise ValueError(f'module mismatch: {name}')
        for entry in expanded:
            if entry['name'] in seen:
                raise ValueError(f'overlapping entry: {entry["name"]}')
            seen.add(entry['name'])
    totals = (len(rows), len(seen), len(seen & frozen.keys()), len(seen - frozen.keys()))
    if totals != (369, 876, 799, 77):
        raise ValueError(f'census totals changed: {totals}')
    return totals


if __name__ == '__main__':
    try:
        totals = check()
        print('fgsa-port-census: PASS (sources %d; entries %d; frozen %d; later %d)' % totals)
    except (ValueError, KeyError, IndexError, OSError) as exc:
        print(f'fgsa-port-census: FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
