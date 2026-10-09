#!/usr/bin/env python3
"""Storage and exact exception checks for V2Manifest's FG-SA deep kernel digests.

Use V2Manifest --scope fgsa --deep --write/--check for compiled checks.
This helper also maintains the separate shallow frame baseline. All writes are
explicit; --check never refreshes a baseline or an exception.
"""
import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

DEEP = Path('scripts/fgsa-deep-frozen.json')
FRAME = Path('scripts/fgsa-frame-frozen.json')
FRAME_SHA = Path('scripts/fgsa-frame-frozen.sha256')
FRAME_ALLOW = Path('scripts/fgsa-frame-allow.json')
MANIFEST = Path('docs/FGSA-API.md')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def strict_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError(f'DUPLICATE JSON KEY {path}: {key}')
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=pairs)


def manifest(path):
    result, module = {}, None
    for line in path.read_text().splitlines():
        heading = re.fullmatch(r'### `([^`]+)`', line)
        if heading:
            module = heading[1]
        entry = re.fullmatch(r'([a-z]+) (\S+) ([0-9a-f]{16})', line)
        if entry:
            if entry[2] in result or module is None:
                raise ValueError(f'INVALID MANIFEST ENTRY {entry[2]}')
            result[entry[2]] = dict(kind=entry[1], module=module, digest=entry[3])
    if not result:
        raise ValueError(f'EMPTY MANIFEST {path}')
    return result


def frame_entries(current):
    # Include every additive FrameNext/ComposeNext entry (including constructors,
    # projections and _def equations), plus the full canonical frame families.
    families = ('RFrameExact', 'RFrame', 'FGFoundation', 'FGFoundationClaim',
                'FrameAt', 'FrameClaim')
    prefix = 'AvailableChain.FGSA.Run.'
    return {name: row for name, row in current.items()
            if row['module'].split('.')[-1] in ('FrameNext', 'ComposeNext') or any(
                name == prefix + family or name == prefix + family + '_def' or
                name.startswith(prefix + family + '.') for family in families)}


def pins():
    return dict(toolchain=Path('lean-toolchain').read_text().strip(),
                package_pins_sha256=sha(Path('lake-manifest.json').read_bytes()))


def provenance(current):
    return dict(basis_commit=subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], text=True).strip(), **pins(),
        shallow_manifest_sha256=sha(current.read_bytes()),
        original_frozen_sha256=sha(Path('docs/FGSA-API-frozen.md').read_bytes()),
        original_frozen_entries=sorted(manifest(Path('docs/FGSA-API-frozen.md'))),
        plan_revision='fgsa-port-r2 + binding addendum; S0-F/00c')


def write_baseline(path, sha_path, data):
    # One node/root per line keeps a full dependency list reviewable and compact.
    fields = []
    for key, value in data.items():
        if key == 'nodes':
            body = '[\n' + ',\n'.join('    ' + json.dumps(row, ensure_ascii=False,
                separators=(',', ':')) for row in value) + '\n  ]'
        elif key == 'entries':
            body = '{\n' + ',\n'.join('    ' + json.dumps(name, ensure_ascii=False) + ': ' +
                json.dumps(row, ensure_ascii=False, separators=(',', ':'))
                for name, row in value.items()) + '\n  }'
        else:
            body = json.dumps(value, ensure_ascii=False, indent=2)
        fields.append('  ' + json.dumps(key) + ': ' + body)
    path.write_text('{\n' + ',\n'.join(fields) + '\n}\n')
    sha_path.write_text(sha(path.read_bytes()) + '\n')


def read_baseline(path, sha_path):
    expected = sha_path.read_text().strip()
    if not re.fullmatch('[0-9a-f]{64}', expected) or sha(path.read_bytes()) != expected:
        raise ValueError(f'BASELINE SHA256 MISMATCH {path}')
    data = strict_json(path)
    if data['format_version'] != 1:
        raise ValueError(f'UNSUPPORTED BASELINE FORMAT {path}')
    if not re.fullmatch('[0-9a-f]{40}', data['provenance']['basis_commit']):
        raise ValueError(f'INVALID BASIS COMMIT {path}')
    for key, value in pins().items():
        if data['provenance'][key] != value:
            raise ValueError(f'BASELINE PIN MISMATCH {path}: {key}')
    frozen = Path('docs/FGSA-API-frozen.md')
    if (data['provenance']['original_frozen_sha256'] != sha(frozen.read_bytes()) or
            data['provenance']['original_frozen_entries'] != sorted(manifest(frozen))):
        raise ValueError(f'ORIGINAL FROZEN MEMBERSHIP MISMATCH {path}')
    return data


def exceptions(path, width):
    data = strict_json(path)
    if set(data) != {'format_version', 'exceptions'} or data['format_version'] != 1:
        raise ValueError(f'INVALID EXCEPTION FORMAT {path}')
    result = data['exceptions']
    if not isinstance(result, dict):
        raise ValueError(f'INVALID EXCEPTION MAP {path}')
    keys = {'old_digest', 'new_digest', 'cause', 'census_class', 'plan_revision'}
    for name, row in result.items():
        if (not isinstance(row, dict) or set(row) != keys or any(
                not isinstance(v, str) or not v.strip() for v in row.values())):
            raise ValueError(f'UNEXPLAINED EXCEPTION {name}: require {sorted(keys)}')
        if row['census_class'] not in ('A', 'B'):
            raise ValueError(f'INVALID CENSUS CLASS {name}: use A or B; C-i is contextual')
        for key in ('old_digest', 'new_digest'):
            if not re.fullmatch(f'[0-9a-f]{{{width}}}|absent', row[key]):
                raise ValueError(f'INVALID EXCEPTION DIGEST {name}: {key}')
    return result


def compare(old, now, allowed, label):
    failures = []
    for name in sorted(set(old) | set(now) | set(allowed)):
        before, after = old.get(name, {}).get('digest', 'absent'), now.get(name, {}).get('digest', 'absent')
        row = allowed.get(name)
        if before == after:
            if row is not None:
                failures.append(f'STALE EXCEPTION {name}: digest is unchanged ({before})')
        elif row is None:
            failures.append(f'{label} UNEXPLAINED {name}: {before} -> {after}')
        elif row['old_digest'] != before or row['new_digest'] != after:
            failures.append(f'EXCEPTION DIGEST MISMATCH {name}: '
                            f'recorded {row["old_digest"]} -> {row["new_digest"]}; '
                            f'actual {before} -> {after}')
    return failures


def validate_graph(data):
    if data['format_version'] != 1 or not data['entries'] or not data['nodes']:
        raise ValueError('INVALID DEEP SNAPSHOT')
    nodes = data['nodes']
    names = {row['name']: i for i, row in enumerate(nodes)}
    if len(names) != len(nodes):
        raise ValueError('DUPLICATE DEEP NODE')
    for row in nodes:
        if not re.fullmatch('[0-9a-f]{64}', row['digest']):
            raise ValueError(f'INVALID NODE DIGEST {row["name"]}')
        if (row['dependencies'] != sorted(set(row['dependencies'])) or any(
                type(i) is not int or not 0 <= i < len(nodes) for i in row['dependencies'])):
            raise ValueError(f'INVALID NODE DEPENDENCIES {row["name"]}')
    for name, row in data['entries'].items():
        if not re.fullmatch('[0-9a-f]{64}', row['digest']) or name not in names:
            raise ValueError(f'INVALID ROOT {name}')
        seen, stack = set(), [names[name]]
        while stack:
            i = stack.pop()
            if i not in seen:
                seen.add(i)
                stack.extend(nodes[i]['dependencies'])
        if sorted(seen) != row['dependencies']:
            raise ValueError(f'INCOMPLETE ROOT DEPENDENCIES {name}')


def changed_path(name, old, now):
    old_nodes = {n['name']: n for n in old['nodes']}
    new_nodes = {n['name']: n for n in now['nodes']}
    changed = {n for n in set(old_nodes) | set(new_nodes)
               if old_nodes.get(n, {}).get('digest') != new_nodes.get(n, {}).get('digest')}
    for label, data in (('current', now), ('baseline', old)):
        nodes = data['nodes']
        ids = {n['name']: i for i, n in enumerate(nodes)}
        if name not in ids:
            continue
        queue = deque([ids[name]])
        parents = {ids[name]: None}
        while queue:
            i = queue.popleft()
            node = nodes[i]
            if node['name'] in changed:
                path = []
                cur = i
                while cur is not None:
                    path.append(nodes[cur]['name'])
                    cur = parents[cur]
                before = old_nodes.get(node['name'], {}).get('digest', 'absent')
                after = new_nodes.get(node['name'], {}).get('digest', 'absent')
                return f'{label} path: {" -> ".join(reversed(path))}; node {before} -> {after}'
            for dep in node['dependencies']:
                if dep not in parents:
                    parents[dep] = i
                    queue.append(dep)
    return 'root added/removed or dependency graph changed'


def check_deep(old, now, allowed):
    validate_graph(old)
    validate_graph(now)
    failures = compare(old['entries'], now['entries'], allowed, 'DEEP')
    for name in sorted(set(old['entries']) | set(now['entries'])):
        before = old['entries'].get(name, {}).get('digest', 'absent')
        after = now['entries'].get(name, {}).get('digest', 'absent')
        if before != after:
            print(f'DEEP CHANGE {name}: {before} -> {after}; {changed_path(name, old, now)}')
    return failures


def check_frame(old, current, allowed):
    # Look up frozen names in the complete current manifest even if an entry
    # moved out of a selected module. Such a move is not an entry removal.
    now = frame_entries(current)
    now.update({name: current[name] for name in old if name in current})
    failures = compare(old, now, allowed, 'FRAME')
    for name in set(old) & set(now):
        if any(old[name][k] != now[name][k] for k in ('kind', 'module')):
            failures.append(f'FRAME KIND/MODULE CHANGED {name}')
    return failures


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    modes = ap.add_mutually_exclusive_group(required=True)
    for mode in ('write', 'check', 'frame-write', 'frame-check'):
        modes.add_argument('--' + mode, action='store_true')
    ap.add_argument('--snapshot', type=Path)
    ap.add_argument('--manifest', type=Path, default=MANIFEST)
    ap.add_argument('--baseline', type=Path)
    ap.add_argument('--sha', type=Path)
    ap.add_argument('--allow', type=Path)
    args = ap.parse_args()
    frame = args.frame_write or args.frame_check
    path = args.baseline or (FRAME if frame else DEEP)
    sha_path = args.sha or path.with_suffix('.sha256')
    allow_path = args.allow or (FRAME_ALLOW if frame else Path('scripts/fgsa-deep-allow.json'))
    current = manifest(args.manifest)
    if frame:
        now = dict(format_version=1, entries=frame_entries(current))
    else:
        if args.snapshot is None:
            ap.error('deep modes require --snapshot; use V2Manifest --deep')
        now = strict_json(args.snapshot)
        validate_graph(now)
        if set(now['entries']) != set(current):
            raise ValueError('DEEP ROOTS DIFFER FROM COMPLETE CURRENT MANIFEST')
    if args.write or args.frame_write:
        now['provenance'] = provenance(args.manifest)
        write_baseline(path, sha_path, now)
        print(f'{path}: written; {len(now["entries"])} entries')
        return
    old = read_baseline(path, sha_path)
    allowed = exceptions(allow_path, 16 if frame else 64)
    failures = (check_frame(old['entries'], current, allowed) if frame else
                check_deep(old, now, allowed))
    if failures:
        raise ValueError('\n'.join(failures))
    print(f'{"FRAME" if frame else "DEEP"} PASS: {len(now["entries"])} entries; '
          f'{len(allowed)} exact exceptions')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as exc:
        print(f'FGSA BASELINE FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
