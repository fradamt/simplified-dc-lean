#!/usr/bin/env python3
"""Check exact FG-SA port edit paths at the pinned base; no Lean build needed."""
import argparse
from copy import deepcopy
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from importlib import import_module
census = import_module('recount-fgsa-port-census')
ROOT = Path(__file__).resolve().parent.parent
OWNERS = set('WP00a WP00t WP01a WP02 WP01b WP03a WP04a WP12a WP14p WP00b '
             'WP00c SWITCH WP05a WP05b WP06a WP05c WP03b WP06b WP03c WP06c '
             'WP09a WP04b WP07 WP08 WP09b WP11 WP10 WP12b WP13v WP15 WP16 '
             'WP13 WP14a WP14b'.split())


def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError(f'duplicate JSON key: {key}')
        obj[key] = value
    return obj


def check(data, root=ROOT):
    base = data['base_revision']
    if len(base) != 40 or any(c not in '0123456789abcdef' for c in base):
        raise ValueError('base must be a full commit SHA')
    files = set(subprocess.check_output(
        ['git', 'ls-tree', '-r', '--name-only', base], cwd=root, text=True).splitlines())
    owners = {}
    for entry in data['paths']:
        path = entry['path']
        pure = PurePosixPath(path)
        if pure.is_absolute() or '..' in pure.parts or str(pure) != path or any(
                char in path for char in '*?{}[]\\'):
            raise ValueError(f'path is not exact and relative: {path}')
        if path in owners:
            raise ValueError(f'duplicate owner: {path}: {owners[path]} and {entry["owner"]}')
        if entry['owner'] not in OWNERS or not entry['writer']:
            raise ValueError(f'invalid owner or missing writer: {path}')
        if not isinstance(entry['new'], bool):
            raise ValueError(f'new must be boolean: {path}')
        if path not in files and not entry['new']:
            raise ValueError(f'path absent from base and not marked new: {path}')
        if path in files and entry['new']:
            raise ValueError(f'base path incorrectly marked new: {path}')
        owners[path] = entry['owner']
    protected = set(data['protected_paths'])
    for path in owners:
        if path in protected or any(path.startswith(p) for p in data['protected_trees']):
            raise ValueError(f'protected edit path: {path}')
        if path in data['comparison_only_paths']:
            raise ValueError(f'comparison-only edit path: {path}')
    needed = {r['path'] for r in census.records(root)} | set(data['census_input_paths'])
    for path in sorted(needed):
        if path not in owners:
            raise ValueError(f'census path has no owner: {path}')
    # Complete base families, local prerequisites, finality and central tests.
    for path in sorted(files):
        if path.startswith(('AvailableChainFGSA/', 'AvailableChainFGSARun/',
                            'AvailableChainFGSAClaims/', 'AvailableChainFGSAProofs/',
                            'AvailableChainFGSAInhabit/')) and path.endswith('.lean'):
            if path not in protected and path not in owners:
                raise ValueError(f'base FG-SA module has no owner: {path}')
    tests = [p for p in files if p.startswith('AvailableChainFGSAProofs/Tests/')
             and p.endswith('.lean')]
    if len(tests) != 99 or any(owners.get(p) != 'WP13v' for p in tests):
        raise ValueError('the 99 base proof tests must have owner WP13v')
    healing = 'AvailableChainFGSAProofs/Proofs/Healing/'
    phase = {'PhaseFrame', 'PhaseOrder', 'Phase', 'PhaseRelay', 'PhaseSettle',
             'PhaseBoot', 'PromotionPhase'}
    for path in files:
        if path.startswith(healing) and path.endswith('.lean'):
            name = PurePosixPath(path).stem
            expected = 'WP09a' if name == 'Base' else 'WP04b' if name in phase else 'WP09b'
            if owners.get(path) != expected:
                raise ValueError(f'Healing split mismatch: {path}: expected {expected}')
    return len(owners), sum(e['new'] for e in data['paths']), len(tests)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--register', type=Path, default=ROOT / 'docs/FGSA-PORT-OWNERS.json')
    ap.add_argument('--selftest', action='store_true', help='also run a duplicate-owner negative control')
    args = ap.parse_args()
    data = json.loads(args.register.read_text(), object_pairs_hook=unique_object)
    size, new, tests = check(data)
    print(f'fgsa-port-owners: PASS ({size} exact paths; {new} new; {tests} proof tests)')
    if args.selftest:
        bad = deepcopy(data)
        duplicate = deepcopy(bad['paths'][0])
        duplicate['owner'] = 'WP00a' if duplicate['owner'] != 'WP00a' else 'WP16'
        bad['paths'].append(duplicate)
        try:
            check(bad)
        except ValueError as exc:
            if not str(exc).startswith('duplicate owner:'):
                raise
            print(f'negative control: expected FAIL: {exc}')
        else:
            raise ValueError('duplicate-owner negative control unexpectedly passed')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as exc:
        print(f'fgsa-port-owners: FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
