#!/usr/bin/env python3
"""Run CheckProofEqns with the fixed owning-module and #print axioms inventory."""
import ast
import argparse
from pathlib import Path
import re
import subprocess
import tempfile

AUDITS = tuple('AvailableChain' + lib + '.Tests.Axioms' for lib in
               ('Generic', 'FGSA', 'FGSARun', 'FGSAClaims', 'FGSAProofs', 'FGSAInhabit',
                'PCSAProofs', 'FGCompose')) + ('AvailableChainFGSAProofs.Tests.FGCompose',
                                            'AvailableChainPCSAProofs.Tests.FGCompose')


def read_coverage(path):
    tree = ast.parse(path.read_text(), mode='eval')
    # Reject repeated keys before literal_eval can discard them.
    for node in ast.walk(tree):
        if isinstance(node, ast.Dict):
            keys = [ast.literal_eval(key) for key in node.keys]
            if len(keys) != len(set(keys)):
                raise ValueError('duplicate proof coverage key')
    data = ast.literal_eval(tree)
    if not isinstance(data, dict) or not data:
        raise ValueError('empty or invalid proof coverage inventory')
    rows = []
    for audit, owners in data.items():
        if not isinstance(owners, dict) or not owners:
            raise ValueError('empty or invalid proof coverage owner map')
        for owner, names in owners.items():
            if not isinstance(names, tuple) or not names:
                raise ValueError('empty or invalid proof coverage names')
            for name in names:
                if not all(isinstance(n, str) and re.fullmatch(r"[^\W\d][\w'.?!]*", n)
                           for n in (audit, owner, name)):
                    raise ValueError('invalid proof coverage identifier')
                rows.append((owner, name, audit))
    if len(rows) != len({(name, audit) for _, name, audit in rows}):
        raise ValueError('duplicate proof coverage row')
    return sorted(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='regenerate; review the diff')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    inventory = root / 'scripts/proof-audit-coverage.txt'
    rows = [] if args.write else read_coverage(inventory)
    if not args.write and {audit for _, _, audit in rows} != set(AUDITS):
        raise ValueError('proof coverage audit set differs from the FULL tier')
    with tempfile.TemporaryDirectory(prefix='proof-coverage-', dir=root / '.lake') as tmp:
        coverage = Path(tmp) / 'coverage.txt'
        audits = sorted(AUDITS)
        print(f'proof audit coverage: {len(rows)} declarations; {len(audits)} audits', flush=True)
        # Import one audit's private syntax per process. Do not accumulate the
        # private environments of all six libraries under the 7 GiB wrapper cap.
        for audit in audits:
            selected = [row for row in rows if row[2] == audit]
            coverage.write_text(''.join(' '.join(row) + '\n' for row in selected))
            print(f'proof audit: {audit} ({len(selected)} declarations)', flush=True)
            mode = ['--write-coverage', str(coverage)] if args.write else [
                '--coverage', str(coverage), '--complete-coverage']
            rc = subprocess.call(['lake', 'env', 'lean', '--run', 'scripts/CheckProofEqns.lean',
                                  '--baseline', 'scripts/baselines/check-proof-eqns.txt',
                                  *mode, audit], cwd=root)
            if rc:
                return rc
            if args.write:
                rows.extend(tuple(line.split()) for line in coverage.read_text().splitlines())
        if args.write:
            # Adjacent string literals keep long identifiers below 100 columns.
            lines = ['# Complete C14 audit inventory. Generate with '
                     'check-proof-coverage.py --write.',
                     '# Review changes. Normal checks never regenerate this file.', '{']
            for audit in audits:
                lines.append(f'    {audit!r}: {{')
                owners = sorted({owner for owner, _, a in rows if a == audit})
                for owner in owners:
                    lines.append(f'        {owner!r}: (')
                    for name in sorted({n for o, n, a in rows if o == owner and a == audit}):
                        if len(repr(name)) <= 86:
                            lines.append(f'            {name!r},')
                        else:
                            cut = name.rfind('.', 0, 80) + 1
                            lines += [f'            ({name[:cut]!r}',
                                      f'             {name[cut:]!r}),']
                    lines.append('        ),')
                lines.append('    },')
            inventory.write_text('\n'.join([*lines, '}']) + '\n')
        return 0


if __name__ == '__main__':
    raise SystemExit(main())
