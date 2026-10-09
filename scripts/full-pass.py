#!/usr/bin/env python3
"""Sign and verify exact-head FULL receipts. Keys belong to trusted gate operators."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

NAMESPACE = 'lean-framework-full-v1'
IDENTITY = 'full-gate'
STEPS = ('build', 'check-build', 'check-fgsa', 'check-fgsa-run', 'catalog-lock',
         'v2-manifest', 'gen-manifest', 'fgsa-manifest', 'fgsa-claims',
         'Generic-axioms', 'FGSA-axioms', 'FGSARun-axioms', 'proof-audit-coverage',
         'check-fg-compose', 'FGCompose-axioms', 'FGSACompose-axioms',
         'FGSafety-axioms', 'FGSASafety-axioms', 'FGSAGrowth-axioms',
         'fg-finality-freeze',
         'fg-finality-coverage', 'fgsa-blueprint')


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


def clean_head(root, expected):
    head = git(root, 'rev-parse', '--verify', 'HEAD')
    if head != expected:
        raise ValueError('FULL RECEIPT WRONG HEAD')
    ignored = git(root, 'ls-files', '--others', '--ignored', '--exclude-standard',
                  '--', '*.lean', 'scripts/*', ':(exclude).lake/**')
    if ignored:
        raise ValueError('FULL RECEIPT IGNORED SOURCE')
    if git(root, 'status', '--porcelain', '--untracked-files=all'):
        raise ValueError('FULL RECEIPT DIRTY TARGET')
    return head


def verify(main, target, receipt):
    try:
        data = receipt.read_bytes()
        record = json.loads(data)
    except (OSError, ValueError):
        raise ValueError('FULL RECEIPT MISSING OR INVALID') from None
    required = {'version', 'head', 'policy', 'tier', 'result'}
    if not isinstance(record, dict) or set(record) != required or record['version'] != 1:
        raise ValueError('FULL RECEIPT INVALID FORMAT')
    if record['tier'] != 'full' or record['result'] != 'PASS':
        raise ValueError('FULL RECEIPT NOT FULL PASS')
    clean_head(target, record['head'])
    if record['policy'] != git(main, 'rev-parse', '--verify', 'HEAD'):
        raise ValueError('FULL RECEIPT WRONG POLICY HEAD')
    # Use the trust file from main's committed tree, never the target or local edits.
    trusted = subprocess.run(['git', '-C', str(main), 'show',
                              'HEAD:scripts/full-pass-signers'], capture_output=True)
    if trusted.returncode or not trusted.stdout.strip():
        raise ValueError('FULL RECEIPT NO TRUSTED SIGNER')
    import tempfile
    with tempfile.TemporaryDirectory(prefix='full-receipt-') as tmp:
        signers = Path(tmp) / 'signers'
        signers.write_bytes(trusted.stdout)
        result = subprocess.run(['ssh-keygen', '-Y', 'verify', '-f', str(signers),
                                 '-I', IDENTITY, '-n', NAMESPACE,
                                 '-s', str(receipt) + '.sig'], input=data, capture_output=True)
    if result.returncode:
        raise ValueError('FULL RECEIPT SIGNATURE REFUSED')
    # Repeat after verification to reject a concurrent checkout/edit.
    clean_head(target, record['head'])
    print(f'VERIFIED FULL PASS head={record["head"]} policy={record["policy"]}')


def sign(root, head, policy, logs, key, receipt):
    clean_head(root, head)
    required = {step + '.result' for step in STEPS}
    actual = {path.name for path in logs.glob('*.result')}
    if actual != required:
        missing, extra = sorted(required - actual), sorted(actual - required)
        raise ValueError(f'FULL RECEIPT FAILED OR MISSING STEP SET: {missing}; extra: {extra}')
    for step in STEPS:
        try:
            fields = (logs / f'{step}.result').read_text().split()
        except FileNotFoundError:
            raise ValueError(f'FULL RECEIPT FAILED OR MISSING STEP: {step}') from None
        if len(fields) != 2 or fields[0] != '0' or not fields[1].isdigit():
            raise ValueError(f'FULL RECEIPT FAILED OR MISSING STEP: {step}')
    policy = git(root, 'rev-parse', '--verify', policy + '^{commit}')
    record = dict(version=1, head=head, policy=policy, tier='full', result='PASS')
    receipt.write_text(json.dumps(record, sort_keys=True) + '\n')
    subprocess.run(['ssh-keygen', '-Y', 'sign', '-f', str(key), '-n', NAMESPACE,
                    str(receipt)], check=True)
    clean_head(root, head)
    print(f'FULL receipt: {receipt}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    check = commands.add_parser('verify')
    check.add_argument('main', type=Path)
    check.add_argument('target', type=Path)
    check.add_argument('receipt', type=Path)
    issue = commands.add_parser('sign')
    issue.add_argument('root', type=Path)
    issue.add_argument('head')
    issue.add_argument('policy')
    issue.add_argument('logs', type=Path)
    issue.add_argument('key', type=Path)
    issue.add_argument('receipt', type=Path)
    args = parser.parse_args()
    try:
        if args.command == 'verify':
            verify(args.main, args.target, args.receipt)
        else:
            sign(args.root, args.head, args.policy, args.logs, args.key, args.receipt)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(2, f'{error}\n')


if __name__ == '__main__':
    main()
