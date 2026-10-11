"""Conservative eligibility for a provisional gate; never main evidence."""
import argparse
import ast
import hashlib
from difflib import SequenceMatcher
import json
from importlib import import_module
from pathlib import Path
import re
import subprocess
import sys

from checker_scope import matched_paths, resolve

INVENTORIES = {f'scripts/{name}-expected.txt' for name in
               ('fg', 'fgsa', 'fgsa-run', 'fgsa-claims', 'fg-compose')}
SNAPSHOTS = {f'docs/api/{name}.json' for name in
             ('legacy-api', 'compose-api', 'fgsa-deep', 'fgsa-claims-api',
              'gen-deep', 'v2-deep')}
# Only coverage lists can grow. Permission/exemption lists are not in this set.
CONSTANTS = {'scripts/check-fgsa-claims.sh': {'ORDER', 'REQUIRED_MODEL_SCOPE'},
             'scripts/check-fgsa-blueprint.py': {'CLAIMS_STRUCTURES', 'SAFETY_FIELDS'}}
P0 = ('AvailableChainGeneric', 'AvailableChainFGSA', 'AvailableChainFGSARun',
      'AvailableChainFGSAClaims', 'AvailableChainFGSAProofs',
      'AvailableChainFGSAInhabit', 'AvailableChainFGCompose')


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])


def ordered_additions(before, after):
    if len(after) != len(set(after)) or len(before) >= len(after):
        raise ValueError('needs distinct additions')
    remaining = iter(after)
    if not all(any(old == new for new in remaining) for old in before):
        raise ValueError('old entry removed, changed, or reordered')


def added_lines(before, after):
    old, new = before.splitlines(), after.splitlines()
    additions = []
    for tag, i, j, k, l in SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
        if tag not in ('equal', 'insert'):
            raise ValueError('old line removed or changed')
        if tag == 'insert':
            additions.extend(new[k:l])
    if not additions:
        raise ValueError('no added lines')
    return additions


def exact_names(values):
    # ? and ! are literal Lean identifier characters in inventories, not glob
    # permissions. These lists are parsed and compared as exact strings.
    if not all(isinstance(x, str) and re.fullmatch(r"[^\W\d][\w'.!?]*", x)
               for x in values):
        raise ValueError('entries must be exact names without wildcards')


def constant_additions(before, after, names, shell=False):
    if shell:
        marker = "<<'PY'\n"
        a, before = before.split(marker, 1)
        b, after = after.split(marker, 1)
        before, c = before.rsplit('\nPY', 1)
        after, d = after.rsplit('\nPY', 1)
        if (a, c) != (b, d):
            raise ValueError('shell logic changed')
    old, new = ast.parse(before), ast.parse(after)
    changed = []
    for name in sorted(names):
        def assignment(tree):
            nodes = [n for n in tree.body if isinstance(n, ast.Assign) and
                     len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) and
                     n.targets[0].id == name]
            if len(nodes) != 1:
                raise ValueError('missing or ambiguous constant: ' + name)
            return nodes[0]
        x, y = assignment(old), assignment(new)
        if ast.dump(x) == ast.dump(y):
            continue
        if type(x.value) != type(y.value) or not isinstance(x.value, (ast.Tuple, ast.List, ast.Set)):
            raise ValueError('constant is not a literal list: ' + name)
        first, last = [ast.literal_eval(n) for n in (x.value, y.value)]
        if isinstance(first, set):
            if not first < last or len(y.value.elts) != len(last):
                raise ValueError('set is not a distinct strict superset: ' + name)
            for pair in last:
                if not isinstance(pair, tuple) or len(pair) != 2:
                    raise ValueError('scope entry is not an owner/name pair')
                exact_names(pair)
        else:
            exact_names(last)
            ordered_additions(first, last)
        x.value = y.value = ast.Constant(value=None)
        changed.append(name)
    if not changed or ast.dump(old) != ast.dump(new):
        raise ValueError('checker logic or an unapproved constant changed')
    return changed


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate JSON key: ' + key)
        result[key] = value
    return result


def snapshot_additions(before, after):
    old, new = [json.loads(x, object_pairs_hook=unique_object) for x in (before, after)]
    if not isinstance(old, dict) or not isinstance(new, dict) or set(old) != set(new):
        raise ValueError('snapshot schema changed')
    count = 0
    for field in old:
        a, b = old[field], new[field]
        if field in ('entries', 'nodes'):
            if not isinstance(a, dict) or not isinstance(b, dict) or any(
                    key not in b or b[key] != value for key, value in a.items()):
                raise ValueError('old snapshot entry removed or changed: ' + field)
            count += len(b) - len(a)
        elif field == 'node_order' and a != b:
            ordered_additions(a, b)
        elif a != b:
            raise ValueError('snapshot metadata changed: ' + field)
    if count <= 0:
        raise ValueError('no snapshot entries added')
    return count


def policy_file(path):
    return (path.startswith('scripts/baselines/') or
            bool(re.search(r'(?:allow|exclu|wildcard)', path, re.I)))


def deferred_controls(root):
    # These are the precise NEG-controlled drivers/blocks. Package Tests are
    # built and checked separately; none of their results are deferred.
    selectors = ['gate.sh: checker-self-tests (check-build.sh --selftests-only)',
            'check-fgsa-claims.sh: NEG-selected source and compiled fixture controls',
            'check-fg-compose.sh: check-fg-compose-controls.py',
            'check-fgsa-manifest.sh: api-snapshot-controls.py',
            'check-fgsa-manifest.sh: fgsa-deep-controls.py',
            'check-fgsa-run.sh: NEG-selected source and compiled fixture controls',
            'check-fgsa.sh: NEG-selected fixture controls and CheckFGSAOldReads --controls']
    records = []
    for selector in selectors:
        driver = selector.split(':', 1)[0]
        text = (root / 'scripts' / driver).read_text()
        # The source hash and line numbers identify the exact deferred dispatch.
        lines = [i for i, line in enumerate(text.splitlines(), 1)
                 if 'NEG' in line and not line.lstrip().startswith('#')]
        records.append(dict(selector=selector, driver=driver,
                            neg_dispatch_lines=lines,
                            driver_sha256=hashlib.sha256(text.encode()).hexdigest()))
    return records


def select(root, base, head='HEAD', reviewed=()):
    base, head = resolve(root, base), resolve(root, head)
    subprocess.run(['git', '-C', str(root), 'merge-base', '--is-ancestor', base, head], check=True)
    if base == head:
        raise ValueError('empty candidate range')
    branch = git(root, 'symbolic-ref', '--quiet', '--short', 'HEAD').decode().strip() \
        if subprocess.run(['git', '-C', str(root), 'symbolic-ref', '--quiet', 'HEAD'],
                          stdout=subprocess.DEVNULL).returncode == 0 else ''
    if branch in ('main', 'master'):
        raise ValueError('integration mode cannot run on main')
    if git(root, 'status', '--porcelain', '--untracked-files=all').strip():
        raise ValueError('candidate must be clean and committed')
    ignored = git(root, 'ls-files', '--others', '--ignored', '--exclude-standard', '--',
                  '*.lean', 'scripts/*', ':(exclude).lake/**').strip()
    if ignored:
        raise ValueError('ignored source or checker file')
    paths = [p for p in git(root, 'diff', '--no-ext-diff', '--no-renames', '--name-only',
                           '-z', base + '..' + head).decode().split('\0') if p]
    matched = matched_paths(root, base, head)
    reviewed = sorted(set(reviewed))
    if any(p not in paths or not p.startswith('scripts/') or not p.endswith('.txt') or not policy_file(p) or
           any(c in p for c in '*?[]') for p in reviewed):
        raise ValueError('--reviewed-allow must name changed, exact policy-data files')
    evidence = []
    for path in paths:
        try:
            old_tree, new_tree = [git(root, 'ls-tree', rev, '--', path).decode().strip()
                                  for rev in (base, head)]
            if not new_tree or new_tree.split()[0] != '100644':
                # Existing executable checker wrappers are allowed only as AST data.
                if not (new_tree and old_tree and new_tree.split()[0] == old_tree.split()[0] ==
                        '100755' and path in CONSTANTS):
                    raise ValueError('scope removal, symlink, executable addition, or mode change')
            if old_tree and old_tree.split()[0] != new_tree.split()[0]:
                raise ValueError('file mode changed')
            before = git(root, 'show', base + ':' + path).decode() if old_tree else ''
            after = git(root, 'show', head + ':' + path).decode()
            if policy_file(path):
                if path not in reviewed:
                    raise ValueError('policy/baseline/allow/exclusion growth requires --reviewed-allow')
                added_lines(before, after)
                reason = 'explicitly reviewed policy additions; all generic controls retained'
            elif path in INVENTORIES:
                from check_inventory import parse_names
                first, last = parse_names(before, path), parse_names(after, path)
                exact_names(last)
                ordered_additions(first, last)
                reason = 'parsed inventory additions'
            elif path == 'scripts/claims-model-scope.txt':
                lines = added_lines(before, after)
                for line in lines:
                    if not line.strip() or line.lstrip().startswith('#'):
                        continue
                    pair = line.split()
                    if len(pair) != 2 or not pair[0].startswith('AvailableChainFGSA.Model.'):
                        raise ValueError('invalid audit owner/name map entry')
                    exact_names(pair)
                reason = 'exact owner/name map additions'
            elif path in SNAPSHOTS:
                reason = f'structural snapshot additions: {snapshot_additions(before, after)}'
            elif path in CONSTANTS:
                reason = 'AST coverage-list additions: ' + ', '.join(constant_additions(
                    before, after, CONSTANTS[path], path.endswith('.sh')))
            elif (path.endswith('.lean') and
                  any(path == p + '.lean' or path.startswith(p + '/') for p in P0) and
                  not re.search(r'Check|Control', path) and
                  ('/Tests/' not in path or not old_tree)):
                reason = 'P0 source addition or extraction; complete positive and package G0 checks required'
            elif path.startswith(('scripts/', 'docs/api/')) or path in matched:
                raise ValueError('checker logic, parser, fixture, toolchain, dependency, or unknown checker data')
            elif path.startswith('docs/') and path.endswith('.md'):
                reason = 'non-checker documentation'
            else:
                raise ValueError('ambiguous change outside P0 source and approved data additions')
            evidence.append(dict(path=path, reason=reason))
        except (ValueError, SyntaxError, TypeError) as error:
            raise ValueError(path + ': ' + str(error)) from None
    return dict(mode='integration', provisional=True, eligible=True, base=base, head=head,
                matched_checker_paths=matched, reviewed_allow=reviewed, evidence=evidence,
                neg=1 if reviewed else 0,
                deferred_controls=[] if reviewed else deferred_controls(root),
                main_accepted=False, full_receipt=False)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('base')
    parser.add_argument('--reviewed-allow', action='append', default=[])
    parser.add_argument('--complete', type=Path)
    args = parser.parse_args()
    try:
        record = select(args.root, args.base, reviewed=args.reviewed_allow)
        if args.complete:
            if json.loads((args.complete / 'integration.json').read_text()) != record:
                raise ValueError('candidate or eligibility changed during the gate')
            required = set(import_module('full-pass').STEPS) | {'package-g0'}
            if record['neg']:
                required.add('checker-self-tests')
            actual = {p.stem for p in args.complete.glob('*.result')}
            if actual != required:
                raise ValueError('incomplete provisional step coverage')
            results = {}
            for step in sorted(required):
                rc, wall = (args.complete / (step + '.result')).read_text().split()
                if rc != '0' or not wall.isdigit():
                    raise ValueError('failed provisional step: ' + step)
                results[step] = dict(rc=0, wall_s=int(wall))
            g0 = json.loads((args.complete / 'package-g0.json').read_text())
            if not g0['results'] or any(row['rc'] != 0 for row in g0['results']):
                raise ValueError('missing or failed package G0 results')
            record.update(result='PROVISIONAL PASS', positive_steps=results, package_g0=g0)
            (args.complete / 'integration-result.json').write_text(json.dumps(record, sort_keys=True) + '\n')
        print(json.dumps(record, sort_keys=True))
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(2, 'INTEGRATION REFUSED: ' + str(error) + '\n')
