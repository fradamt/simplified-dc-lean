#!/usr/bin/env python3
"""Keep checker code from main and literal guard lists from the target."""
import argparse
import ast
from pathlib import Path
import sys
sys.dont_write_bytecode = True
import subprocess
from check_inventory import parse_names

LISTS = ('EXPECTED', 'ORDER')
CHECKER = 'scripts/check-fgsa-claims.sh'


def read_guard(text, label, inventory_text=None):
    lines = text.splitlines(keepends=True)
    start = next((i + 1 for i, line in enumerate(lines) if "<<'PY'" in line), None)
    if start is None:
        raise ValueError(f'{label}: missing Python heredoc')
    end = next((i for i in range(start, len(lines))
                if lines[i].rstrip('\r\n') == 'PY'), None)
    if end is None:
        raise ValueError(f'{label}: missing Python heredoc terminator')
    body = lines[start:end]
    tree = ast.parse(''.join(body), filename=str(label))
    lists = {}
    for name in LISTS:
        nodes = [node for node in tree.body if isinstance(node, ast.Assign)
                 and any(isinstance(t, ast.Name) and t.id == name for t in node.targets)]
        if len(nodes) != 1:
            raise ValueError(f'{label}: {name} needs one top-level literal tuple')
        node = nodes[0]
        external = (name == 'EXPECTED' and isinstance(node.value, ast.Call)
                    and ast.dump(node.value) == ast.dump(ast.parse(
                        "read_names('scripts/fgsa-claims-expected.txt')", mode='eval').body))
        if external:
            before = body[node.lineno - 1].encode()[:node.col_offset].strip()
            after = body[node.end_lineno - 1].encode()[node.end_col_offset:].strip()
            if len(node.targets) != 1 or before or (after and not after.startswith(b'#')):
                raise ValueError(f'{label}: {name} must occupy separate lines')
            if inventory_text is None:
                inventory_text = (Path(label).parent / 'fgsa-claims-expected.txt').read_text()
            values = parse_names(inventory_text, label)
            # Expansion is literal data. No expression from the target is copied.
            body[node.lineno - 1:node.end_lineno] = [f'EXPECTED = {values!r}\n']
            return read_guard(''.join(lines[:start] + body + lines[end:]), label)
        if len(node.targets) != 1 or not isinstance(node.value, ast.Tuple):
            raise ValueError(f'{label}: {name} must be a literal tuple')
        try:
            values = ast.literal_eval(node.value)
        except (ValueError, TypeError):
            raise ValueError(f'{label}: {name} must be a literal tuple') from None
        if not all(isinstance(value, str) for value in values):
            raise ValueError(f'{label}: {name} entries must be strings')
        if len(values) != len(set(values)):
            raise ValueError(f'{label}: duplicate {name} entry')
        # Whole-line replacement must not copy other target code on those lines.
        before = body[node.lineno - 1].encode()[:node.col_offset].strip()
        after = body[node.end_lineno - 1].encode()[node.end_col_offset:].strip()
        if before or (after and not after.startswith(b'#')):
            raise ValueError(f'{label}: {name} must occupy separate lines')
        lists[name] = (start + node.lineno - 1, start + node.end_lineno, values)
    return lines, lists


def read_allow(path):
    # Older target branches have no allow file. They permit no removals.
    if not path.exists():
        return []
    entries = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        fields = line.split(None, 2)
        if len(fields) != 3 or fields[0] not in LISTS:
            raise ValueError(f'{path}:{number}: expected <LIST> <entry> <reason>')
        entries.append((fields[0], fields[1], line))
    return entries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    merge = commands.add_parser('merge')
    merge.add_argument('--code', type=Path, required=True)
    merge.add_argument('--data', type=Path, required=True)
    merge.add_argument('--out', type=Path, required=True)
    superset = commands.add_parser('superset')
    source = superset.add_mutually_exclusive_group(required=True)
    source.add_argument('--main', type=Path)
    source.add_argument('--main-rev')
    superset.add_argument('--target', type=Path, required=True)
    superset.add_argument('--allow', type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.command == 'merge':
            code, main_lists = read_guard(args.code.read_text(), args.code)
            data, target_lists = read_guard(args.data.read_text(), args.data)
            # Replace from the bottom so line offsets stay correct.
            for name in sorted(LISTS, key=lambda name: main_lists[name][0], reverse=True):
                first, last, _ = main_lists[name]
                target_first, target_last, _ = target_lists[name]
                code[first:last] = data[target_first:target_last]
            args.out.write_text(''.join(code))
            return 0
        if args.main_rev is not None:
            label = f'{args.main_rev}:{CHECKER}'
            result = subprocess.run(['git', 'show', label], capture_output=True, text=True)
            if result.returncode:
                raise ValueError(f'cannot read {label}: {result.stderr.strip()}')
            main_text = result.stdout
        else:
            label = args.main
            main_text = args.main.read_text()
        inventory_text = None
        external = "read_names('scripts/fgsa-claims-expected.txt')" in main_text
        if args.main_rev is not None and external:
            data = subprocess.run(['git', 'show',
                f'{args.main_rev}:scripts/fgsa-claims-expected.txt'],
                capture_output=True, text=True)
            if data.returncode:
                raise ValueError('cannot read historical EXPECTED inventory')
            inventory_text = data.stdout
        _, main_lists = read_guard(main_text, label, inventory_text)
        _, target_lists = read_guard(args.target.read_text(), args.target)
        allow = read_allow(args.allow)
        allowed = {(name, entry) for name, entry, _ in allow}
        removed = [(name, entry) for name in LISTS
                   for entry in dict.fromkeys(main_lists[name][2])
                   if entry not in target_lists[name][2]]
        violations = [item for item in removed if item not in allowed]
        for name, entry in violations:
            print(f'GUARD LIST REMOVED: {name} {entry} (not in {args.allow})')
        for name, entry, line in allow:
            if (name, entry) not in removed:
                print(f'stale allow: {line}')
        if violations:
            return 1
        print('guard lists: superset OK')
        return 0
    except (OSError, ValueError, SyntaxError) as error:
        parser.error(str(error))


if __name__ == '__main__':
    raise SystemExit(main())
