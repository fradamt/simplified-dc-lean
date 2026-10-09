#!/usr/bin/env python3
"""Record/check PC-SA sources and compiled statement dependencies, read-only.

Run through the installed Lean wrapper. The probe is a temporary copy of the
existing V2Manifest helper definitions; no repository Lean source is changed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
PROBE = r'''
def statementDeps (ci : ConstantInfo) : Array Name :=
  deps ci ++ match ci with
    | .inductInfo d => d.ctors.toArray
    | _ => #[]

def statementClosure (env : Environment) (n : Name) : Except String (Array Name) := do
  let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert n
  let mut stack := #[n]
  let mut out := #[]
  while h : stack.size > 0 do
    let m := stack[stack.size - 1]
    stack := stack.pop
    out := out.push m
    let some ci := env.find? m | throw s!"missing declaration: {m}"
    for d in statementDeps ci do
      unless seen.contains d do
        seen := seen.insert d
        stack := stack.push d
  return out

def main (args : List String) : IO UInt32 := do
  unless args == ["--scope", "pcsa"] do
    IO.eprintln "expected --scope pcsa"
    return 2
  let scope := Scope.pcsa
  let env ← importModules (← familyImports scope) {}
  let decls ← runCore env (scan scope)
  let mut roots : Array Json := #[]
  let mut all : Std.HashSet Name := {}
  for m in sortedModules decls do
    for (n, k) in decls.getD m #[] do
      let h ← runCore env (entryHex scope n)
      roots := roots.push (Json.mkObj [("name", toJson n.toString),
        ("kind", toJson k), ("module", toJson m.toString), ("manifest_digest", toJson h)])
      match statementClosure env n with
      | .error e => IO.eprintln e; return 2
      | .ok ns => for d in ns do all := all.insert d
  let mut nodes : Array Json := #[]
  for n in all.toArray.qsort Name.lt do
    let some ci := env.find? n | IO.eprintln s!"missing {n}"; return 2
    let us := (List.range ci.levelParams.length).map fun i => Level.param (.mkSimple s!"u{i}")
    let norm (e : Expr) := e.instantiateLevelParams ci.levelParams us
    let value : Json := match ci with
      | .defnInfo d => toJson (reprStr (norm d.value))
      | .opaqueInfo d => toJson (reprStr (norm d.value))
      | _ => Json.null
    let ctors : Array String := match ci with
      | .inductInfo d => d.ctors.toArray.map Name.toString
      | _ => #[]
    let rs ← runCore env do pure (reducibilityTag (getReducibilityStatusCore env n))
    let inst ← runCore env do pure (Meta.isInstanceCore env n)
    nodes := nodes.push (Json.mkObj [("name", toJson n.toString),
      ("kind_tag", toJson (kindTag ci).toNat), ("universe_count", toJson ci.levelParams.length),
      ("type_expr", toJson (reprStr (norm ci.type))), ("value_expr", value),
      ("constructors", toJson ctors), ("reducibility_tag", toJson rs.toNat),
      ("is_instance", toJson inst), ("own_hash", toJson (hex (ownHash ci))),
      ("dependencies", toJson ((statementDeps ci).qsort Name.lt |>.map Name.toString))])
  IO.println (Json.mkObj [("roots", toJson roots), ("nodes", toJson nodes)]).compress
  return 0
'''


def sha(content):
    return hashlib.sha256(content).hexdigest()


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()


def manifest(path):
    module = None
    entries = []
    for line in path.read_text().splitlines():
        heading = re.fullmatch(r'### `([^`]+)`', line)
        if heading:
            module = heading[1]
        entry = re.fullmatch(r'([a-z]+) (\S+) ([0-9a-f]{16})', line)
        if entry:
            entries.append(dict(name=entry[2], kind=entry[1], module=module, manifest_digest=entry[3]))
    return entries


def record(base):
    # Verify D15 before extracting a separate baseline. Never write PCSA-API.md.
    subprocess.run(['lake', 'env', 'lean', '--run', 'scripts/V2Manifest.lean',
                    '--scope', 'pcsa', '--check'], cwd=ROOT, check=True)
    tool = ROOT / 'scripts/V2Manifest.lean'
    tool_bytes = tool.read_bytes()
    helpers = tool.read_text().split('def main (args : List String)')[0]
    with tempfile.TemporaryDirectory(prefix='fgsa-port-pcsa-') as scratch:
        probe = Path(scratch) / 'PCSAPortBaseline.lean'
        probe.write_text(helpers + PROBE)
        result = subprocess.check_output(['lake', 'env', 'lean', '--run', str(probe),
                                          '--scope', 'pcsa'], cwd=ROOT, text=True)
    graph = json.loads(result)
    if sorted(graph['roots'], key=lambda e: e['name']) != sorted(
            manifest(ROOT / 'docs/PCSA-API.md'), key=lambda e: e['name']):
        raise ValueError('compiled roots differ from docs/PCSA-API.md')
    nodes = {n['name']: n for n in graph['nodes']}
    # This hashes complete normalized kernel representations, not only ownHash.
    # Shared/private/library constants are all kept; theorem proof values are omitted.
    node_digests = {name: sha(canonical(node)) for name, node in nodes.items()}
    for name, node in nodes.items():
        node['kernel_node_sha256'] = node_digests[name]
        node['type_expr_sha256'] = sha(node.pop('type_expr').encode())
        value = node.pop('value_expr')
        node['value_expr_sha256'] = sha(value.encode()) if value is not None else None
    for entry in graph['roots']:
        seen, stack = set(), [entry['name']]
        while stack:
            name = stack.pop()
            if name in seen:
                continue
            seen.add(name)
            stack.extend(nodes[name]['dependencies'])
        parts = [[name, node_digests[name]] for name in sorted(seen)]
        entry['dependency_count'] = len(seen)
        entry['statement_dependency_sha256'] = sha(canonical(parts))
    paths = sorted(str(p.relative_to(ROOT)) for lib in
                   ('AvailableChainPCSA', 'AvailableChainPCSARun', 'AvailableChainPCSAClaims')
                   for p in (ROOT / lib).rglob('*.lean'))
    sources = {p: sha((ROOT / p).read_bytes()) for p in paths if p.endswith('.lean') and
               p.startswith(('AvailableChainPCSA/', 'AvailableChainPCSARun/', 'AvailableChainPCSAClaims/'))}
    statement_sources = {p: h for p, h in sources.items() if '/Statements/' in p or
                         '/Claims/' in p or p == 'AvailableChainPCSAClaims/PCSAClaims.lean'}
    return dict(format_version=1, base_revision=base, scope='pcsa',
                toolchain=(ROOT / 'lean-toolchain').read_text().strip(),
                package_pins_sha256=sha((ROOT / 'lake-manifest.json').read_bytes()),
                manifest_tool_sha256=sha(tool_bytes),
                manifest_sha256=sha((ROOT / 'docs/PCSA-API.md').read_bytes()),
                dependency_format='pcsa-kernel-repr-v1: V2Manifest deps/closure plus inductive constructor traversal; all libraries, public and private; normalized universes; type and definition/opaque value repr; inductive constructors; reducibility and instance status; theorem types only. Canonical UTF-8 JSON sorted keys, no whitespace. Node digest: SHA-256 of the full canonical raw node before expression fields are replaced by their SHA-256 values. Root digest: SHA-256 of sorted [name, raw node SHA-256] pairs.',
                source_digest_format='SHA-256 of exact source bytes',
                source_statement_digests=statement_sources,
                pcsa_model_run_claim_source_digests=sources,
                compiled_statement_roots=graph['roots'],
                compiled_dependency_nodes=graph['nodes'],
                compiled_dependency_graph_sha256=sha(canonical(graph)),
                validation='V2Manifest --scope pcsa --check; roots equal the read-only committed PC-SA manifest. This is a separate baseline; WP00c still owns the FG-SA deep checker.')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=ROOT / 'docs/FGSA-PORT-PCSA-BASELINE.json')
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    before = (ROOT / 'docs/PCSA-API.md').read_bytes()
    base = json.loads(args.output.read_text())['base_revision'] if args.check else subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    data = record(base)
    if before != (ROOT / 'docs/PCSA-API.md').read_bytes():
        raise ValueError('PCSA-API.md changed during read-only baseline extraction')
    if args.check:
        expected = json.loads(args.output.read_text())
        # The port adds the FG-SA deep checker to V2Manifest. Keep its original
        # tool SHA as provenance; compare PC-SA source and kernel data directly.
        ignored = {'manifest_tool_sha256', 'validation'}
        if {k: v for k, v in data.items() if k not in ignored} != {
                k: v for k, v in expected.items() if k not in ignored}:
            raise ValueError('PC-SA baseline differs')
        if data['manifest_tool_sha256'] != expected['manifest_tool_sha256']:
            print('manifest tool changed; PC-SA source and compiled dependency data match')
    else:
        # Compact graph nodes keep this data snapshot small and reviewable.
        fields = []
        for key, value in data.items():
            if key == 'compiled_dependency_nodes':
                body = '[\n' + ',\n'.join('    ' + json.dumps(n, ensure_ascii=False, separators=(',', ':')) for n in value) + '\n  ]'
            else:
                body = json.dumps(value, indent=2, ensure_ascii=False)
            fields.append('  ' + json.dumps(key) + ': ' + body)
        args.output.write_text('{\n' + ',\n'.join(fields) + '\n}\n')
    print(f'fgsa-port-pcsa-baseline: PASS ({len(data["source_statement_digests"])} source statement files; '
          f'{len(data["compiled_statement_roots"])} compiled roots; {len(data["compiled_dependency_nodes"])} dependencies)')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as exc:
        print(f'fgsa-port-pcsa-baseline: FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
