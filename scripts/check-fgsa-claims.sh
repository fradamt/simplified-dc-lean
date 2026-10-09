#!/usr/bin/env bash
# P3 F0.0b: Claims, Proofs and Inhabit guard. The compiled auditors below
# adapt the CURRENT T7.1 auditors, including their generated-owner rules.
# No baseline is written. Temporary fixtures under .lake are removed on exit.
# SOURCE_ONLY=1 runs source findings and facade/F4 coverage, without controls or Lean.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
if [ "${SOURCE_ONLY:-0}" != 1 ]; then gate_slots_init; fi
exec python3 - "$@" <<'PY'
from pathlib import Path
import importlib.util
import os
import re
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
sys.path.insert(0, 'scripts')
import check_common as C
import import_policy as P
from check_inventory import read_names
from importlib import import_module
current_inventory = import_module('current-inventory')
spec = importlib.util.spec_from_file_location('layers', 'scripts/check-layers.py')
L = importlib.util.module_from_spec(spec)
sys.modules['layers'] = L
spec.loader.exec_module(L)
ROOT = Path.cwd()
SOURCE_ONLY = os.environ.get('SOURCE_ONLY', '0') == '1'
NEG = os.environ.get('NEG', '1') == '1'
LIBS = ('AvailableChainFGSAClaims', 'AvailableChainFGSAProofs', 'AvailableChainFGSAInhabit')
CLAIMS, PROOFS, INHABIT = LIBS
ROOT_LIBS = (*LIBS, "AvailableChainPCSAProofs")
# Keep this minimum scope independent of the data file. The _def rows are
# required even when their declarations do not yet exist.
REQUIRED_MODEL_SCOPE = {
    ('AvailableChainFGSA.Model.RowCore', 'AvailableChain.FGSA.parentFoldState'),
    ('AvailableChainFGSA.Model.RowCore', 'AvailableChain.FGSA.parentFoldState_def'),
    ('AvailableChainFGSA.Model.Objects', 'AvailableChain.FGSA.Params.actionTime'),
    ('AvailableChainFGSA.Model.Objects', 'AvailableChain.FGSA.Params.actionTime_def'),
}


def read_model_scope(raw):
    rows, seen = [], set()
    for line in raw.splitlines():
        fields = line.split('#', 1)[0].split()
        if not fields:
            continue
        if len(fields) != 2 or not fields[0].startswith('AvailableChainFGSA.Model.') or not all(
                re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', value) for value in fields):
            raise SystemExit(f'INVALID MODEL AUDIT SCOPE: {line}')
        if not Path(fields[0].replace('.', '/') + '.lean').is_file():
            raise SystemExit(f'MISSING MODEL AUDIT MODULE: {fields[0]}')
        pair = tuple(fields)
        if pair in seen:
            raise SystemExit('DUPLICATE MODEL AUDIT SCOPE: ' + ' '.join(pair))
        seen.add(pair)
        rows.append(pair)
    missing = REQUIRED_MODEL_SCOPE - seen
    if missing:
        raise SystemExit('MISSING MODEL AUDIT SCOPE: ' +
                         ', '.join(' '.join(pair) for pair in sorted(missing)))
    return rows


MODEL_SCOPE = read_model_scope(Path('scripts/claims-model-scope.txt').read_text())
MODEL_ROOTS = sorted({module for module, _ in MODEL_SCOPE})
# Required declarations: later tasks add their principal outputs here.
EXPECTED = read_names('scripts/fgsa-claims-expected.txt')
# WC Job 4 adds no Statements module; the WC entries keep their current order.
ORDER = ('Recurrence', 'Bounds', 'BoundsW', 'Reads', 'Counts', 'Regimes', 'OutageContinuation', 'Windows',
         'Packages.Safety', 'OutputReads', 'Packages.Inclusion', 'Packages.Outage', 'Channels', 'Witness',
         'ChannelProps', 'FinalityApi', 'Healed', 'HealedBest', 'WeakContinuation', 'WeakContinuationLive', 'WeakContinuationGrowth', 'Packages.Finality', 'Packages.FinalityGST',
         'LiveDC', 'FrameNext', 'ComposeStmt', 'ComposeNext', 'Fold',
         'Phases', 'PhasesInternal', 'Packages.Healing')
def audit_workers():
    values = []
    # Two is the measured default: control RSS exceeded 7 GiB on the Mac.
    for key, default in (('AUDIT_WORKERS', '2'), ('LEAN_SLOTS', '3'),
                         ('GATE_SLOTS', os.environ.get('LEAN_SLOTS', '3'))):
        value = os.environ.get(key, default)
        if not re.fullmatch(r'[1-9][0-9]*', value):
            raise SystemExit(f'{key} must be a positive integer')
        values.append(int(value))
    return 1 if os.environ.get('AUDIT_SERIAL', '0') == '1' else min(values)

workers = audit_workers()
# The generated Lean code and the control pool use the same bound.
os.environ['AUDIT_WORKERS'] = str(workers)

if not SOURCE_ONLY:
    from audit_pool import AuditPool
    pool = AuditPool(ROOT / '.lake', workers, temp_prefix='fgsa-claims-check.',
                     slot_script=ROOT / 'scripts/gate-common.sh')
    work = pool.work
    print(f'FGSA claims temporary audit logs: {work}', flush=True)
    run, run_pool = pool.run, pool.run_pool

# Source policy: use check (e), then the tighter P3/T7 direct-import set.
ctx = L.load_context(ROOT)

def owned(name):
    return any(L.under(name, lib) for lib in LIBS)

def sources():
    files = []
    for lib in LIBS:
        files.append(Path(lib + '.lean'))
        for directory, _, names in os.walk(lib, followlinks=True):
            files.extend(Path(directory) / n for n in sorted(names) if n.lower().endswith('.lean'))
    return sorted(files)

def module(path):
    return str(path.with_suffix('')).replace(os.sep, '.')

def direct_ok(m, dep):
    if dep == 'Init':
        return True
    if m in LIBS:
        return L.under(dep, m) and dep != m and not L.is_test(dep)
    # SYN L58: one exact Assembly root may import the claim facade.
    if (m, dep) == (L.ASSEMBLY_ROOT, CLAIMS + '.FGSAClaims'):
        return True
    if dep in LIBS or dep.endswith('.FGSAClaims'):
        return False
    if (m, dep) in L.COMPOSE_EDGES:
        return True  # the shared exact adapter/wrapper pairs, with no prefix exception
    if dep.startswith(('AvailableChainGridCO.Proofs.', 'AvailableChainKit.',
                       'AvailableChainStatements.')) or dep == 'AvailableChainModel.Generic.Run':
        return False
    if L.under(m, CLAIMS) and L.is_proof(ctx, dep):
        return False
    if L.under(m, INHABIT) and L.under(dep, PROOFS):
        return False
    if owned(dep):
        return True  # check (e) and order below apply to every internal edge
    if P.matches('claimsExternal', dep) or dep in ctx.definitions:
        return True
    return not L.under(m, CLAIMS) and P.matches('claimsProof', dep)

# O m4: the F2 constants are the declarations of Statements/CleanInvariant.
F2_NAMES = set(re.findall(r"(?m)^(?:def|structure|abbrev|theorem)\s+([A-Za-z_][A-Za-z0-9_']*)",
                          Path(PROOFS + '/Statements/CleanInvariant.lean').read_text()))

def source_findings(m, raw):
    imports, body = L.read_header(raw)
    owner = next(x for x in LIBS if L.under(m, x))
    item = L.Module(m, Path(m.replace('.', '/') + '.lean'), owner, m in LIBS, imports, body)
    findings = []
    for dep in imports:
        for rule, predicate in L.EDGE_RULES.items():
            if predicate(ctx, item, dep):
                findings.append(f'{rule}: {m} imports {dep}')
        if not direct_ok(m, dep):
            findings.append(f'IMPORT NOT ALLOWED: {m} imports {dep}')
        prefix = CLAIMS + '.Statements.'
        if m.startswith(prefix) and dep.startswith(prefix):
            left, right = m[len(prefix):], dep[len(prefix):]
            if left not in ORDER or right not in ORDER or ORDER.index(right) >= ORDER.index(left):
                findings.append(f'MODULE ORDER: {m} imports {dep}')
        if dep in (prefix + 'CleanInvariant', PROOFS + '.Statements.CleanInvariant') or dep.endswith('Internal'):
            lane = 'Clean' if dep.endswith('CleanInvariant') else 'Finality'
            if not m.startswith(PROOFS + '.Proofs.' + lane + '.'):
                findings.append(f'INTERNAL STATEMENT: {m} imports {dep}')
        if L.under(m, CLAIMS) and dep.startswith(PROOFS + '.Proofs.Clean.'):
            findings.append(f'CLEAN PROOF PATH: {m} imports {dep}')
    if L.under(m, CLAIMS):
        for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", C.strip(raw)):
            last = tok.split('.')[-1]
            if last in F2_NAMES and (tok == last or tok.endswith('Run.' + last)):
                findings.append(f'F2 CONSTANT: {m} names {tok}')
    if m in LIBS and body:
        findings.append(f'B7-BODY: {m}')
    clean = C.strip(raw)
    if re.search(r'\b(native_decide|sorry|admit|axiom)\b|\+native|native\s*:=\s*true|\bofReduce(?:Bool|Nat)\b', clean):
        findings.append(f'FORBIDDEN EVALUATION/AXIOM: {m}')
    if L.under(m, CLAIMS):
        lf = C.LeanFile(owner, str(item.path), m)
        lf._raw = raw
        decls = C.declarations(lf)
        defs = {d.full for d in decls if d.kind == 'def'}
        for d in decls:
            if d.kind in ('theorem', 'lemma') and not (
                m.startswith(CLAIMS + '.Statements.') and
                d.short.endswith('_def') and d.full[:-4] in defs
            ):
                findings.append(f'F-28: {m} {d.full}')
    if L.under(m, PROOFS) and not L.is_test(m) and m != PROOFS:
        if re.search(r'@\[[^]]*\bexpose\b', clean):
            findings.append(f'PROOF EXPOSE: {m}')
        if re.search(r'\b(theorem|lemma|def)\b', clean) and 'public section' not in clean:
            findings.append(f'PROOF PUBLIC SECTION: {m}')
    # Use T7's exact comment-aware V2-open parser, including quoted names,
    # multi-line opens, hiding, selective Auth/Signed, export and namespace.
    t7 = Path('scripts/check-fgsa-run.sh').read_text()
    parser = t7.split("v2_open='", 1)[1].split("'\ncheck_v2_open()", 1)[0]
    parsed = subprocess.run(['perl', '-CSD', '-e', parser], input=clean,
                            text=True, capture_output=True, check=True)
    if parsed.stdout:
        findings.append(f'V2 NAME CLASH: {m}: {parsed.stdout.strip()}')
    return findings

files = sources()
findings = [f for p in files for f in source_findings(module(p), p.read_text())]
if findings:
    print('\n'.join(findings))
    raise SystemExit(1)
current_inventory.check_source('fgsa-claims', EXPECTED)
if SOURCE_ONLY:
    result = subprocess.run(['python3', 'scripts/check-layers.py'])
    if result.returncode:
        raise SystemExit(result.returncode)
else:
    run('layers', ['python3', 'scripts/check-layers.py'])

def compose_source_controls():
    dep = L.COMPOSE + '.Statements.EventReads'
    for importer in (CLAIMS + '.Statements.Control', INHABIT + '.Control',
                     PROOFS + '.Proofs.Shared.Claims', PROOFS + '.Proofs.Finality.Control',
                     PROOFS + '.Proofs.Shared.FGCompose.Extra'):
        expected = f'UPSTREAM-COMPOSE: {importer} imports {dep}'
        assert expected in source_findings(importer, f'module\npublic import {dep}\n'), expected
    for importer, dep in sorted(L.COMPOSE_EDGES):
        if owned(importer):
            found = source_findings(importer, f'module\npublic import {dep}\n')
            assert not found, (importer, dep, found)
    importer = PROOFS + '.Proofs.Shared.FGCompose'
    dep = L.COMPOSE + '.Statements.EventReads.Extra'
    expected = f'UPSTREAM-COMPOSE: {importer} imports {dep}'
    assert expected in source_findings(importer, f'module\npublic import {dep}\n'), expected
    print('CONTROL Compose claims exact edges: PASS', flush=True)

if not SOURCE_ONLY and os.environ.get('NEG', '1') == '1':
    compose_source_controls()


def check_source_coverage(imports, roots):
    imports = {**{m.name: m.imports for m in ctx.modules.values()
                  if L.under(m.name, "AvailableChainPCSAProofs")}, **imports}
    roots = list(dict.fromkeys([*roots, *imports]))
    # Every production module must be in its root facade's transitive closure.
    def closure(starts):
        seen = set()
        pending = list(starts)
        while pending:
            m = pending.pop()
            if m in seen:
                continue
            seen.add(m)
            pending.extend(imports.get(m, ()))
        return seen

    # PhasesInternal is restricted to F4/Finality. The facade cannot import it.
    f4_only = {CLAIMS + '.Statements.PhasesInternal'}
    for lib in ROOT_LIBS:
        seen = closure([lib])
        missing = [m for m in roots if L.under(m, lib) and not L.is_test(m) and m not in seen
                   and m not in f4_only]
        if missing:
            raise SystemExit('NOT IMPORTED BY ROOT: ' + ', '.join(missing))
    f4_tree = [m for m in roots if L.proof_path(m)[:1] in (('F4',), ('Finality',))]
    if f4_tree:
        seen = closure(f4_tree)
        unreached = sorted(m for m in f4_only if m in roots and m not in seen)
        if unreached:
            raise SystemExit('NOT REACHED FROM F4: ' + ', '.join(unreached))

# The PC-SA root must reach every production module, as the FG-SA roots do.
if NEG:
    pcsa_orphan = "AvailableChainPCSAProofs.Proofs.Foundations.CoverageNegative"
    try:
        check_source_coverage({}, [pcsa_orphan])
    except SystemExit as exc:
        assert str(exc) == "NOT IMPORTED BY ROOT: " + pcsa_orphan, exc
    else:
        raise SystemExit("PC-SA ROOT COVERAGE CONTROL FAILED")

if SOURCE_ONLY:
    source_edges = {module(p): L.read_header(p.read_text())[0] for p in files}
    check_source_coverage(source_edges, list(source_edges))
    print('FGSA Claims/Proofs/Inhabit source checks: PASS', flush=True)
    raise SystemExit(0)

# Scope controls use the real reader and the independent required pair set.
scope_controls = [
    ('duplicate-model-scope', '\n'.join(' '.join(pair) for pair in MODEL_SCOPE) +
     '\n\t' + '\t'.join(MODEL_SCOPE[0]) + ' # repeated pair\n',
     'DUPLICATE MODEL AUDIT SCOPE: ' + ' '.join(MODEL_SCOPE[0])),
]
for pair in sorted(REQUIRED_MODEL_SCOPE):
    scope_controls.append((
        'missing-model-scope-' + pair[1],
        '\n'.join(' '.join(row) for row in MODEL_SCOPE if row != pair),
        'MISSING MODEL AUDIT SCOPE: ' + ' '.join(pair)))
for label, raw, reason in (scope_controls if NEG else ()):
    try:
        read_model_scope(raw)
    except SystemExit as exc:
        if str(exc) != reason:
            raise SystemExit(f'STOP: {label} failed with unexpected reason: {exc}')
        print(f'{label}: rejected as expected ({reason})', flush=True)
    else:
        raise SystemExit(f'STOP: {label} passed')

# Independent source controls use the same policy function as the real scan.
controls = (
    ('statements-non-def-theorem', CLAIMS + '.Statements.Reads',
     'def fgsaControl : Nat := 0\ntheorem fgsaControl_eq : fgsaControl = 0 := rfl\n', 'F-28'),
    ('plain-v2-open', CLAIMS + '.Statements.Reads', 'open AvailableChain.V2\n', 'V2 NAME CLASH'),
    ('grid-proof-import', PROOFS + '.Proofs.Shared.Reads', 'public import AvailableChainGridCO.Proofs.Map\n', 'IMPORT NOT ALLOWED'),
    ('rightward-statement', CLAIMS + '.Statements.Reads', 'public import ' + CLAIMS + '.Statements.Counts\n', 'MODULE ORDER'),
    ('clean-proof-path', CLAIMS + '.Statements.Reads', 'public import ' + PROOFS + '.Proofs.Clean.Step\n', 'CLEAN PROOF PATH'),
    ('f2-constant-in-claim', CLAIMS + '.Claims.Clean',
     'public section\n'
     'def fgsaF2Control : Prop := ∀ (p : AvailableChain.FGSA.Params) '
     '(c : AvailableChain.FGSA.Run.AppCodec Unit) (E : AvailableChain.Generic.Env Unit) '
     '(rho : AvailableChain.V2.Run Unit (AvailableChain.FGSA.Run.fgsa p c)), '
     'AvailableChain.FGSA.Run.CleanHist p c E rho 0\n', 'F2 CONSTANT'),
    ('clean-invariant-import', PROOFS + '.Proofs.Outage.Step',
     'public import ' + PROOFS + '.Statements.CleanInvariant\n', 'INTERNAL STATEMENT'),
    ('claims-proof-import', CLAIMS + '.Claims.Clean', 'public import AvailableChainFGSARun.Proofs.ClientTrace\n', 'IMPORT NOT ALLOWED'),
    ('facade-tests', CLAIMS, 'public import ' + CLAIMS + '.Tests.Axioms\n', 'B7-TESTS'),
    ('cross-lane-proof', PROOFS + '.Proofs.Clean.Step', 'public import ' + PROOFS + '.Proofs.Outage.Step\n', 'LANE'),
    ('cross-lane-export', PROOFS + '.Proofs.Clean.Step', 'public import ' + PROOFS + '.Proofs.Outage.Export\n', 'EXPORT-USE'),
    ('shared-lane-proof', PROOFS + '.Proofs.Shared.Reads', 'public import ' + PROOFS + '.Proofs.Clean.Step\n', 'SHARED'),
    # SYN L58: direct_ok and the layer predicates apply together.
    ('assembly-control-facade', PROOFS + '.Proofs.Assembly.Control',
     'public import ' + CLAIMS + '.FGSAClaims\n', 'IMPORT NOT ALLOWED'),
    ('assembly-root-sibling-facade', PROOFS + '.Proofs.Assembly.RootExtra',
     'public import ' + CLAIMS + '.FGSAClaims\n', 'IMPORT NOT ALLOWED'),
    ('assembly-root-child-facade', L.ASSEMBLY_ROOT + '.Extra',
     'public import ' + CLAIMS + '.FGSAClaims\n', 'IMPORT NOT ALLOWED'),
    ('assembly-control-root', PROOFS + '.Proofs.Assembly.Control',
     'public import ' + L.ASSEMBLY_ROOT + '\n', 'ASSEMBLY'),
    ('assembly-root-claims-root', L.ASSEMBLY_ROOT,
     'public import ' + CLAIMS + '\n', 'IMPORT NOT ALLOWED'),
    ('assembly-root-proofs-root', L.ASSEMBLY_ROOT,
     'public import ' + PROOFS + '\n', 'IMPORT NOT ALLOWED'),
    ('assembly-root-raw-lane', L.ASSEMBLY_ROOT,
     'public import ' + PROOFS + '.Proofs.Foundations.Store\n', 'ASSEMBLY'),
    ('assembly-root-lane-export', L.ASSEMBLY_ROOT,
     'public import ' + PROOFS + '.Proofs.Foundations.Export\n', 'ASSEMBLY'),
    ('assembly-root-unnamed-lower', L.ASSEMBLY_ROOT,
     'public import ' + PROOFS + '.Proofs.Assembly.Other\n', 'ASSEMBLY'),
    ('assembly-root-lower-child', L.ASSEMBLY_ROOT,
     'public import ' + PROOFS + '.Proofs.Assembly.Foundations.Extra\n', 'ASSEMBLY'),
    ('assembly-root-tests', L.ASSEMBLY_ROOT,
     'public import ' + PROOFS + '.Tests.Axioms\n', 'ASSEMBLY'),
    ('assembly-root-inhabit', L.ASSEMBLY_ROOT,
     'public import ' + INHABIT + '.Control\n', 'ASSEMBLY'),
    ('assembly-root-field-claims', L.ASSEMBLY_ROOT,
     'public import ' + CLAIMS + '.Claims.Clean\n', 'CLAIM-USE'),
    ('proofs-root-shared-export', PROOFS,
     'public import ' + PROOFS + '.Proofs.Shared.Export\n', 'EXPORT-USE'),
    ('assembly-root-phases-internal', L.ASSEMBLY_ROOT,
     'public import ' + CLAIMS + '.Statements.PhasesInternal\n', 'INTERNAL STATEMENT'),
)
for label, m, body, expected in (controls if NEG else ()):
    hits = source_findings(m, 'module\n' + body)
    if not any(expected in f for f in hits):
        raise SystemExit(f'STOP: negative control passed: {label}: {hits}')
    print(f'{label}: rc 1, rejected as expected ({expected})', flush=True)

# SYN L58: each allowed edge must pass both direct_ok and every layer rule.
assembly_positives = (
    ('assembly-root-facade', L.ASSEMBLY_ROOT, CLAIMS + '.FGSAClaims'),
    ('assembly-root-foundations', L.ASSEMBLY_ROOT, PROOFS + '.Proofs.Assembly.Foundations'),
    ('assembly-root-shared', L.ASSEMBLY_ROOT, PROOFS + '.Proofs.Assembly.Shared'),
    ('assembly-root-clean', L.ASSEMBLY_ROOT, PROOFS + '.Proofs.Assembly.Clean'),
    ('assembly-root-foundation-import', L.ASSEMBLY_ROOT, 'Lean.Elab.Command'),
    ('proofs-root-assembly-root', PROOFS, L.ASSEMBLY_ROOT),
)
for label, m, dep in assembly_positives:
    hits = source_findings(m, 'module\npublic import ' + dep + '\n')
    if hits:
        raise SystemExit(f'STOP: positive control failed: {label}: {hits}')
    print(f'{label}: rc 0', flush=True)

# Future F4 coverage stays separate from facade coverage (SYN L58).
phase_internal = CLAIMS + '.Statements.PhasesInternal'
finality_control = PROOFS + '.Proofs.Finality.Control'
coverage_edges = {CLAIMS: (), PROOFS: (finality_control,), INHABIT: (),
                  phase_internal: (), finality_control: ()}
if NEG:
    try:
        check_source_coverage(coverage_edges, list(coverage_edges))
    except SystemExit as exc:
        if not str(exc).startswith('NOT REACHED FROM F4: '):
            raise
        print('missing-f4-reach: rc 1, rejected as expected (NOT REACHED FROM F4)', flush=True)
    else:
        raise SystemExit('STOP: missing F4 reach control passed')

coverage_edges[finality_control] = (phase_internal,)
check_source_coverage(coverage_edges, list(coverage_edges))
print('f4-reach-twin: rc 0', flush=True)

# Positive twin of f2-constant-in-claim: the same Prop over a frozen Claims name passes.
twin_hits = [f for f in source_findings(CLAIMS + '.Claims.Clean', 'module\npublic section\n'
    'def fgsaF2Twin : Prop := ∀ (p : AvailableChain.FGSA.Params) '
    '(c : AvailableChain.FGSA.Run.AppCodec Unit) (E : AvailableChain.Generic.Env Unit) '
    '(rho : AvailableChain.V2.Run Unit (AvailableChain.FGSA.Run.fgsa p c)), '
    'AvailableChain.FGSA.Run.CleanTruncAt p c E rho 0\n') if f.startswith('F2 CONSTANT')]
if twin_hits:
    raise SystemExit(f'STOP: F2 constant positive twin failed: {twin_hits}')
print('f2-constant-twin: rc 0 (a frozen Claims name passes)', flush=True)

# The seven home equation theorems must pass the same source policy.
reads_path = Path(CLAIMS + '/Statements/Reads.lean')
positive_hits = source_findings(module(reads_path), reads_path.read_text())
if positive_hits:
    raise SystemExit(f'STOP: Statements _def positive case failed: {positive_hits}')
print('statements-home-def-theorems: rc 0 (seven matching _def theorems)', flush=True)

def build(label, *targets):
    run(label, ['bash', '-c', 'source scripts/gate-common.sh; gate_build "$@"',
                'claims-build', *targets])

for lib in LIBS:
    build('build-' + lib, '--wfail', lib)
    build('build-' + lib + 'Tests', '--wfail', lib + 'Tests')
build('support', 'AvailableChainCheckSupport')

# Derive a compiled-edge table only AFTER source policy validation. A built
# module may not contain an edge absent from its checked source. This also
# rejects stale .oleans. Every source module is imported as an audit root;
# root-facade coverage is checked separately below.
edges = [(module(p), L.read_header(p.read_text())[0]) for p in files]
assert CLAIMS + '.FGSAClaims' in dict(edges)[L.ASSEMBLY_ROOT]
print('compiled import table: SYN L58 Assembly.Root -> FGSAClaims included', flush=True)
edge_cases = '\n'.join('  | `' + m + ' => [' + ', '.join('`' + d for d in deps) + '].contains imp' for m, deps in edges)
allowed_import = 'def allowedImport (mod imp : Name) : Bool :=\n  imp == `Init || match mod with\n' + edge_cases + '\n  | _ => false\n\n'
source = Path('scripts/CheckFGSARunAxioms.lean').read_text()
source = source.replace('import AvailableChainFGSARun\n', ''.join('import ' + x + '\n' for x in LIBS), 1)
source = source.replace('def lib : Name := `AvailableChainFGSARun',
    'def libs : List Name := [' + ', '.join('`' + x for x in LIBS) + ']\n' +
    'def inLibraries (m : Name) : Bool := libs.any (·.isPrefixOf m)')
a = source.index('def allowedImport ('); b = source.index('/-- The module names', a)
source = source[:a] + allowed_import + source[b:]
source = source.replace('parts.foldl (fun n s => Name.str n s) lib', 'parts.foldl (fun n s => Name.str n s) dir.fileName.get!.toName')
source = source.replace('lib.isPrefixOf m', 'inLibraries m')
# Only these exact Model declaration/owner pairs join the constant audit.
# Imports still use the source-validated library table. FGSA audits Model imports.
model_scope = ('def modelAuditScope : List (Name × Name) := [\n' +
               ',\n'.join(f'  (`{m}, `{n})' for m, n in MODEL_SCOPE) + ']\n\n')
source = source.replace('def inLib (env : Environment)',
                        model_scope + 'def inLib (env : Environment)', 1)
source = source.replace('| some m => inLibraries m',
    '| some m => inLibraries m || modelAuditScope.contains (m, n)', 1)
source = source.replace('let mut dir : System.FilePath := "AvailableChainFGSARun"', 'let mut dir : System.FilePath := ""')
source = source.replace('(#[lib] ++ extra)', '(libs.toArray ++ extra)')
source = source.replace('  for m in ← sourceModules dir do',
    '  let dirs := if dir.toString.isEmpty then libs.map (fun n => System.FilePath.mk n.toString) else [dir]\n' +
    '  let mut sourceMods := #[]\n  for d in dirs do sourceMods := sourceMods ++ (← sourceModules d)\n' +
    '  for m in sourceMods do')
source = source.replace('  if cs.isEmpty then\n    IO.eprintln "NO CONSTANTS FOUND"\n    return 2\n',
    '  -- Empty libraries are valid only with successful source/build coverage.\n')
# Change only the generated claims auditor. The T7 template and its users
# keep their existing behavior. Each call has a fresh CoreM state; tasks
# share the imported, read-only Environment and return data without output.
parallel_axioms = '''def auditWorkerCount : IO Nat := do
  let mut count := 2
  for key in ["AUDIT_WORKERS", "LEAN_SLOTS", "GATE_SLOTS"] do
    if let some value ← IO.getEnv key then
      let some n := value.toNat? | throw (IO.userError s!"{key} must be a positive integer")
      if n == 0 then throw (IO.userError s!"{key} must be a positive integer")
      if key == "AUDIT_WORKERS" then count := n else count := min count n
  if (← IO.getEnv "AUDIT_SERIAL") == some "1" then return 1
  return min count ((← IO.getEnv "LEAN_SLOTS").bind String.toNat? |>.getD 3)

def auditAxiomChunk (env : Environment) (chunk : Array (Nat × Name)) :
    IO (Array (Nat × Name × Array Name)) := do
  let mut rows := #[]
  for (i, n) in chunk do
    let bad := (← axiomsOf env n).filter (fun a => !allowed.contains a)
    unless bad.isEmpty do rows := rows.push (i, n, bad)
  return rows

def auditAxioms (env : Environment) (names : Array Name) :
    IO (Array (Nat × Name × Array Name)) := do
  let workers ← auditWorkerCount
  let indexed := names.mapIdx fun i n => (i, n)
  if workers == 1 then return ← auditAxiomChunk env indexed
  let size := (names.size + workers - 1) / workers
  let mut tasks := #[]
  for i in [:workers] do
    let chunk := (indexed.toList.drop (i * size) |>.take size).toArray
    unless chunk.isEmpty do tasks := tasks.push (← IO.asTask (auditAxiomChunk env chunk))
  let mut rows := #[]
  let mut error : Option IO.Error := none
  -- Join every task before propagating a failure.
  for task in tasks do
    match (← IO.wait task) with
    | .ok result => rows := rows ++ result
    | .error e => if error.isNone then error := some e
  if let some e := error then throw e
  -- Original ordinals preserve the serial diagnostic order byte for byte.
  return rows.qsort (fun a b => a.1 < b.1)

'''
source = source.replace('def main (args : List String)', parallel_axioms + 'def main (args : List String)', 1)
serial_loop = '''  for (n, _) in cs do
    let axs ← axiomsOf env n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      IO.println s!"BAD AXIOMS {n}: {bad}"
      badAxioms := true
'''
assert source.count(serial_loop) == 1, 'STOP: claims axiom loop changed'
source = source.replace(serial_loop, '''  let axiomRows ← auditAxioms env (cs.map Prod.fst).toArray
  for (_, n, bad) in axiomRows do
    IO.println s!"BAD AXIOMS {n}: {bad}"
    badAxioms := true
''', 1)
# P10/Q-10: each theorem in a lane Export has a matching Claims/<Lane>
# proposition as its type head (after binders). Helpers belong in lane files.
anchor = '  let mut badAxioms := false\n'
source = source.replace(anchor, anchor + '''  for (n, ci) in cs do
    let some m := moduleOf env n | continue
    let parts := m.components.map (·.toString)
    if parts.length == 4 && parts[0]! == "AvailableChainFGSAProofs" &&
        parts[1]! == "Proofs" && parts[3]! == "Export" then
      if ci matches .thmInfo _ then
        let head := ci.type.getForallBody.getAppFn
        let claimModule := ("AvailableChainFGSAClaims.Claims." ++ parts[2]!).toName
        unless head.constName?.any (fun c => moduleOf env c == some claimModule) do
          IO.println s!"EXPORT CLAIM TYPE: {n} must prove a Prop of {claimModule}"
          badAxioms := true
''')
audit = work / 'CheckClaimsAxioms.lean'
audit.write_text(source)
lease = Path('scripts/CheckFGSARunLease.lean').read_text()
lease = lease.replace('import AvailableChainFGSARun\n', ''.join('import ' + x + '\n' for x in LIBS), 1)
lease = lease.replace('let roots := `AvailableChainFGSARun :: extra',
    'let roots := [' + ', '.join('`' + x for x in LIBS) + '] ++ extra')
lease = lease.replace('  if cs.isEmpty then\n    IO.eprintln "NO CONSTANTS FOUND"\n    return 2\n', '')
lease_file = work / 'CheckClaimsLease.lean'
lease_file.write_text(lease)
roots = [module(p) for p in files]
args = ['lake', 'env', 'lean', '--run', str(audit)]
for m in [*roots, *MODEL_ROOTS]:
    args += ['--root', m]
if EXPECTED:
    run('inventory', ['python3', '-B', 'scripts/write-check-inventories.py',
                      '--scope', 'fgsa-claims', '--check'])
    args += ['--expect', 'AvailableChain.FGSA.Run.fgsaClaims', *EXPECTED, *[n for _, n in MODEL_SCOPE
                                     if not n.endswith('_def')]]
run('axioms-coverage-used-constants', args)
run('lease', ['lake', 'env', 'lean', '--run', str(lease_file), *roots])

# Every production module must be in its root facade's transitive closure.
# Importing all modules for the audit above cannot mask a missing facade edge.
# J3 STOP A (lead ruling 2026-09-30): PhasesInternal may be imported only by the
# F4 tree (the INTERNAL STATEMENT edge rule above), so the Claims facade cannot
# reach it. It stays in the source and compiled audit roots. Once an F4-tree
# module exists, it must reach PhasesInternal instead.
check_source_coverage(dict(edges), roots)
run('proof-eqns', ['lake', 'env', 'lean', '--run', 'scripts/CheckProofEqns.lean',
                   '--baseline', 'scripts/baselines/check-proof-eqns.txt'])
run('unused-imports', ['bash', 'scripts/shake-report.sh', '--fail-on-new', *roots])

# W1 applies the aggregate field across Proofs and Inhabit in both gate tiers.
w1_output = run('weak-continuation-w1', ['lake', 'env', 'lean', '-DwarningAsError=true',
                                      'scripts/CheckWeakContinuationW1.lean'])
w1_reports = re.findall(
    r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    w1_output)
w1_name = 'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_weakContinuationLive'
if not any(name == w1_name for name, _ in w1_reports):
    raise SystemExit('STOP: W1 axiom report missing')
w1_axioms = {name.strip() for _, axioms in w1_reports for name in axioms.split(',')
             if name.strip()}
w1_bad = w1_axioms - {'propext', 'Classical.choice', 'Quot.sound'}
if w1_bad:
    raise SystemExit(f'BAD W1 AXIOMS: {sorted(w1_bad)}')
print('weak-continuation-w1 axioms: rc 0 (standard axioms only)', flush=True)

# The gate sets NEG=0 when no checker path changed: skip compiled negative controls
# below (about 135 s on the NUC), as the other check scripts do.
if os.environ.get('NEG', '1') == '0':
    print('compiled negative controls: SKIPPED (NEG=0)', flush=True)
    print('all FGSA claims checks pass (NEG=0: no compiled negative controls)', flush=True)
    raise SystemExit(0)

# Compiled negative controls. They are never added to the real library.
# Use the real auditor and require its diagnostic, not merely a Lean error.
control_path = run('control-lean-path', ['lake', 'env', 'printenv', 'LEAN_PATH']).strip()
controls = []

def control_dir(label, *, shadow=False):
    neg = work / 'controls' / label
    neg.mkdir(parents=True)
    # A tiny offline Lake package: no dependencies or fetch step.
    (neg / 'lean-toolchain').write_text(Path('lean-toolchain').read_text())
    (neg / 'lakefile.toml').write_text('name = "fgsa-controls"\n[[lean_lib]]\nname = "FGSAControl"\nglobs = ["FGSAControl.+"]\n')
    if shadow:
        # Lean resolves an entire prefix at its first path entry. Each
        # auditor gets private built roots and only its own shadow module.
        built = ROOT / '.lake/build/lib/lean'
        for lib in LIBS:
            shutil.copytree(built / lib, neg / lib)
            for p in built.glob(lib + '.*'):
                if p.is_file():
                    shutil.copy2(p, neg / p.name)
    return neg

def shadow_env(neg):
    return dict(os.environ, LEAN_PATH=str(neg) + os.pathsep + control_path)

def run_shadow(label, args, *, expect=None):
    return run(label, ['lake', 'env', 'lean', *args], expect=expect,
               env=shadow_env(neg), cwd=neg)

def queue_shadow(label, args, *, expect):
    controls.append((label, ['lake', 'env', 'lean', *args],
                     dict(expect=expect, env=shadow_env(neg), cwd=neg)))

def write_module(name, text):
    p = neg / (name.replace('.', '/') + '.lean')
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)
    return p

def compile_module(name, text):
    p = write_module(name, text)
    run_shadow('compile-' + name.split('.')[-1],
               ['-o', str(p.with_suffix('.olean')), str(p)])
    return p

# Test the scoped Model equation without changing any production declaration.
model_owner = 'AvailableChainFGSA.Model.Objects'
model_name = 'AvailableChain.FGSA.Params.actionTime_def'
neg = control_dir('model-scope', shadow=True)
model_audit = work / 'CheckModelScope.lean'
model_text = source.replace('import ' + CLAIMS + '\n', '')
for lib in (PROOFS, INHABIT):
    model_text = model_text.replace('import ' + lib + '\n', '')
model_text = model_text.replace('(libs.toArray ++ extra)', 'extra')
model_text = model_text.replace('  for m in sourceMods do', '  for m in (#[] : Array Name) do')
model_audit.write_text(model_text)
model_fixture = compile_module(model_owner, """module
public import Init
public section
namespace AvailableChain.FGSA.Params
theorem actionTime_def : True := True.intro
theorem outsideModelScope : True := True.intro
end AvailableChain.FGSA.Params
end
""")
run_shadow('model-def-checked', ['--run', str(model_audit), '--root', model_owner,
                               '--expect', model_name])
queue_shadow('model-name-outside-scope', ['--run', str(model_audit), '--root', model_owner,
    '--expect', 'AvailableChain.FGSA.Params.outsideModelScope'], expect='NOT CHECKED:')
# The same name in another Model module must not satisfy the owner pair.
wrong_owner = 'AvailableChainFGSA.Model.ScopeControl'
neg = control_dir('model-wrong-owner', shadow=True)
compile_module(wrong_owner, model_fixture.read_text())
queue_shadow('model-def-wrong-owner', ['--run', str(model_audit), '--root', wrong_owner,
    '--expect', model_name], expect='NOT CHECKED:')
# A scoped equation must also pass the same used-constant rule as library names.
neg = control_dir('model-forbidden-use', shadow=True)
compile_module(model_owner, """module
public import AvailableChainGridCO.Proofs.Map
public section
namespace AvailableChain.FGSA.Params
theorem actionTime_def {n : Nat} (st : AvailableChain.GridCO.State n)
    (h : AvailableChain.GridCO.ComparableTargets st) :
    AvailableChain.GridCO.ComparableTargets st := h
end AvailableChain.FGSA.Params
end
""")
queue_shadow('model-forbidden-use', ['--run', str(model_audit), '--root', model_owner,
    '--expect', model_name], expect='FORBIDDEN CONSTANT: ' + model_name)

bad = PROOFS + '.Proofs.Shared.NegUse'
neg = control_dir('grid-constant-in-statement', shadow=True)
compile_module(bad, '''module
public import AvailableChainGridCO.Proofs.Map
public import AvailableChainKit.Engine.EngineClock
public section
namespace AvailableChain.FGSA.Run
def negKitClock {n : Nat} (P : AvailableChain.Generic.ProtocolSpec n) : Type :=
  AvailableChain.Engine.ClockLaws P
def negStatements : Type := AvailableChain.Statements.Generic.Constants
theorem negGridStatement {n : Nat} (st : AvailableChain.GridCO.State n)
    (h : AvailableChain.GridCO.ComparableTargets st) :
    AvailableChain.GridCO.ComparableTargets st := h
end AvailableChain.FGSA.Run
end
''')
queue_shadow('grid-constant-in-statement', ['--run', str(audit), '--root', bad],
    expect='FORBIDDEN CONSTANT: AvailableChain.FGSA.Run.negGridStatement uses AvailableChain.GridCO.ComparableTargets')
# The controls have the same FG-SA namespace and upstream reachability as T7.
lease_bad = PROOFS + '.Proofs.Shared.NegLease'
neg = control_dir('default-lease', shadow=True)
compile_module(lease_bad, '''module
public import AvailableChainFGSA.Model.Clock
public section
namespace AvailableChain.FGSA.Run
def negLease (p : AvailableChain.GridCO.Params) (st : AvailableChain.GridCO.State 1) :
    AvailableChain.GridCO.State 1 := AvailableChain.GridCO.gate p st 0
end AvailableChain.FGSA.Run
end
''')
queue_shadow('default-lease', ['--run', str(lease_file), lease_bad], expect='BAD LEASE INSTANCE')

# SYN L58: replace one ordinary Assembly .olean in the scratch copy only.
# The generated table still contains its validated, unchanged source edges.
assembly_bad = PROOFS + '.Proofs.Assembly.Foundations'
neg = control_dir('assembly-facade-compiled-import', shadow=True)
assembly_text = Path(assembly_bad.replace('.', '/') + '.lean').read_text()
compile_module(assembly_bad, assembly_text.replace(
    'module\n', 'module\npublic import ' + CLAIMS + '.FGSAClaims\n', 1))
queue_shadow('assembly-facade-compiled-import', ['--run', str(audit), '--root', assembly_bad],
    expect='COMPILED IMPORT NOT ALLOWED: ' + assembly_bad +
    ' imports ' + CLAIMS + '.FGSAClaims')

neg = control_dir('control-build')
write_module('FGSAControl.Statements.Fn', '''module
@[expose] public section
def fgsaControlFn : Bool → Nat
  | true => 1
  | false => 0
end
''')
write_module('FGSAControl.Proofs.NegEq', '''module
public import FGSAControl.Statements.Fn
public section
theorem fgsaControlEq : fgsaControlFn true = 1 := by simp [fgsaControlFn]
end
''')
write_module('FGSAControl.NegUnused', '''module
public import Init.Data.List.Sort
public section
def fgsaControlUnused : Nat := 0
end
''')
run('control-build', ['lake', 'build', 'FGSAControl'], cwd=neg)
# CheckProofEqns reads repository-relative inputs as well as its baseline.
# This extra module has a unique prefix, so Lake's path order needs no shadow.
simp_dir = work / 'controls' / 'simp-without-f-def'
unused_dir = work / 'controls' / 'unused-import-control'
shutil.copytree(neg, simp_dir)
shutil.copytree(neg, unused_dir)
control_env = dict(os.environ, LEAN_PATH=str(simp_dir / '.lake/build/lib/lean'))
controls.append(('simp-without-f-def', ['lake', 'env', 'lean', '--run', 'scripts/CheckProofEqns.lean',
    '--baseline', 'scripts/baselines/check-proof-eqns.txt', 'FGSAControl.Proofs.NegEq'],
    dict(env=control_env, expect='EQ EXPORT FGSAControl.Proofs.NegEq')))
# Use the same --fail-on-new baseline comparison as the real D47 scan.
# shake-report reads its package from cwd only via its cd, so obtain Lake's
# raw report here, then apply the same removal key and frozen baseline.
controls.append(('unused-import-control', ['lake', 'shake', 'FGSAControl.NegUnused'],
                 dict(cwd=unused_dir, expect='remove #[public import Init.Data.List.Sort]')))
run_pool(controls)
key = 'remove FGSAControl/NegUnused.lean public import Init.Data.List.Sort'
if C.read_baseline('shake-report')[key]:
    raise SystemExit('STOP: unused-import control is in the baseline')
print('unused-import baseline comparison: rc 1 (NEW removal), rejected as expected', flush=True)
print('all FGSA claims checks pass', flush=True)
PY
