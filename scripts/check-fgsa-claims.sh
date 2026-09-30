#!/usr/bin/env bash
# P3 F0.0b: Claims, Proofs and Inhabit guard. The compiled auditors below
# adapt the CURRENT T7.1 auditors, including their generated-owner rules.
# No baseline is written. Fixtures and audit logs stay under .lake.
set -euo pipefail
cd "$(dirname "$0")/.."
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
spec = importlib.util.spec_from_file_location('layers', 'scripts/check-layers.py')
L = importlib.util.module_from_spec(spec)
sys.modules['layers'] = L
spec.loader.exec_module(L)
ROOT = Path.cwd()
LIBS = ('AvailableChainFGSAClaims', 'AvailableChainFGSAProofs', 'AvailableChainFGSAInhabit')
CLAIMS, PROOFS, INHABIT = LIBS
# Required declarations: later tasks add their principal outputs here.
EXPECTED = (

    'AvailableChain.FGSA.Run.awakeHonestIn',
    'AvailableChain.FGSA.Run.HonestProposal',
    'AvailableChain.FGSA.Run.Base₂',
    'AvailableChain.FGSA.Run.HealthyPrefix₂',
    'AvailableChain.FGSA.Run.CleanPrefix₂',
    'AvailableChain.FGSA.Run.CleanCut₂',
    'AvailableChain.FGSA.Run.Clean₂',
    'AvailableChain.FGSA.Run.Recovery₂',
    'AvailableChain.FGSA.Run.BaseSet',
    'AvailableChain.FGSA.Run.CleanSet',
    'AvailableChain.FGSA.Run.CleanCutSet',
    'AvailableChain.FGSA.Run.CleanPrefixSet',
    'AvailableChain.FGSA.Run.HealingSet',
    'AvailableChain.FGSA.Run.FinalitySet',
    'AvailableChain.FGSA.Run.WinSpec',
    'AvailableChain.FGSA.Run.PtB₀',
    'AvailableChain.FGSA.Run.PtT',
    'AvailableChain.FGSA.Run.PtOut',
    'AvailableChain.FGSA.Run.cleanWinAt',
    'AvailableChain.FGSA.Run.cleanWin',
    'AvailableChain.FGSA.Run.cleanPrefixWin',
    'AvailableChain.FGSA.Run.cleanLabelWin',
    'AvailableChain.FGSA.Run.gapWin',
    'AvailableChain.FGSA.Run.formWin',
    'AvailableChain.FGSA.Run.formWinAt',
    'AvailableChain.FGSA.Run.kernelWin',
    'AvailableChain.FGSA.Run.trigWin',
    'AvailableChain.FGSA.Run.PtS',
    'AvailableChain.FGSA.Run.PtSP',
    'AvailableChain.FGSA.Run.PtSX',
    'AvailableChain.FGSA.Run.BasePrem',
    'AvailableChain.FGSA.Run.SameLabelPrem',
    'AvailableChain.FGSA.Run.SourceDisciplinePrem',
    'AvailableChain.FGSA.Run.FinalizedSafetyPrem',
    'AvailableChain.FGSA.Run.CleanPrem',
    'AvailableChain.FGSA.Run.CleanPrefixPrem',
    'AvailableChain.FGSA.Run.CleanCutPrem',
    'AvailableChain.FGSA.Run.card_eq_n_of_linked',
    'AvailableChain.FGSA.Run.CleanPrefix₂.toCleanCut',
    'AvailableChain.FGSA.Run.HealthyPrefix₂.faultQ_of_pos',
    'AvailableChain.FGSA.Run.CleanPrefix₂.faultQ',
    'AvailableChain.FGSA.Run.HealthyPrefix₂.batch',
    'AvailableChain.FGSA.Run.CleanPrefix₂.batchAt',
    'AvailableChain.FGSA.Run.Recovery₂.batch',
    'AvailableChain.FGSA.Run.fgsa_clean_delivery_iff',
    'AvailableChain.FGSA.Run.fgsa_seed_reachable',
    'AvailableChain.FGSA.Run.fgsa_seed_accepted',

    'AvailableChain.FGSA.Run.preTick_def',
    'AvailableChain.FGSA.Run.postClock_def',
    'AvailableChain.FGSA.Run.gateIn_def',
    'AvailableChain.FGSA.Run.gateResult_def',
    'AvailableChain.FGSA.Run.isGateTime_def',
    'AvailableChain.FGSA.Run.vHead_def',
    'AvailableChain.FGSA.Run.actionSourceFG_def',
    'AvailableChain.FGSA.Run.fgsa_strongW_recF',
    'AvailableChain.FGSA.Run.fgsa_lit_recF',
    'AvailableChain.FGSA.Run.fgsa_recPat_restricted',
    'AvailableChain.FGSA.Run.fgsa_recPatAt_restricted',
    'AvailableChain.FGSA.Run.fgsa_restricted_of_unrestricted',
    'AvailableChain.FGSA.Run.fgsa_horizon_mono',
    'AvailableChain.FGSA.Run.fgsa_B_max',
    'AvailableChain.FGSA.Run.L',
    'AvailableChain.FGSA.Run.P',
    'AvailableChain.FGSA.Run.Γ',
    'AvailableChain.FGSA.Run.ρΓ',
    'AvailableChain.FGSA.Run.ρ₁',
    'AvailableChain.FGSA.Run.ρ',
    'AvailableChain.FGSA.Run.E_g',
    'AvailableChain.FGSA.Run.E_j',
    'AvailableChain.FGSA.Run.B_c',
    'AvailableChain.FGSA.Run.D_c',
    'AvailableChain.FGSA.Run.B_reset',
    'AvailableChain.FGSA.Run.B',
    'AvailableChain.FGSA.Run.B_H2',
    'AvailableChain.FGSA.Run.B_H1',
    'AvailableChain.FGSA.Run.B_H',
    'AvailableChain.FGSA.Run.W_F',
    'AvailableChain.FGSA.Run.B_F',
    'AvailableChain.FGSA.Run.B_heal',
    'AvailableChain.FGSA.Run.B_best',
    'AvailableChain.FGSA.Run.B_Q',
    'AvailableChain.FGSA.Run.B_skip',
    'AvailableChain.FGSA.Run.γ',
    'AvailableChain.FGSA.Run.carrierTime2',
    'AvailableChain.FGSA.Run.kernelDeadline',
    'AvailableChain.FGSA.Run.ActionDeliveryBounds',
    'AvailableChain.FGSA.Run.KernelBeforeNextAction',
    'AvailableChain.FGSA.Run.VoteBeforeAction',
    'AvailableChain.FGSA.Run.GateAfterCarrier2',
    'AvailableChain.FGSA.Run.GateActionOrder',
    'AvailableChain.FGSA.Run.FourteenBeforeTwoRounds',
    'AvailableChain.FGSA.Run.cutPred',
    'AvailableChain.FGSA.Run.afterTicksIdx',
    'AvailableChain.FGSA.Run.afterTicks',
    'AvailableChain.FGSA.Run.SuffixIdx',
    'AvailableChain.FGSA.Run.timeIdx',
    'AvailableChain.FGSA.Run.preTick',
    'AvailableChain.FGSA.Run.postClock',
    'AvailableChain.FGSA.Run.postTick',
    'AvailableChain.FGSA.Run.afterTicks_eq_stateBefore',
    'AvailableChain.FGSA.Run.afterTicks_node',
    'AvailableChain.FGSA.Run.afterTicks_eq_tick_preTick',
    'AvailableChain.FGSA.Run.preIdx_le_afterTicksIdx',
    'AvailableChain.FGSA.Run.afterTicksIdx_mono',
    'AvailableChain.FGSA.Run.storeAt',
    'AvailableChain.FGSA.Run.S_at',
    'AvailableChain.FGSA.Run.F_at',
    'AvailableChain.FGSA.Run.J_at',
    'AvailableChain.FGSA.Run.gateIn',
    'AvailableChain.FGSA.Run.gateResult',
    'AvailableChain.FGSA.Run.isGateTime',
    'AvailableChain.FGSA.Run.IsGateTick',
    'AvailableChain.FGSA.Run.gateResultAt',
    'AvailableChain.FGSA.Run.gatePassedAt',
    'AvailableChain.FGSA.Run.fastAt',
    'AvailableChain.FGSA.Run.headAtIdx',
    'AvailableChain.FGSA.Run.vHead',
    'AvailableChain.FGSA.Run.actionSourceFG',
    'AvailableChain.FGSA.Run.actionSource',
    'AvailableChain.FGSA.Run.labelBoundAt',
    'AvailableChain.FGSA.Run.DeliveredAt',
    'AvailableChain.FGSA.Run.HandlesRowAt',
    'AvailableChain.FGSA.Run.AcceptsFinalBefore',
    'AvailableChain.FGSA.Run.cleanResults',
    'AvailableChain.FGSA.Run.BelowLabel',
    'AvailableChain.FGSA.Run.gateResult_eq_saved',
    'AvailableChain.FGSA.Run.isGateTime_iff',
    'AvailableChain.FGSA.Run.gateResultAt_eq_gateResult',
    'AvailableChain.FGSA.Run.vHead_eq_headAtIdx',
    'AvailableChain.FGSA.Run.actionSourceFG_eq_round',
    'AvailableChain.FGSA.Run.acceptsFinalBefore_of_idx',
    'AvailableChain.FGSA.Run.stable_afterTicks',
)
ORDER = ('Recurrence', 'Bounds', 'Reads', 'Counts', 'Regimes', 'Windows',
         'Packages.Safety', 'Packages.Outage', 'Channels', 'Witness',
         'ChannelProps', 'Healed', 'Packages.Finality', 'ComposeStmt', 'Fold',
         'Phases', 'PhasesInternal', 'Packages.Healing')
work = Path(tempfile.mkdtemp(prefix='fgsa-claims-check.', dir=ROOT / '.lake'))
print(f'FGSA claims audit logs: {work}', flush=True)
serial = 0

def run(label, args, *, expect=None, env=None, cwd=None):
    global serial
    serial += 1
    path = work / f'{serial:02d}-{label}.log'
    with path.open('w') as out:
        proc = subprocess.run(args, stdout=out, stderr=subprocess.STDOUT,
                              env=env, cwd=cwd)
    output = path.read_text()
    print(f'{label}: rc {proc.returncode} ({path.name})', flush=True)
    if expect is None:
        if proc.returncode:
            print(output)
            raise SystemExit(proc.returncode)
    elif proc.returncode == 0 or expect not in output:
        print(output)
        raise SystemExit(f'STOP: negative control {label} did not fail with {expect!r}')
    else:
        print(f'rejected, as expected: {label}', flush=True)
    return output

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
    if dep in LIBS or dep.endswith('.FGSAClaims'):
        return False
    if dep.startswith(('AvailableChainGridCO.Proofs.', 'AvailableChainKit.',
                       'AvailableChainStatements.')) or dep == 'AvailableChainModel.Generic.Run':
        return False
    if L.under(m, CLAIMS) and L.is_proof(ctx, dep):
        return False
    if L.under(m, INHABIT) and L.under(dep, PROOFS):
        return False
    if owned(dep):
        return True  # check (e) and order below apply to every internal edge
    common = ('AvailableChainEngineV2.', 'AvailableChainFGSA.Model.',
              'AvailableChainFGSA.Statements.', 'AvailableChainFGSARun.Model.',
              'AvailableChainFGSARun.Statements.', 'AvailableChainGeneric.Statements.',
              'AvailableChainSimplexFG.', 'Mathlib.', 'Init.', 'Lean.', 'Std.')
    exact = {'AvailableChainModel.Objects.Identifiers', 'AvailableChainModel.Objects.Time',
             'AvailableChainModel.Objects.Blocks', 'AvailableChainModel.Objects.Codec',
             'AvailableChainModel.Generic.Env', 'AvailableChainGridCO.Model.Protocol',
             'AvailableChainGridCO.Model.Walk', 'AvailableChainSA.Model.Protocol'}
    if dep.startswith(common) or dep in exact or dep in ctx.definitions:
        return True
    return not L.under(m, CLAIMS) and dep.startswith((
        'AvailableChainKitV2.', 'AvailableChainKitFG.', 'AvailableChainFGSA.Proofs.',
        'AvailableChainFGSARun.Proofs.', 'AvailableChainGeneric.Proofs.'))

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
        if dep == prefix + 'CleanInvariant' or dep.endswith('Internal'):
            lane = 'Clean' if dep.endswith('CleanInvariant') else 'Finality'
            if not m.startswith(PROOFS + '.Proofs.' + lane + '.'):
                findings.append(f'INTERNAL STATEMENT: {m} imports {dep}')
        if L.under(m, CLAIMS) and dep.startswith(PROOFS + '.Proofs.Clean.'):
            findings.append(f'CLEAN PROOF PATH: {m} imports {dep}')
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
run('layers', ['python3', 'scripts/check-layers.py'])

# Independent source controls use the same policy function as the real scan.
controls = (
    ('statements-non-def-theorem', CLAIMS + '.Statements.Reads',
     'def fgsaControl : Nat := 0\ntheorem fgsaControl_eq : fgsaControl = 0 := rfl\n', 'F-28'),
    ('plain-v2-open', CLAIMS + '.Statements.Reads', 'open AvailableChain.V2\n', 'V2 NAME CLASH'),
    ('grid-proof-import', PROOFS + '.Proofs.Shared.Reads', 'public import AvailableChainGridCO.Proofs.Map\n', 'IMPORT NOT ALLOWED'),
    ('rightward-statement', CLAIMS + '.Statements.Reads', 'public import ' + CLAIMS + '.Statements.Counts\n', 'MODULE ORDER'),
    ('clean-proof-path', CLAIMS + '.Statements.Reads', 'public import ' + PROOFS + '.Proofs.Clean.Step\n', 'CLEAN PROOF PATH'),
    ('claims-proof-import', CLAIMS + '.Claims.Clean', 'public import AvailableChainFGSARun.Proofs.ClientTrace\n', 'IMPORT NOT ALLOWED'),
    ('facade-tests', CLAIMS, 'public import ' + CLAIMS + '.Tests.Axioms\n', 'B7-TESTS'),
    ('cross-lane-proof', PROOFS + '.Proofs.Clean.Step', 'public import ' + PROOFS + '.Proofs.Outage.Step\n', 'LANE'),
    ('cross-lane-export', PROOFS + '.Proofs.Clean.Step', 'public import ' + PROOFS + '.Proofs.Outage.Export\n', 'EXPORT-USE'),
    ('shared-lane-proof', PROOFS + '.Proofs.Shared.Reads', 'public import ' + PROOFS + '.Proofs.Clean.Step\n', 'SHARED'),
)
for label, m, body, expected in controls:
    hits = source_findings(m, 'module\n' + body)
    if not any(expected in f for f in hits):
        raise SystemExit(f'STOP: negative control passed: {label}: {hits}')
    print(f'{label}: rc 1, rejected as expected ({expected})', flush=True)

# The seven home equation theorems must pass the same source policy.
reads_path = Path(CLAIMS + '/Statements/Reads.lean')
positive_hits = source_findings(module(reads_path), reads_path.read_text())
if positive_hits:
    raise SystemExit(f'STOP: Statements _def positive case failed: {positive_hits}')
print('statements-home-def-theorems: rc 0 (seven matching _def theorems)', flush=True)

for lib in LIBS:
    run('build-' + lib, ['lake', 'build', '--wfail', lib])
    run('build-' + lib + 'Tests', ['lake', 'build', '--wfail', lib + 'Tests'])
run('support', ['lake', 'build', 'AvailableChainCheckSupport'])

# Derive a compiled-edge table only AFTER source policy validation. A built
# module may not contain an edge absent from its checked source. This also
# rejects stale .oleans. Every source module is imported as an audit root;
# root-facade coverage is checked separately below.
edges = [(module(p), L.read_header(p.read_text())[0]) for p in files]
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
source = source.replace('let mut dir : System.FilePath := "AvailableChainFGSARun"', 'let mut dir : System.FilePath := ""')
source = source.replace('(#[lib] ++ extra)', '(libs.toArray ++ extra)')
source = source.replace('  for m in ← sourceModules dir do',
    '  let dirs := if dir.toString.isEmpty then libs.map (fun n => System.FilePath.mk n.toString) else [dir]\n' +
    '  let mut sourceMods := #[]\n  for d in dirs do sourceMods := sourceMods ++ (← sourceModules d)\n' +
    '  for m in sourceMods do')
source = source.replace('  if cs.isEmpty then\n    IO.eprintln "NO CONSTANTS FOUND"\n    return 2\n',
    '  -- Empty libraries are valid only with successful source/build coverage.\n')
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
for m in roots:
    args += ['--root', m]
if EXPECTED:
    args += ['--expect', *EXPECTED]
run('axioms-coverage-used-constants', args)
run('lease', ['lake', 'env', 'lean', '--run', str(lease_file), *roots])

# Every production module must be in its root facade's transitive closure.
# Importing all modules for the audit above cannot mask a missing facade edge.
for lib in LIBS:
    seen = set()
    pending = [lib]
    imports = dict(edges)
    while pending:
        m = pending.pop()
        if m in seen:
            continue
        seen.add(m)
        pending.extend(imports.get(m, ()))
    missing = [m for m in roots if L.under(m, lib) and not L.is_test(m) and m not in seen]
    if missing:
        raise SystemExit('NOT IMPORTED BY ROOT: ' + ', '.join(missing))
run('proof-eqns', ['lake', 'env', 'lean', '--run', 'scripts/CheckProofEqns.lean',
                   '--baseline', 'scripts/baselines/check-proof-eqns.txt'])
run('unused-imports', ['bash', 'scripts/shake-report.sh', '--fail-on-new', *roots])

# Compiled negative controls. They are never added to the real library.
# Use the real auditor and require its diagnostic, not merely a Lean error.
neg = work / 'controls'
neg.mkdir()
# Lean resolves an entire module prefix at the first search-path entry.
# Copy the built roots too, as the current T7 negative controls do.
for lib in LIBS:
    built = ROOT / '.lake/build/lib/lean'
    shutil.copytree(built / lib, neg / lib)
    for p in built.glob(lib + '.*'):
        if p.is_file():
            shutil.copy2(p, neg / p.name)

def write_module(name, text):
    p = neg / (name.replace('.', '/') + '.lean')
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)
    return p

def compile_module(name, text):
    p = write_module(name, text)
    run('compile-' + name.split('.')[-1], ['lake', 'env', 'bash', '-c',
        'LEAN_PATH="$1:$LEAN_PATH" lean -o "$2" "$3"', 'fgsa-claims', str(neg),
        str(p.with_suffix('.olean')), str(p)])
    return p

bad = PROOFS + '.Proofs.Shared.NegUse'
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
run('grid-constant-in-statement', ['lake', 'env', 'bash', '-c',
    'LEAN_PATH="$1:$LEAN_PATH" lean --run "$2" --root "$3"', 'fgsa-claims', str(neg),
    str(audit), bad], expect='FORBIDDEN CONSTANT: AvailableChain.FGSA.Run.negGridStatement uses AvailableChain.GridCO.ComparableTargets')
# The controls have the same FG-SA namespace and upstream reachability as T7.
lease_bad = PROOFS + '.Proofs.Shared.NegLease'
compile_module(lease_bad, '''module
public import AvailableChainFGSA.Model.Clock
public section
namespace AvailableChain.FGSA.Run
def negLease (p : AvailableChain.GridCO.Params) (st : AvailableChain.GridCO.State 1) :
    AvailableChain.GridCO.State 1 := AvailableChain.GridCO.gate p st 0
end AvailableChain.FGSA.Run
end
''')
run('default-lease', ['lake', 'env', 'bash', '-c',
    'LEAN_PATH="$1:$LEAN_PATH" lean --run "$2" "$3"', 'fgsa-claims', str(neg),
    str(lease_file), lease_bad], expect='BAD LEASE INSTANCE')

# A tiny offline Lake package lets shake read its own build traces. It imports
# only Lean core, has no dependencies and never invokes lake update.
(neg / 'lean-toolchain').write_text(Path('lean-toolchain').read_text())
(neg / 'lakefile.toml').write_text('name = "fgsa-controls"\n[[lean_lib]]\nname = "FGSAControl"\nglobs = ["FGSAControl.+"]\n')
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
control_lib = neg / '.lake/build/lib/lean'
run('simp-without-f-def', ['lake', 'env', 'bash', '-c',
    'LEAN_PATH="$1:$LEAN_PATH" lean --run scripts/CheckProofEqns.lean --baseline scripts/baselines/check-proof-eqns.txt FGSAControl.Proofs.NegEq',
    'fgsa-claims', str(control_lib)], expect='EQ EXPORT FGSAControl.Proofs.NegEq')
# Use the same --fail-on-new baseline comparison as the real D47 scan.
# shake-report reads its package from cwd only via its cd, so obtain Lake's
# raw report here, then apply the same removal key and frozen baseline.
out = run('unused-import-control', ['lake', 'shake', 'FGSAControl.NegUnused'],
          cwd=neg, expect='remove #[public import Init.Data.List.Sort]')
key = 'remove FGSAControl/NegUnused.lean public import Init.Data.List.Sort'
if C.read_baseline('shake-report')[key]:
    raise SystemExit('STOP: unused-import control is in the baseline')
print('unused-import baseline comparison: rc 1 (NEW removal), rejected as expected', flush=True)
print('all FGSA claims checks pass', flush=True)
PY
