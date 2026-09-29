#!/usr/bin/env python3
"""Check (i), BUILD §7.3: the GLY §F rules whose enforcement is a grep or a
mechanical scan (GLY r3.13 §F; step-2 rulings D08 as corrected, D13).
The driver is scripts/check-gly-rules.sh.

Each rule has its own baseline scripts/baselines/check-gly-rules-<rule>.txt.
A FAIL rule fails on a finding in a new library (scripts/new-libraries.txt)
and on a legacy finding that its baseline does not list. A REVIEW rule
("review list" / "review the output" in GLY §F) lists its findings and
never fails; its baseline separates the reviewed ones. F-13 (duplicate
short names) is baselined in new libraries too (step-2 ruling D07).
scripts/gly-rules-allow.txt: `<rule> <declaration>` lines that a rule
skips (the F-3 E-13 wrapper allow list; empty now).

Rules (GLY §F row → what this script checks):
  F-1  REVIEW  structures (and classes) whose field-name sets coincide.
  F-3  FAIL    a premise of a theorem in Generic, KitFG or an FGSA library
               names RootInjectiveBelow, ViewRootInj, RootInjectiveOn or
               ContentAgree.
  F-4  FAIL    the import closure of a Generic Pure module
               (Statements.Pure.*, Proofs.Pure.*) holds only Model.Objects.*,
               Generic Pure modules and GridCO.Model.Walk (plus non-project
               modules: Mathlib, …).
  F-5  REVIEW  Block.genesis (or `.genesis`) in the statement of a theorem
               in a Walk, Votes or Lease module.
  F-6  FAIL    `slowLeasePolicy` in Generic.
  F-7  FAIL    zero rename: a declaration of GridCO, SimplexFG or KitFG at
               the base commit (GLY_BASE, default 7ac5b0c) is missing now.
  F-10 FAIL    git guard: no change under AvailableChainKit/ (v1 Kit) since
               the base commit.
  F-12 FAIL    the closure of Generic Statements.Pure (not Walk) holds only
               Model.Objects.* and Statements.Pure (not Walk); the closure of
               Statements.V2 also holds Statements.V2 and the closures of
               EngineV2.{Engine,Conditions,Laws}.* and KitV2.ClockLaws.
  F-13 FAIL    a theorem short name in more than one library (baseline =
               allow list); a `private theorem` in Generic.
  F-14 REVIEW  a theorem outside Generic with a PartialSynchrony or
               HealthyPrefixDelivery premise and a handles/processed
               conclusion.
  F-15 FAIL    `…` in a Generic Statements module (outside comments).
  F-18 REVIEW  a window definition (name contains "window") outside the
               Schedule and Recurrence modules.
  F-20 FAIL    a declaration name with suffix _of_pins, _closed or _landed
               in Generic or an FGSA library.
  F-21 FAIL    plan vocabulary in a declaration name: a component token
               T<n>, I<n>, W<n>, V<3-9>, GF<n>, G_F<n> or F<n><letter>.
  F-23 FAIL    a premise of a theorem in Generic, KitFG or
               FGSAProofs …Shared… names CleanCut₂, Outage₂, Recovery₂,
               HealthyPrefix₂, HealingInput, a …Set or a …Contract type.
  F-24 FAIL    a theorem whose conclusion is FaultX and whose name does not
               contain count_rec.
  F-25 REVIEW  a Keep/Frame theorem with `∩` in its conclusion.
  F-26 FAIL    HealingInput in FGSAClaims Statements/Phases (PhasesInternal
               exempt).
  F-28 FAIL    a theorem in a Statements module (a `.Statements.` module or a
               KitFG definition module) whose name does not end in `_def`.
  F-30 FAIL    a Generic declaration in namespace AvailableChain.Generic; a
               GridCO.Proofs module in the closure of a Generic module.

Usage: python3 scripts/check-gly-rules.py [--rule F-n]... [--list-legacy]
[--write-baseline]. Exit 0: no failing finding; 1: a failing finding;
2: an input error (for example, the base commit cannot be read)."""
import argparse
import os
import re
import subprocess
import sys
from collections import defaultdict

sys.dont_write_bytecode = True
import check_common as C  # noqa: E402

GEN = {'AvailableChainGeneric'}
FGSA_ALL = {'AvailableChainFGSA', 'AvailableChainFGSARun', 'AvailableChainFGSAClaims',
            'AvailableChainFGSAProofs', 'AvailableChainFGSAInhabit'}
KITFG = {'AvailableChainKitFG'}
BASE = os.environ.get('GLY_BASE', '7ac5b0c')
ALLOW = os.path.join(C.SCRIPTS, 'gly-rules-allow.txt')
KITFG_DEF = os.path.join(C.BASELINES, 'kitfg-def-modules.txt')
THM = ('theorem', 'lemma')


def tok(names):
    """A regex for these identifiers as a whole name or a last component."""
    return re.compile(r'(?<![\w.₀-₉])(?:[\w₀-₉]+\.)*(' + '|'.join(names) + r')(?![\w₀-₉])')


def has_prefix(module, prefixes):
    return any(module == p or module.startswith(p + '.') for p in prefixes)


def read_allow():
    out = set()
    if os.path.exists(ALLOW):
        for line in open(ALLOW, encoding='utf-8'):
            line = line.split('#', 1)[0].split()
            if len(line) == 2:
                out.add(tuple(line))
    return out


def kitfg_def_modules():
    mods = set()
    if os.path.exists(KITFG_DEF):
        for line in open(KITFG_DEF, encoding='utf-8'):
            x = line.split('#', 1)[0].strip()
            if x:
                x = x[:-5].replace('/', '.') if x.endswith('.lean') else x
                mods.add(x if x.startswith('AvailableChainKitFG') else 'AvailableChainKitFG.' + x)
    return mods


class Ctx:
    def __init__(self):
        self.scope = C.Scope()
        self.files = C.library_files()
        self.decls = {lf.path: C.declarations(lf) for lf in self.files}
        self.graph = C.import_graph(self.files)
        self.allow = read_allow()

    def new(self, lf):
        return self.scope.is_new_file(lf)

    def all_decls(self, libs=None):
        for lf in self.files:
            if libs is None or lf.lib in libs:
                for d in self.decls[lf.path]:
                    yield lf, d


def F(rule, key, msg, lf=None, new=None, review=False, **kw):
    return C.Finding(f'{rule} {key}', f'{rule}: {msg}', new=bool(new), review=review, **kw)


# ---------------------------------------------------------------------------
# Rules. Each returns a list of findings.

FIELD = re.compile(r'^\(?\s*([^\s:({\[⦃]+(?:\s+[^\s:({\[⦃]+)*)\s*(?::|\(|\{|\[|⦃)')


def struct_fields(d):
    t = d.text()
    m = re.search(r'\bwhere\b', t)
    if not m:
        return None
    lines = t[m.end():].split('\n')[1:]
    indent, fields = None, []
    for line in lines:
        if not line.strip():
            continue
        ind = len(line) - len(line.lstrip())
        if ind == 0:
            break
        if indent is None:
            indent = ind
        if ind != indent:
            continue
        s = line.strip()
        if re.match(r'^[\w₀-₉\']+\s*::', s):      # constructor name
            continue
        fm = FIELD.match(s)
        if fm:
            fields.extend(fm.group(1).split())
    return frozenset(fields) if fields else None


def rule_f1(x):
    groups = defaultdict(list)
    for lf, d in x.all_decls():
        if d.kind in ('structure', 'class'):
            fs = struct_fields(d)
            if fs:
                groups[fs].append((lf, d))
    out = []
    for fs, members in groups.items():
        if len(members) > 1:
            names = sorted(d.full for _, d in members)
            out.append(F('F-1', f'{",".join(sorted(fs))} :: {" ".join(names)}',
                         f'structures with the field set {{{", ".join(sorted(fs))}}}: {", ".join(names)}',
                         new=any(x.new(lf) for lf, _ in members), review=True))
    return out


ROOT_PREMISES = tok(['RootInjectiveBelow', 'ViewRootInj', 'RootInjectiveOn', 'ContentAgree'])


def rule_f3(x):
    out = []
    for lf, d in x.all_decls(GEN | KITFG | FGSA_ALL):
        if d.kind not in THM or ('F-3', d.full) in x.allow:
            continue
        prem, _ = d.premises_and_conclusion()
        for name in sorted({m.group(1) for m in ROOT_PREMISES.finditer(prem)}):
            out.append(F('F-3', f'{lf.module} {d.full} {name}',
                         f'{lf.path}:{d.line}: {d.full} takes a {name} premise', new=x.new(lf)))
    return out


def closure_rule(x, rule, starts, allowed):
    """Findings for each local module in the closure of each start module
    that `allowed(module)` rejects."""
    out = []
    by_mod = {lf.module: lf for lf in x.files}
    for m in sorted(starts):
        lf = by_mod[m]
        for bad in sorted(t for t in C.closure(x.graph, m) if t in by_mod and not allowed(t)):
            out.append(F(rule, f'{m} {bad}', f'{lf.path}: the import closure holds {bad}', new=x.new(lf)))
    return out


GEN_S_PURE = 'AvailableChainGeneric.Statements.Pure'
GEN_P_PURE = 'AvailableChainGeneric.Proofs.Pure'
GEN_S_V2 = 'AvailableChainGeneric.Statements.V2'
GEN_S_WALK = GEN_S_PURE + '.Walk'


def rule_f4(x):
    starts = [lf.module for lf in x.files if has_prefix(lf.module, [GEN_S_PURE, GEN_P_PURE])]
    ok = lambda t: has_prefix(t, ['AvailableChainModel.Objects', GEN_S_PURE, GEN_P_PURE,
                                  'AvailableChainGridCO.Model.Walk'])
    return closure_rule(x, 'F-4', starts, ok)


def rule_f5(x):
    out = []
    pat = re.compile(r'(?<![\w₀-₉])(?:Block)?\.genesis(?![\w₀-₉])')
    for lf, d in x.all_decls():
        if d.kind in THM and re.search(r'(Walk|Votes|Lease)', lf.module.rsplit('.', 1)[-1]):
            if pat.search(d.signature()):
                out.append(F('F-5', f'{lf.module} {d.full}',
                             f'{lf.path}:{d.line}: {d.full}: Block.genesis in the statement',
                             new=x.new(lf), review=True))
    return out


def grep_rule(x, rule, libs, pattern, what, module_filter=lambda m: True):
    out = []
    for lf in x.files:
        if lf.lib in libs and module_filter(lf.module):
            for m in pattern.finditer(lf.stripped):
                out.append(F(rule, f'{lf.module}', f'{lf.path}:{C.line_of(lf.stripped, m.start())}: {what}',
                             new=x.new(lf)))
    return out


def rule_f6(x):
    return grep_rule(x, 'F-6', GEN, tok(['slowLeasePolicy']), 'slowLeasePolicy in Generic')


def git(*args):
    r = subprocess.run(['git', '-C', C.ROOT] + list(args), capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f'git {" ".join(args)}: {r.stderr.strip()}')
    return r.stdout


def lib_paths(lib):
    return [lib + '.lean', lib + '/']


def rule_f7(x):
    libs = ['AvailableChainGridCO', 'AvailableChainSimplexFG', 'AvailableChainKitFG']
    out = []
    now = defaultdict(set)
    for lf, d in x.all_decls(set(libs)):
        if d.name:
            now[lf.lib].add(d.full)
    for lib in libs:
        paths = [p for p in git('ls-tree', '-r', '--name-only', BASE, '--', *lib_paths(lib)).split('\n')
                 if p.lower().endswith('.lean')]
        before = {}
        for p in paths:
            lf = C.LeanFile(lib, p, p[:-5].replace('/', '.'))
            lf._raw = git('show', f'{BASE}:{p}')
            for d in C.declarations(lf):
                if d.name:
                    before.setdefault(d.full, p)
        for name in sorted(set(before) - now[lib]):
            out.append(F('F-7', f'{lib} {name}',
                         f'{name} ({before[name]} at {BASE}) is no longer declared in {lib}'))
    return out


def rule_f10(x):
    paths = lib_paths('AvailableChainKit')
    changed = set(git('diff', '--name-only', BASE, '--', *paths).split())
    changed |= set(git('ls-files', '--others', '--exclude-standard', '--', *paths).split())
    return [F('F-10', p, f'{p} changed since {BASE} (v1 Kit is closed)') for p in sorted(changed)]


def rule_f12(x):
    by_mod = {lf.module for lf in x.files}
    pure = [m for m in by_mod if has_prefix(m, [GEN_S_PURE]) and not has_prefix(m, [GEN_S_WALK])]
    v2 = [m for m in by_mod if has_prefix(m, [GEN_S_V2])]
    pure_ok = lambda t: has_prefix(t, ['AvailableChainModel.Objects', GEN_S_PURE]) and not has_prefix(t, [GEN_S_WALK])
    roots = [m for m in by_mod if has_prefix(m, ['AvailableChainEngineV2.Engine', 'AvailableChainEngineV2.Conditions',
                                                 'AvailableChainEngineV2.Laws', 'AvailableChainKitV2.ClockLaws'])]
    v2_allowed = set(roots)
    for r in roots:
        v2_allowed |= C.closure(x.graph, r)
    v2_ok = lambda t: pure_ok(t) or has_prefix(t, [GEN_S_V2]) or t in v2_allowed
    return closure_rule(x, 'F-12', pure, pure_ok) + closure_rule(x, 'F-12', v2, v2_ok)


def rule_f13(x):
    libs_of = defaultdict(set)
    where = defaultdict(list)
    for lf, d in x.all_decls():
        if d.kind in THM and d.name:
            libs_of[d.short].add(lf.lib)
            where[d.short].append((lf, d))
    out = []
    for short, libs in sorted(libs_of.items()):
        if len(libs) > 1:
            locs = ', '.join(f'{lf.path}:{d.line}' for lf, d in where[short])
            out.append(F('F-13', f'dup {short} {" ".join(sorted(libs))}',
                         f'theorem short name {short} in {len(libs)} libraries: {locs}',
                         new=any(x.new(lf) for lf, _ in where[short]), baselinable_in_new=True))
    for lf, d in x.all_decls(GEN):
        if d.kind in THM and d.private:
            out.append(F('F-13', f'private {lf.module} {d.full}',
                         f'{lf.path}:{d.line}: private theorem {d.full} in Generic', new=x.new(lf)))
    return out


def rule_f14(x):
    out = []
    p = tok(['PartialSynchrony', 'HealthyPrefixDelivery'])
    c = tok(['handles', 'processed'])
    for lf, d in x.all_decls():
        if lf.lib in GEN or d.kind not in THM:
            continue
        prem, concl = d.premises_and_conclusion()
        if p.search(prem) and c.search(concl):
            out.append(F('F-14', f'{lf.module} {d.full}',
                         f'{lf.path}:{d.line}: {d.full}: PartialSynchrony/HealthyPrefixDelivery premise, '
                         f'handles/processed conclusion', new=x.new(lf), review=True))
    return out


def rule_f15(x):
    return grep_rule(x, 'F-15', GEN, re.compile('…'), '`…` in a Generic Statements module',
                     lambda m: '.Statements.' in m + '.')


def rule_f18(x):
    out = []
    for lf, d in x.all_decls():
        if d.kind in ('def', 'abbrev', 'structure', 'inductive') and 'window' in d.short.lower() \
                and not re.search(r'Schedule|Recurrence', lf.module):
            out.append(F('F-18', f'{lf.module} {d.full}', f'{lf.path}:{d.line}: window definition {d.full}',
                         new=x.new(lf), review=True))
    return out


def rule_f20(x):
    out = []
    for lf, d in x.all_decls(GEN | FGSA_ALL):
        if re.search(r'_(of_pins|closed|landed)$', d.short):
            out.append(F('F-20', f'{lf.module} {d.full}', f'{lf.path}:{d.line}: staged name {d.full}',
                         new=x.new(lf)))
    return out


PLAN = re.compile(r'(?:^|(?<=[_.])|(?<=[a-z]))(T\d+|I\d+|W\d+|V[3-9]\d*|G_?F\d+[a-z]?|F\d+[a-z])(?=$|[_.A-Z])')


def rule_f21(x):
    out = []
    for lf, d in x.all_decls():
        if not d.name:
            continue
        toks = [m.group(1) for comp in d.name.split('.') for m in PLAN.finditer(comp)]
        if toks:
            out.append(F('F-21', f'{lf.module} {d.full}',
                         f'{lf.path}:{d.line}: plan vocabulary {",".join(toks)} in {d.full}', new=x.new(lf)))
    return out


REGIME = re.compile(r'(?<![\w.₀-₉])(?:[\w₀-₉]+\.)*(CleanCut₂|Outage₂|Recovery₂|HealthyPrefix₂|HealingInput|'
                    r'[\w₀-₉]+Set|[\w₀-₉]*Contract)(?![\w₀-₉])')


def rule_f23(x):
    out = []
    for lf, d in x.all_decls():
        if d.kind not in THM:
            continue
        if not (lf.lib in GEN | KITFG or (lf.lib == 'AvailableChainFGSAProofs' and '.Shared.' in lf.module + '.')):
            continue
        prem, _ = d.premises_and_conclusion()
        for name in sorted({m.group(1) for m in REGIME.finditer(prem)}):
            out.append(F('F-23', f'{lf.module} {d.full} {name}',
                         f'{lf.path}:{d.line}: {d.full} takes a {name} premise (a regime bundle)', new=x.new(lf)))
    return out


def rule_f24(x):
    out = []
    for lf, d in x.all_decls():
        if d.kind not in THM:
            continue
        _, concl = d.premises_and_conclusion()
        m = re.match(r'[\s(]*([\w.₀-₉]+)', concl)
        if m and m.group(1).rsplit('.', 1)[-1] == 'FaultX' and 'count_rec' not in d.short:
            out.append(F('F-24', f'{lf.module} {d.full}', f'{lf.path}:{d.line}: {d.full} concludes FaultX',
                         new=x.new(lf)))
    return out


def rule_f25(x):
    out = []
    for lf, d in x.all_decls():
        if d.kind in THM and re.search(r'keep|frame', d.short, re.I):
            if '∩' in d.premises_and_conclusion()[1]:
                out.append(F('F-25', f'{lf.module} {d.full}', f'{lf.path}:{d.line}: {d.full}: `∩` in the conclusion',
                             new=x.new(lf), review=True))
    return out


def rule_f26(x):
    return grep_rule(x, 'F-26', {'AvailableChainFGSAClaims'}, tok(['HealingInput']),
                     'HealingInput in Statements/Phases',
                     lambda m: has_prefix(m, ['AvailableChainFGSAClaims.Statements.Phases']))


def rule_f28(x):
    defs = kitfg_def_modules()
    out = []
    for lf, d in x.all_decls():
        if d.kind in THM and ('.Statements.' in lf.module + '.' or lf.module in defs) \
                and not d.short.endswith('_def'):
            out.append(F('F-28', f'{lf.module} {d.full}', f'{lf.path}:{d.line}: theorem {d.full} in a Statements module',
                         new=x.new(lf)))
    return out


def rule_f30(x):
    out = []
    ns = re.compile(r'^\s*namespace\s+AvailableChain\.Generic(\.|\s|$)', re.M)
    for lf in x.files:
        if lf.lib in GEN:
            for m in ns.finditer(lf.stripped):
                out.append(F('F-30', f'namespace {lf.module}',
                             f'{lf.path}:{C.line_of(lf.stripped, m.start())}: namespace AvailableChain.Generic',
                             new=True))
    for lf, d in x.all_decls(GEN):
        if d.full.startswith('AvailableChain.Generic.'):
            out.append(F('F-30', f'decl {lf.module} {d.full}', f'{lf.path}:{d.line}: {d.full} in AvailableChain.Generic',
                         new=True))
    starts = [lf.module for lf in x.files if lf.lib in GEN]
    out += closure_rule(x, 'F-30', starts, lambda t: not has_prefix(t, ['AvailableChainGridCO.Proofs']))
    return out


RULES = {'F-1': rule_f1, 'F-3': rule_f3, 'F-4': rule_f4, 'F-5': rule_f5, 'F-6': rule_f6,
         'F-7': rule_f7, 'F-10': rule_f10, 'F-12': rule_f12, 'F-13': rule_f13, 'F-14': rule_f14,
         'F-15': rule_f15, 'F-18': rule_f18, 'F-20': rule_f20, 'F-21': rule_f21, 'F-23': rule_f23,
         'F-24': rule_f24, 'F-25': rule_f25, 'F-26': rule_f26, 'F-28': rule_f28, 'F-30': rule_f30}


def main():
    ap = C.standard_args(argparse.ArgumentParser(description=__doc__.split('\n')[0]))
    ap.add_argument('--rule', action='append', choices=list(RULES), help='run only this rule')
    a = ap.parse_args()
    x = Ctx()
    fails, errors = 0, 0
    for rule in a.rule or RULES:
        name = f'check-gly-rules-{rule}'
        try:
            findings = RULES[rule](x)
        except RuntimeError as e:
            print(f'{rule}: ERROR: {e}')
            errors += 1
            continue
        if a.write_baseline:
            n = C.write_baseline(name, findings, [
                f'check (i) check-gly-rules, GLY §F rule {rule}: legacy findings.',
                f'Generated by: python3 scripts/check-gly-rules.py --rule {rule} --write-baseline'])
            print(f'{rule}: wrote {n} baseline entries')
            continue
        fails += C.evaluate(name, findings, a.list_legacy, title=rule)
    if a.write_baseline:
        return 2 if errors else 0
    print(f'check-gly-rules: {"FAIL" if fails or errors else "PASS"}: {fails} failing findings, '
          f'{errors} rule errors, {len(a.rule or RULES)} rules')
    return 2 if errors else (1 if fails else 0)


if __name__ == '__main__':
    sys.exit(main())
