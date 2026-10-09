#!/usr/bin/env python3
"""Compare the FGCompose source names without compiled family imports."""
from pathlib import Path
import re
import sys
sys.path.insert(0, 'scripts')
import check_common as C
from check_inventory import read_names

expected = set(read_names('scripts/fg-compose-expected.txt'))
found = set()
files = [lf for lf in C.library_files() if lf.lib == 'AvailableChainFGCompose']
if not files or not Path('AvailableChainFGCompose.lean').is_file():
    raise SystemExit('MISSING COMPOSE SOURCE SCOPE')
for lf in files:
    raw = C.strip(Path(lf.path).read_text())
    # Statements expose their definitions. No other extension is permitted.
    if '.Statements.' in lf.module:
        raw = raw.replace('@[expose] public section', '')
    if re.search(r'@\[|\b(instance|notation|infix[lr]?|prefix|postfix|macro|syntax|attribute|'
                 r'initialize|register_option|elab|builtin_initialize|'
                 r'declare_syntax_cat|export|alias|'
                 r'register_simp_attr|declare_aesop_rule_sets)\b', raw):
        raise SystemExit('FORBIDDEN GLOBAL EXTENSION: ' + lf.module)
    if '.Statements.' in lf.module or '.Proofs.' in lf.module:
        for d in C.declarations(lf):
            if d.kind in ('def', 'abbrev', 'theorem', 'lemma', 'structure', 'inductive',
                          'opaque', 'irreducible_def'):
                if not d.private:
                    found.add(d.full)
        for name, body in re.findall(
                r'^structure (\w+).*?where\n(.*?)(?=^(?:variable|structure|def|theorem)|\Z)',
                raw, re.M | re.S):
            for field in re.findall(r'^  (\w+) :', body, re.M):
                found.add('AvailableChain.FGCompose.' + name + '.' + field)
for path in (Path('AvailableChainFGSAProofs/Proofs/Shared/FGCompose.lean'),):
    if path.exists():
        raw = C.strip(path.read_text())
        if re.search(r'@\[|\b(instance|notation|infix[lr]?|prefix|postfix|macro|syntax|attribute|'
                     r'initialize|register_option|elab|builtin_initialize|'
                 r'declare_syntax_cat|export|alias|'
                 r'register_simp_attr|declare_aesop_rule_sets)\b', raw):
            raise SystemExit('FORBIDDEN GLOBAL EXTENSION: ' + str(path))
if found != expected:
    print('COMPOSE INVENTORY MISSING:', sorted(expected - found))
    print('COMPOSE INVENTORY UNLISTED:', sorted(found - expected))
    raise SystemExit(2)
print(f'Compose source coverage: {len(files)} modules; '
      f'{len(expected)} public declarations/projections')
