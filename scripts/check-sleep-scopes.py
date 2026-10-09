#!/usr/bin/env python3
"""Keep active compiled roots separate from deferred PC-SA source checks."""
from pathlib import Path
import re

import check_common as C

DEFERRED = ('AvailableChainPCSA', 'AvailableChainPCSARun',
            'AvailableChainPCSAClaims', 'AvailableChainPCSAProofs')


def deferred(module):
    return any(module == p or module.startswith(p + '.') for p in DEFERRED)


def check_active(graph, roots):
    for root in roots:
        seen, pending = set(), [root]
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            pending.extend(graph.get(module, ()))
        bad = {m for m in seen if deferred(m)}
        if bad:
            raise ValueError('ACTIVE IMPORTS PC-SA: ' + root + ' -> ' +
                             ', '.join(sorted(bad)))


def check_deferred(module, text):
    clean = C.strip(text)
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b', clean):
        raise ValueError('DEFERRED FORBIDDEN PROOF: ' + module)
    if module == 'AvailableChainPCSAProofs.Proofs.Shared.FGCompose' and re.search(
            r'@\[|\b(instance|notation|infix[lr]?|prefix|postfix|macro|syntax|attribute|'
            r'initialize|register_option|elab|builtin_initialize|declare_syntax_cat|export|alias|'
            r'register_simp_attr|declare_aesop_rule_sets)\b', clean):
        raise ValueError('DEFERRED GLOBAL EXTENSION: ' + module)


def main():
    graph = C.import_graph()
    active = [m for m in graph if not deferred(m)]
    check_active(graph, active)
    files = [f for f in C.library_files() if deferred(f.module)]
    for file in files:
        check_deferred(file.module, Path(file.path).read_text())
    if not files:
        raise ValueError('MISSING DEFERRED PC-SA SOURCE')
    print(f'Sleep source scopes: {len(active)} active; '
          f'{len(files)} deferred PC-SA modules: PASS')


if __name__ == '__main__':
    main()
