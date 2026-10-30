#!/usr/bin/env python3
"""Check the verifier's source-layout and ordinary-import closure constraints.

This is a filesystem audit. Remote Git tree mode and exact-commit checks remain
the publisher's responsibility. A successful audit is not a Lean proof check.
"""
import argparse
import hashlib
import json
import re
import stat
from pathlib import Path

NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z')
EXTERNAL_ROOTS = {'Mathlib','Init','Lean','Std','Batteries','Qq','Aesop',
                  'ProofWidgets','Plausible','ImportGraph','LeanSearchClient'}
STATEMENT_SHA = '9ba7370f1256ef680ccf674e653b5456735c478f9ac80fcffc90f130ac4a2ce6'


def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            out.append('  ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            out.append('  ')
            i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    if depth:
        raise ValueError('Unclosed block comment')
    return ''.join(out)


def headers(path):
    imports, modular = [], False
    for line in strip_comments(path.read_text()).splitlines():
        text = line.strip()
        if text == 'module':
            modular = True
            continue
        if not text or text == 'prelude':
            continue
        match = re.fullmatch(r'(?:(?:public|private|meta)\s+)*import\s+(.+)', text)
        if not match:
            break
        names = match[1].split()
        if not names or any(not NAME.fullmatch(n) for n in names):
            raise ValueError(f'Unsupported import header: {path}: {text}')
        imports += names
    return imports, modular


def audit(root):
    paths = [root/'Submission.lean'] + sorted((root/'Submission').rglob('*.lean'))
    errors, hashes, total, largest = [], {}, 0, (0, '')
    for path in paths:
        info = path.lstat()
        relative = path.relative_to(root)
        module = '.'.join(relative.with_suffix('').parts)
        if not stat.S_ISREG(info.st_mode) or info.st_mode & 0o111 or not NAME.fullmatch(module):
            errors.append(f'Invalid regular-file mode or module path: {relative}')
        if info.st_size > 20_000_000:
            errors.append(f'File exceeds 20 MB: {relative}')
        total += info.st_size
        largest = max(largest, (info.st_size, str(relative)))
        hashes[str(relative)] = hashlib.sha256(path.read_bytes()).hexdigest()
    if total > 150_000_000:
        errors.append('Combined Lean source exceeds 150 MB')
    if hashes['Submission/CatalanStatement.lean'] != STATEMENT_SHA:
        errors.append('Canonical statement hash mismatch')

    done, visiting, external, missing = set(), set(), set(), set()
    edges, kinds, order = {}, {}, []
    def visit(module):
        if module in visiting:
            raise ValueError(f'Import cycle at {module}')
        if module in done:
            return
        path = root/(module.replace('.', '/')+'.lean')
        if not path.is_file():
            (missing if module.startswith('Submission.') else external).add(module)
            return
        visiting.add(module)
        imports, kind = headers(path)
        edges[module], kinds[module] = imports, kind
        for imported in imports:
            if imported.startswith(('VerifierChallenge','VerifierAudit')):
                errors.append(f'Reserved import in {module}: {imported}')
            visit(imported)
        visiting.remove(module)
        done.add(module)
        order.append(module)
    visit('Submission')
    for imported in sorted(missing):
        errors.append(f'Missing local import: {imported}')
    for module, imports in edges.items():
        if kinds[module]:
            for imported in imports:
                if imported in kinds and not kinds[imported]:
                    errors.append(f'Module imports old-style file: {module} -> {imported}')
    for prefix in sorted({m.split('.')[0] for m in external} - EXTERNAL_ROOTS):
        errors.append(f'Unrecognized external source root: {prefix}')
    all_modules = {'.'.join(p.relative_to(root).with_suffix('').parts) for p in paths}
    return {
        'status': 'passed' if not errors else 'incomplete_or_failed',
        'errors': errors,
        'root': 'Submission',
        'sources': len(paths),
        'total_bytes': total,
        'largest_source': {'path': largest[1], 'bytes': largest[0]},
        'reachable_local_modules': len(done),
        'unimported_local_modules': len(all_modules-done),
        'canonical_statement_sha256': hashes['Submission/CatalanStatement.lean'],
        'reachable_topological_order': order,
        'unimported_modules': sorted(all_modules-done),
        'source_sha256': hashes,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = audit(args.root)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()
                     if k not in {'reachable_topological_order','unimported_modules',
                                  'source_sha256','canonical_statement_sha256'}}, indent=2))
    raise SystemExit(bool(result['errors']))
