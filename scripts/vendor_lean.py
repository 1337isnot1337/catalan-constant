#!/usr/bin/env python3
"""Copy the pinned upstream dependency closure into the verifier's layout."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

UPSTREAM_COMMIT = 'aa2a42f4f3835347ad46608779e22dd52c2dc7bf'
ROOT_MODULES = [
    'CatalanMeasure.GenD.Uniform.Bank532.Hosts532Inst',
    'CatalanMeasure.GenD.Analytic.GapWeights',
]
VENDORED_ROOTS = {'CatalanMeasure', 'CatalanCore', 'OAI', 'PrimeNumberTheoremAnd'}
IMPORT = re.compile(r'^(\s*(?:(?:public|private|meta)\s+)*import\s+)(.+)$')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def vendor(source, output):
    actual = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != UPSTREAM_COMMIT:
        raise ValueError(f'Expected upstream {UPSTREAM_COMMIT}, received {actual}')
    seen = set()
    stack = list(ROOT_MODULES)
    manifest = []
    while stack:
        module = stack.pop()
        if module in seen or module.split('.')[0] not in VENDORED_ROOTS:
            continue
        seen.add(module)
        relative = Path(*module.split('.')).with_suffix('.lean')
        original = (source / relative).read_bytes()
        lines = original.decode().split('\n')
        for i, line in enumerate(lines):
            match = IMPORT.match(line)
            if not match:
                continue
            names = match[2].split()
            stack.extend(n for n in names if n.split('.')[0] in VENDORED_ROOTS)
            fixed = ['Submission.' + n if n.split('.')[0] in VENDORED_ROOTS else n for n in names]
            if fixed != names:
                lines[i] = match[1] + ' '.join(fixed)
        transformed = '\n'.join(lines).encode()
        target = output / 'Submission' / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(transformed)
        manifest.append({'path': str(relative), 'source_sha256': sha(original),
                         'converted_sha256': sha(transformed), 'bytes': len(transformed)})
    record = {'source_repository': 'https://github.com/slitsey/catalan-irrationality-measure',
              'source_commit': UPSTREAM_COMMIT, 'root_modules': ROOT_MODULES,
              'conversion': 'Prefix imports of vendored roots with Submission.',
              'files': sorted(manifest, key=lambda x: x['path'])}
    (output / 'certificates/lean_source_manifest.json').write_text(json.dumps(record, indent=2) + '\n')
    print(f'Copied {len(manifest)} files, {sum(x["bytes"] for x in manifest)} bytes')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    vendor(args.source.resolve(), args.output.resolve())
