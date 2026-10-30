#!/usr/bin/env python3
"""Check one Lean file after Lake has built its imported dependencies.

This is an iteration helper. The submission gate remains `lake build Submission`.
Set CATALAN_LEAN_BIN to a compiler path, or put the pinned `lean` on PATH.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('source', type=Path)
parser.add_argument('--emit', action='store_true', help='Write an olean for downstream local checks.')
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'lake-manifest.json').read_text())
paths = [root / '.lake/packages' / p['name'] / '.lake/build/lib/lean' for p in manifest['packages']]
paths.append(root / '.lake/build/lib/lean')
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(str(p) for p in paths)
lean = env.get('CATALAN_LEAN_BIN') or shutil.which('lean')
if not lean:
    parser.error('Put the pinned Lean compiler on PATH or set CATALAN_LEAN_BIN.')
source = args.source.resolve()
command = [lean, '-DautoImplicit=false', str(source)]
if args.emit:
    target = root / '.lake/build/lib/lean' / source.relative_to(root).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    command += ['-o', str(target)]
raise SystemExit(subprocess.run(command, cwd=root, env=env).returncode)
