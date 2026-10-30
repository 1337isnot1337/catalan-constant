#!/usr/bin/env python3
"""Compare a fetched Git commit with the final local Lean-source manifest.

This reads Git objects directly: it does not check out or execute the published
repository. It checks the exact source bytes and modes used by verifier staging.
Fetch the frozen public commit into a bare repository before running this tool.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z')
SHA = re.compile(r'[0-9a-f]{40}\Z')


def audit(git_dir, commit, manifest_path):
    if not SHA.fullmatch(commit):
        raise ValueError('The published commit must be a complete lowercase 40-digit SHA.')
    manifest_raw = manifest_path.read_bytes()
    manifest = json.loads(manifest_raw)
    if manifest.get('status') != 'passed' or manifest.get('errors'):
        raise ValueError('The local source-layout audit must pass before the remote audit.')
    expected = manifest['source_sha256']
    git = ['git', '--git-dir='+str(git_dir), '-c', 'core.hooksPath=/dev/null',
           '-c', 'credential.helper=']
    def read(*args):
        return subprocess.check_output(git+list(args))
    if read('cat-file','-t',commit).strip() != b'commit':
        raise ValueError('The frozen object is not a commit.')
    entries, errors = [], []
    for entry in read('ls-tree','-rz','--full-tree',commit).split(b'\0'):
        if not entry:
            continue
        metadata, raw_path = entry.split(b'\t',1)
        mode, kind, object_id = metadata.decode('ascii').split()
        path = raw_path.decode('utf-8')
        rel = PurePosixPath(path)
        if not rel.parts or rel.parts[0].removesuffix('.lean') != 'Submission' or rel.suffix != '.lean':
            continue
        module = '.'.join(rel.with_suffix('').parts)
        if mode != '100644' or kind != 'blob' or not NAME.fullmatch(module):
            errors.append({'kind':'invalid_git_mode_or_path','path':path,'mode':mode,'object_type':kind})
        entries.append((path,mode,kind,object_id))
    objects = [e[3] for e in entries]
    data = subprocess.check_output(git+['cat-file','--batch'],
        input=(''.join(x+'\n' for x in objects)).encode('ascii'))
    offset, total, actual = 0, 0, {}
    for path,mode,kind,object_id in entries:
        end = data.index(b'\n',offset)
        header = data[offset:end].decode('ascii').split()
        if len(header)!=3 or header[0]!=object_id:
            raise ValueError('Unexpected Git batch object header.')
        size = int(header[2])
        raw = data[end+1:end+1+size]
        if len(raw)!=size or data[end+1+size:end+2+size]!=b'\n':
            raise ValueError('Truncated Git batch object.')
        offset = end+2+size
        if header[1]!='blob':
            errors.append({'kind':'source_is_not_blob','path':path})
        total += size
        if size>20_000_000:
            errors.append({'kind':'source_exceeds_20MB','path':path})
        actual[path] = hashlib.sha256(raw).hexdigest()
    if offset != len(data):
        raise ValueError('Unexpected bytes after Git batch output.')
    if total>150_000_000:
        errors.append({'kind':'combined_sources_exceed_150MB'})
    for path in sorted(expected.keys()-actual.keys()):
        errors.append({'kind':'missing_published_source','path':path})
    for path in sorted(actual.keys()-expected.keys()):
        errors.append({'kind':'extra_published_source','path':path})
    for path in sorted(expected.keys() & actual.keys()):
        if expected[path]!=actual[path]:
            errors.append({'kind':'source_bytes_differ','path':path})
    published_manifest = read('show',commit+':certificates/lean_source_audit.json')
    if published_manifest != manifest_raw:
        errors.append({'kind':'published_source_manifest_differs'})
    return {
        'status':'passed' if not errors else 'failed',
        'commit':commit,
        'errors':errors,
        'published_lean_sources':len(entries),
        'published_lean_bytes':total,
        'manifest_sha256':hashlib.sha256(manifest_raw).hexdigest(),
        'published_source_sha256':actual,
    }


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--git-dir',type=Path,required=True)
    parser.add_argument('--commit',required=True)
    parser.add_argument('--manifest',type=Path,default=Path('certificates/lean_source_audit.json'))
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=audit(args.git_dir,args.commit,args.manifest)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()
                     if k not in {'manifest_sha256','published_source_sha256'}},indent=2))
    raise SystemExit(bool(result['errors']))
