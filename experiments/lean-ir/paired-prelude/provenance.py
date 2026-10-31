#!/usr/bin/env python3
"""Bind actual compiler/exporter/helper bytes; never infer identity from version."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

PIN = '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def main():
    exporter, output = map(Path, sys.argv[1:])
    here = Path(__file__).resolve().parent
    root = here.parent
    build = root / 'target/matched-prelude-producer'
    prefix = subprocess.check_output(['lean', '+leanprover/lean4:v4.33.1', '--print-prefix'], text=True).strip()
    commit = subprocess.check_output(['lean', '+leanprover/lean4:v4.33.1', '--githash'], text=True).strip()
    if commit != PIN:
        raise ValueError('wrong Lean compiler')
    files = {f'producer/{p.name}': digest(p) for p in here.iterdir() if p.is_file() and p.suffix in {'.lean', '.sh', '.py', '.cpp'}}
    files.update({
        'lean4export/Export.lean': digest(exporter / 'Export.lean'),
        'native/ModuleDataTransport.cpp': digest(root / 'native/ModuleDataTransport.cpp'),
        'binary/produce': digest(build / 'produce'),
        'toolchain/bin/lean': digest(Path(prefix) / 'bin/lean'),
        'toolchain/lib/lean/libleanshared.so': digest(Path(prefix) / 'lib/lean/libleanshared.so'),
    })
    for unit in ['Export', 'Projection', 'ScalarCensus', 'MatchedPreludeProducer']:
        for suffix in ['olean', 'c', 'o']:
            p = build / f'{unit}.{suffix}'
            files[f'build/{p.name}'] = digest(p)
    output.write_text(json.dumps({'schema': 'matched-prelude-build-cohort/1', 'leanCommit': commit,
        'sourceFiles': files, 'exporterHead': subprocess.check_output(['git', '-C', str(exporter), 'rev-parse', 'HEAD'], text=True).strip(),
        'exporterDirty': bool(subprocess.check_output(['git', '-C', str(exporter), 'status', '--porcelain'], text=True).strip()),
        'nativeEnvironmentFinalized': False, 'importedProofsReplayed': False}, sort_keys=True, indent=2) + '\n')

if __name__ == '__main__':
    main()
