#!/usr/bin/env python3
"""Fresh paired artifact run; publish admission receipt only after independent audit."""
import json
import os
import time
from pathlib import Path
import shutil
import subprocess
import sys
from audit import audit, digest, require


def snapshot(prefix):
    files = sorted((prefix / 'lib/lean/Init').glob('Prelude.*'))
    require(len(files) >= 5, 'missing Prelude compiled module parts')
    return {str(p): {'sha256': digest(p), 'bytes': p.stat().st_size} for p in files if p.is_file()}


def main():
    here = Path(__file__).resolve().parent
    build = here.parent / os.environ.get('PAIRED_PRELUDE_BUILD', 'target/matched-prelude-producer-structural-v3')
    output = Path(sys.argv[1]).resolve()
    require(not output.exists(), 'output must not exist; failed stages require explicit inspection')
    output.mkdir(parents=True)
    cohort = json.loads((build / 'build-cohort.json').read_text())
    require(digest(build / 'Export.lean') == cohort['sourceFiles']['lean4export-patched/Export.lean'], 'patched exporter source changed')
    require(cohort['exporterCacheEquality'] == 'Lean.ExprStructEq/Expr.equal', 'structural exporter cache profile required')
    require(digest(build / 'produce') == cohort['sourceFiles']['binary/produce'], 'producer binary changed')
    for p in here.iterdir():
        key = f'producer/{p.name}'
        if key in cohort['sourceFiles']:
            require(digest(p) == cohort['sourceFiles'][key], f'producer source changed since build: {p.name}')
    prefix = Path(subprocess.check_output(['lean', '+leanprover/lean4:v4.33.1', '--print-prefix'], text=True).strip())
    before = snapshot(prefix)
    shutil.copyfile(build / 'build-cohort.json', output / 'build-cohort.json')
    env = dict(os.environ, LEAN_SYSROOT=str(prefix), LEAN_NUM_THREADS='1')
    env.pop('LEAN_PATH', None)
    started = time.monotonic()
    peak = 0
    process = subprocess.Popen([str(build / 'produce'), str(output)], env=env)
    try:
        while process.poll() is None:
            try:
                status = Path(f'/proc/{process.pid}/status').read_text()
                rss = next(int(line.split()[1]) for line in status.splitlines() if line.startswith('VmRSS:'))
                peak = max(peak, rss)
            except (FileNotFoundError, StopIteration):
                rss = 0
            available = next(int(line.split()[1]) for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))
            require(rss <= 1200 * 1024 and available >= 1500 * 1024, 'resource floor/cap exceeded')
            require(sum(p.stat().st_size for p in output.iterdir() if p.is_file()) <= 128 * 1024 * 1024, 'producer output byte bound exceeded')
            require(time.monotonic() - started <= 120, 'producer wall bound exceeded')
            time.sleep(0.05)
        require(process.returncode == 0, f'native producer exit {process.returncode}')
    finally:
        if process.poll() is None:
            process.terminate()
            process.wait(timeout=5)
    (output / 'producer-resources.json').write_text(json.dumps({'peakSampledRSSKiB': peak, 'wallSeconds': time.monotonic() - started}) + '\n')
    require(before == snapshot(prefix), 'compiled module files changed during paired read')
    source = json.loads((output / 'correspondence.json').read_text())
    for module in source['source']['modules']:
        for part in module['parts'] + module['irParts']:
            artifact = part['artifact']
            require(artifact['filePath'] in before, 'unexpected compiled module source')
            require(artifact['leanCommit'] == cohort['leanCommit'], 'compiled module cohort mismatch')
    (output / 'module-file-cohort.json').write_text(json.dumps(before, sort_keys=True, indent=2) + '\n')
    receipt = audit(output)
    receipt['moduleFiles'] = {'sha256': digest(output / 'module-file-cohort.json')}
    (output / 'pair-audit.json').write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
    print(json.dumps(receipt, sort_keys=True))

if __name__ == '__main__':
    main()
