#!/usr/bin/env python3
"""Bounded original Init metadata census. No JVM, store import or graph export."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

PIN = '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
MiB = 1024 * 1024
HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def available():
    return next(int(line.split()[1]) * 1024 for line in Path('/proc/meminfo').read_text().splitlines()
                if line.startswith('MemAvailable:'))


def rss(pid):
    try:
        return next(int(line.split()[1]) * 1024 for line in Path(f'/proc/{pid}/status').read_text().splitlines()
                    if line.startswith('VmRSS:'))
    except (FileNotFoundError, StopIteration):
        return 0


def limits():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    resource.setrlimit(resource.RLIMIT_FSIZE, (16 * MiB, 16 * MiB))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('output', type=Path)
    args = p.parse_args()
    version = subprocess.check_output(['lean', '+leanprover/lean4:v4.33.1', '--version'], text=True).strip()
    if PIN not in version or 'version 4.33.1,' not in version:
        raise RuntimeError('wrong Lean source build')
    prefix = Path(subprocess.check_output(['lean', '+leanprover/lean4:v4.33.1', '--print-prefix'], text=True).strip())
    if available() < 2048 * MiB:
        raise RuntimeError('MemAvailable below2GiB floor')
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = HERE / 'MetadataCensus.lean'
    command = [str(prefix / 'bin/lean'), '--run', str(source)]
    env = dict(os.environ, LEAN_SYSROOT=str(prefix), LEAN_PATH=str(prefix / 'lib/lean'), LEAN_NUM_THREADS='1')
    env['PATH'] = str(prefix / 'bin') + os.pathsep + env.get('PATH', '')
    started = time.monotonic()
    peak = 0
    stop = None
    raw, errors = out / 'census.json', out / 'census.stderr'
    with raw.open('wb') as stdout, errors.open('wb') as stderr:
        proc = subprocess.Popen(command, stdout=stdout, stderr=stderr, env=env,
                                start_new_session=True, preexec_fn=limits)
        while proc.poll() is None:
            peak = max(peak, rss(proc.pid))
            if peak > 2048 * MiB:
                stop = '2GiB RSS cap'
            elif available() < 2048 * MiB:
                stop = '2GiB MemAvailable floor'
            elif time.monotonic() - started > 150:
                stop = '150s wall deadline'
            elif errors.stat().st_size > MiB or raw.stat().st_size > 16 * MiB:
                stop = 'output cap'
            if stop:
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    proc.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                break
            time.sleep(0.05)
        code = proc.wait()
    receipt = {'schema': 'matched-init-metadata-native-run/1', 'exit': code, 'stop': stop,
               'toolchain': version, 'sourceSHA256': sha(source), 'runnerSHA256': sha(Path(__file__)),
               'leanExecutableSHA256': sha(prefix / 'bin/lean'), 'stdoutSHA256': sha(raw),
               'stderrSHA256': sha(errors), 'stderrBytes': errors.stat().st_size,
               'peakRSSBytes': peak, 'wallSeconds': time.monotonic() - started, 'command': command,
               'JVMStarted': False, 'storeOpened': False, 'graphExported': False}
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if code or stop or errors.stat().st_size:
        raise RuntimeError(f'Native census failed; diagnostics preserved in {out}')
    result = json.loads(raw.read_text())
    if result['leanCommit'] != PIN or result['schema'] != 'matched-default-init-metadata-census/1':
        raise RuntimeError('wrong source census')
    print(json.dumps({'directory': str(out), 'receipt': receipt,
                      'counts': {k: result[k] for k in ['moduleCount', 'partCount', 'selectedOccurrences', 'uniqueNames', 'kindOccurrences', 'mappedBytes']},
                      'duplicates': len(result['duplicates']), 'displayCollisions': len(result['displayCollisions'])}, indent=2))


if __name__ == '__main__':
    main()
