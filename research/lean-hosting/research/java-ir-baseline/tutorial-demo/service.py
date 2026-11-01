#!/usr/bin/env python3
"""Pinned first-Lake native frontend/cache service; no JVM or hosted checker.

The explicitly configured installed official sysroot is a trusted immutable
dependency. Its reported commit, executable bytes and library stat inventory
are provenance/mutation guards, not cryptographic attestation of every library.
"""
import argparse
import errno
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time

LEAN_COMMIT = '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
EXPORTER_SHA = '0b0344058631b8c3dc18a8a1a600f8100611eaf49c3b4ee5ad18a121651e736e'
PROFILE = 'fp-lean-first-lake-native-4331/1'
SOURCES = {
    'Greeting/Basic.lean': 'b186dbcbc8cd3f04b6f9d39f4f130996ee75093b3d0923a9ceda2e2b70220afb',
    'Greeting.lean': 'b23733091936f7b4318c98880382dc901d5ca5830870bd40bbaa1128cbc91ed2',
    'Main.lean': '84b2361691c0d105c438b137563c447e36e38827aaa633707ca99d14c4d20316',
    'lakefile.toml': 'd66a3f6386de06f0f3666cde3101ec1c71884c9f2678a41c69aac1f5d5834c80',
}
MODULES = [('Greeting.Basic', 'Greeting/Basic.lean'), ('Greeting', 'Greeting.lean'), ('Main', 'Main.lean')]
MAX_BYTES = 32 * 1024 * 1024


def require(ok, message):
    if not ok:
        raise ValueError(message)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def stamp(path):
    s = path.lstat()
    require(stat.S_ISREG(s.st_mode) and not path.is_symlink(), 'Regular non-symlink file required: ' + str(path))
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def hash_file(path, maximum=None):
    before = stamp(path)
    require(maximum is None or before[2] <= maximum, 'File exceeds bound: ' + str(path))
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(65536), b''):
            h.update(block)
    require(before == stamp(path), 'File changed during hash: ' + str(path))
    return {'bytes': before[2], 'sha256': h.hexdigest()}


def source_inputs(project):
    result = {}
    for relative, expected in SOURCES.items():
        path = project / relative
        require(path.resolve().is_relative_to(project), 'Source escapes project')
        for parent in path.relative_to(project).parents:
            require(not (project / parent).is_symlink(), 'Source directory symlink')
        record = hash_file(path, 65536)
        require(record['sha256'] == expected, 'Unsupported or modified selected source: ' + relative)
        result[relative] = record
    return result


def available_kib():
    return next(int(x.split()[1]) for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))


def run_process(label, command, environment, cwd, directory, progress=True):
    require(available_kib() >= 2 * 1024 * 1024, 'MemAvailable is below the 2 GiB process floor')
    stdout, stderr = directory / (label + '.jsonl'), directory / (label + '.stderr')
    start, peak, stop = time.monotonic(), 0, None

    def limits():
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        resource.setrlimit(resource.RLIMIT_CPU, (90, 90))
        resource.setrlimit(resource.RLIMIT_FSIZE, (MAX_BYTES, MAX_BYTES))

    with stdout.open('xb') as o, stderr.open('xb') as e:
        process = subprocess.Popen([str(x) for x in command], env=environment, cwd=cwd,
                                   stdout=o, stderr=e, start_new_session=True, preexec_fn=limits)
        try:
            while process.poll() is None:
                try:
                    status = Path(f'/proc/{process.pid}/status').read_text().splitlines()
                    rss = next(int(x.split()[1]) for x in status if x.startswith('VmRSS:'))
                except (FileNotFoundError, StopIteration):
                    rss = 0
                peak = max(peak, rss)
                if peak > 900 * 1024:
                    stop = 'RSS-900MiB'
                if available_kib() < 2 * 1024 * 1024:
                    stop = 'MemAvailable-2GiB'
                if time.monotonic() - start > 120:
                    stop = 'wall-120s'
                if stdout.stat().st_size > MAX_BYTES or stderr.stat().st_size > 1024 * 1024:
                    stop = 'output-cap'
                if stop:
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                    break
                time.sleep(.02)
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
            code = process.wait()
    receipt = {'label': label, 'command': [str(x) for x in command], 'exit': code, 'stop': stop,
               'stdout': stdout.name, **{'stdout' + k[0].upper() + k[1:]: v for k, v in hash_file(stdout).items()},
               'stderr': stderr.name, **{'stderr' + k[0].upper() + k[1:]: v for k, v in hash_file(stderr).items()},
               'elapsedSeconds': time.monotonic() - start, 'peakSampledRSSKiB': peak}
    (directory / (label + '.receipt.json')).write_bytes(canonical(receipt) + b'\n')
    if progress:
        print(json.dumps({'stage': label, 'exit': code, 'stop': stop, 'peakSampledRSSKiB': peak}), file=sys.stderr, flush=True)
    diagnostic = stderr.read_bytes()[:2048].decode('utf-8', errors='replace')
    require(code == 0 and stop is None and stderr.stat().st_size == 0,
            'Native command failed at ' + label + ': ' + str(code) + '/' + str(stop) + ' ' + diagnostic)
    return receipt


def toolchain_descriptor(sysroot, exporter, cache):
    lean = sysroot / 'bin/lean'
    library = sysroot / 'lib/lean'
    require(library.is_dir() and hash_file(exporter)['sha256'] == EXPORTER_SHA, 'Pinned exporter or sysroot differs')
    environment = dict(os.environ, LEAN_NUM_THREADS='1', MALLOC_ARENA_MAX='1', LEAN_SYSROOT=str(sysroot),
                       LEAN_PATH=str(library), PATH=str(sysroot / 'bin') + os.pathsep + os.environ.get('PATH', ''))
    with tempfile.TemporaryDirectory(prefix='.identity-', dir=cache) as temporary:
        directory = Path(temporary)
        run_process('commit', [lean, '--githash'], environment, directory, directory, False)
        run_process('version', [lean, '--version'], environment, directory, directory, False)
        commit = (directory / 'commit.jsonl').read_text().strip()
        version = (directory / 'version.jsonl').read_text().strip()
    require(commit == LEAN_COMMIT and '4.33.1' in version, 'Installed Lean reports another supported version')
    inventory = []
    # The exported producer imports Init's module files. Include all of their
    # installed companion files as bounded mutation signals, not byte proofs.
    for path in sorted(library.rglob('*')):
        relative = path.relative_to(library)
        if not (path.name.startswith('Init.') or 'Init' in relative.parts[:-1]):
            continue
        require(not path.is_symlink(), 'Symlink in trusted Init library inventory')
        if path.is_file():
            require(len(inventory) < 4096, 'Init library inventory bound')
            inventory.append([relative.as_posix(), stamp(path)])
    require(inventory, 'Installed Init inventory absent')
    return {'policy': 'trusted-immutable-installed-official-toolchain/1', 'sysroot': str(sysroot),
            'reportedCommit': commit, 'reportedVersion': version, 'leanExecutable': hash_file(lean),
            'exporter': hash_file(exporter), 'exporterPath': str(exporter),
            'initLibraryStatInventorySHA256': digest(canonical(inventory)), 'initLibraryFiles': len(inventory),
            'fullLibraryByteAuthentication': False}, environment


def typed_name(label):
    result = ['anonymous']
    for part in label.split('.'):
        result = ['str', result, part]
    return result


def read_stream(path):
    require(stamp(path)[2] <= MAX_BYTES, 'IR stream bound')
    with path.open('rb') as f:
        lines = f.read(MAX_BYTES + 1).splitlines()
    require(0 < len(lines) <= 20001, 'IR row bound')
    manifest, *rows = [json.loads(x) for x in lines]
    require(manifest.get('schema') == 'lean-ir-probe/1' and manifest.get('leanVersion') == '4.33.1'
            and manifest.get('runtimeProfile') == {'target': 'x86_64-unknown-linux-gnu', 'wordBits': 64}, 'IR manifest differs')
    require(all(r.get('kind') == 'decl' for r in rows), 'Missing or unsupported emitted IR row')
    return manifest, rows


def file_inventory(directory):
    result = {}
    for path in sorted(directory.rglob('*')):
        require(not path.is_symlink(), 'Symlink in cached artifact bundle')
        if path.is_dir():
            continue
        require(path.is_file() and len(result) < 128, 'Cached artifact file kind/count bound')
        relative = path.relative_to(directory).as_posix()
        if relative != 'manifest.json':
            result[relative] = hash_file(path, MAX_BYTES)
    return result


def validate_hit(directory, key, inputs):
    require(directory.is_dir() and not directory.is_symlink(), 'Invalid cache entry directory')
    manifest_path = directory / 'manifest.json'
    before = stamp(manifest_path)
    require(before[2] <= 4 * 1024 * 1024, 'Cache manifest bound')
    with manifest_path.open('rb') as reader:
        raw = reader.read(4 * 1024 * 1024 + 1)
    require(len(raw) <= 4 * 1024 * 1024 and before == stamp(manifest_path), 'Cache manifest changed during read')
    manifest = json.loads(raw)
    require(manifest.get('schema') == 'native-compiled-project/1' and manifest.get('cacheKey') == key
            and manifest.get('inputs') == inputs, 'Cache entry belongs to another compile profile')
    require(manifest.get('files') == file_inventory(directory), 'Cached artifact file set/bytes changed')
    return manifest, digest(raw)


def compile_project(project, cache, sysroot, exporter, native_reference=False):
    project, cache, sysroot, exporter = project.resolve(strict=True), cache.resolve(), sysroot.resolve(strict=True), exporter.resolve(strict=True)
    require(project.is_dir(), 'Project directory required')
    cache.mkdir(parents=True, exist_ok=True)
    sources = source_inputs(project)
    toolchain, environment = toolchain_descriptor(sysroot, exporter, cache)
    inputs = {'profile': PROFILE, 'serviceSHA256': hash_file(Path(__file__).resolve())['sha256'],
              'sources': sources, 'toolchain': toolchain, 'options': {'nativeReference': native_reference, 'threads': 1}}
    key = digest(canonical(inputs))
    target = cache / key
    if target.exists() or target.is_symlink():
        _, pin = validate_hit(target, key, inputs)
        return {'status': 'ready', 'cacheHit': True, 'cacheKey': key, 'manifest': str(target / 'manifest.json'), 'manifestSHA256': pin}
    temporary = Path(tempfile.mkdtemp(prefix='.' + key + '-', dir=cache))
    try:
        copied, build = temporary / 'project', temporary / 'build'
        copied.mkdir(); build.mkdir()
        for relative, expected in sources.items():
            path = copied / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(project / relative, path)
            require(hash_file(path) == expected, 'Project changed during private copy')
        environment['LEAN_PATH'] = str(build) + os.pathsep + str(sysroot / 'lib/lean')
        ordered = []
        for label, relative in MODULES:
            olean = build / (label.replace('.', '/') + '.olean')
            olean.parent.mkdir(parents=True, exist_ok=True)
            receipt = run_process(label + '-local', [exporter, '--source', copied / relative, '--olean', olean, '--local', label],
                                  environment, copied, temporary)
            manifest, rows = read_stream(temporary / receipt['stdout'])
            plan = manifest.get('initializationPlan')
            require(plan and plan.get('module') == typed_name(label) and plan.get('actions') == [], 'Selected module initialization plan changed')
            require(all(r.get('sourceLocal') is True and r.get('sourceModule') == typed_name(label) for r in rows), 'Local source provenance changed')
            ordered.append({'module': label, 'typedModule': typed_name(label), 'source': 'project/' + relative,
                            'sourceSHA256': sources[relative]['sha256'], 'olean': olean.relative_to(temporary).as_posix(),
                            'oleanSHA256': hash_file(olean)['sha256'], 'localStream': receipt['stdout'],
                            'localStreamSHA256': receipt['stdoutSha256'], 'initPlan': plan, 'rowCount': len(rows)})
        closure = run_process('Main-closure', [exporter, '--source', copied / 'Main.lean', '--closure', 'Main', 'main'], environment, copied, temporary)
        manifest, rows = read_stream(temporary / closure['stdout'])
        names = {canonical(r['name']) for r in rows}
        require(len(names) == len(rows) and all(canonical(n) in names for r in rows for n in r['dependencies']), 'Incomplete static dependency closure')
        main = next((r for r in rows if r['name'] == typed_name('main')), None)
        require(main and main['ir']['fdecl']['xs'] == [{'borrow': False, 'ty': 'void', 'x': {'idx': 1}}]
                and main['ir']['fdecl']['type'] == 'object', 'Original main raw IO ABI differs')
        reference = None
        if native_reference:
            r = run_process('native-reference', [sysroot / 'bin/lean', '--run', copied / 'Main.lean'], environment, copied, temporary)
            require((temporary / r['stdout']).read_bytes() == b'Hello, world!\n', 'Native reference output differs')
            reference = {'receipt': 'native-reference.receipt.json', 'stdoutSHA256': r['stdoutSha256'],
                         'stdoutBytes': r['stdoutBytes'], 'stdoutUTF8': (temporary / r['stdout']).read_text(encoding='utf-8'), 'exit': r['exit']}
        require(source_inputs(project) == sources and source_inputs(copied) == sources, 'Selected source changed during compilation')
        current_toolchain, _ = toolchain_descriptor(sysroot, exporter, cache)
        require(current_toolchain == toolchain, 'Trusted toolchain changed during compilation')
        artifact = {'schema': 'native-compiled-project/1', 'profile': PROFILE, 'cacheKey': key, 'inputs': inputs,
                    'producerLeanCommit': LEAN_COMMIT, 'producerLeanVersion': '4.33.1', 'target': 'x86_64-unknown-linux-gnu',
                    'exporterSHA256': EXPORTER_SHA, 'serviceSHA256': inputs['serviceSHA256'],
                    'repositoryCommit': '0abeea545d560a324e2561f7210fbd6ed154fa02', 'sourceFilesUnchanged': True,
                    'orderedModules': ordered, 'executionStream': closure['stdout'], 'executionStreamSHA256': closure['stdoutSha256'],
                    'entry': typed_name('main'), 'nativeReference': reference, 'staticDependencyClosureComplete': True,
                    'dynamicClosureProven': False, 'guestModuleDataAccepted': False, 'guestKernelAccepted': False,
                    'trustBoundary': 'Official native frontend/checker/compiler; no hosted frontend or Java kernel rechecking',
                    'files': file_inventory(temporary)}
        # Last file is the authority-bearing complete manifest. Publish the
        # entire new directory atomically; never patch an accepted cache entry.
        with (temporary / 'manifest.json').open('xb') as f:
            f.write(canonical(artifact) + b'\n'); f.flush(); os.fsync(f.fileno())
        validate_hit(temporary, key, inputs)
        try:
            temporary.rename(target)
        except OSError as error:
            if error.errno not in (errno.EEXIST, errno.ENOTEMPTY):
                raise
            validate_hit(target, key, inputs)
            shutil.rmtree(temporary)
        _, pin = validate_hit(target, key, inputs)
        return {'status': 'ready', 'cacheHit': False, 'cacheKey': key, 'manifest': str(target / 'manifest.json'), 'manifestSHA256': pin}
    except BaseException:
        # No runtime/guest owners exist here. Preserve failed compiler evidence;
        # the caller may inspect/remove only this private unpublished directory.
        print(json.dumps({'status': 'compile-failed', 'unpublishedDirectory': str(temporary)}), file=sys.stderr)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['project', 'cache', 'sysroot', 'exporter']:
        parser.add_argument('--' + name, required=True, type=Path)
    parser.add_argument('--native-reference', action='store_true')
    args = parser.parse_args()
    try:
        result = compile_project(args.project, args.cache, args.sysroot, args.exporter, args.native_reference)
        print(json.dumps(result), flush=True)
    except Exception as error:
        print(json.dumps({'status': 'error', 'class': type(error).__name__, 'message': str(error)[:2048]}), flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
