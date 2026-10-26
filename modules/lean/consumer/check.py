#!/usr/bin/env python3
"""Bounded jar-only integration gate, separate from genuine prepared acceptance.

Supply independently resolved core-only and complete module classpaths; no source
folder, Git checkout or appended dependency overlay may enter either runtime.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile
from pom_contract import validate as validate_pom
from pattern_contract import entries as pattern_entries

PATTERN_SHA256 = 'd9e21fb6623b3eeec9b145f3bcf327b2f533e1fc1397c7db7d67026480e4b3bd'
module = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--core-classpath', required=True)
parser.add_argument('--module-classpath', required=True)
parser.add_argument('--core-version', required=True)
parser.add_argument('--pattern-repository', required=True, type=Path, help='Read-only Git objects for source provenance audit')
args = parser.parse_args()


def jars(value):
    paths = [Path(p).resolve() for p in value.split(os.pathsep)]
    if not paths or len(paths) != len(set(paths)) or any(not p.is_file() or p.suffix != '.jar' for p in paths):
        parser.error('Each classpath must contain unique explicit jar files only')
    return paths


def run(command, **kwargs):
    return subprocess.run(command, timeout=120, check=True, **kwargs)


def core_input(paths):
    found = []
    for path in paths:
        with zipfile.ZipFile(path) as archive:
            entry = 'META-INF/maven/org.replikativ/ansatz/pom.properties'
            if entry in archive.namelist():
                props = dict(line.split('=', 1) for line in archive.read(entry).decode().splitlines()
                             if '=' in line and not line.startswith('#'))
                found.append((path, props.get('version')))
    if len(found) != 1 or found[0][1] != args.core_version:
        raise AssertionError('Exactly one matching pinned core jar required')
    return found[0][0]


core, complete = jars(args.core_classpath), jars(args.module_classpath)
assert core_input(core) == core_input(complete), 'Both profiles must use the same explicit core jar'
optional = (module / 'target/ansatz-lean.jar').resolve()
assert optional in complete and optional not in core, 'Module basis must resolve the built optional jar'
run([sys.executable, '-m', 'unittest', 'test_pom_contract', 'test_pattern_contract'], cwd=module / 'consumer')
inventory = (module / 'runtime-closure.edn').read_text()
closure = []
for field in ['sources', 'resources']:
    section = re.search(r':' + field + r'\s*\[([^\]]*)\]', inventory)
    assert section, 'Missing closed inventory section'
    closure.extend(re.findall(r'"(prototype/[^" ]+)"', section.group(1)))
assert len(closure) == len(set(closure))
with zipfile.ZipFile(optional) as archive:
    validate_pom(archive.read('META-INF/maven/org.replikativ/ansatz-lean/pom.xml'), args.core_version)
    assert archive.read('META-INF/ansatz-lean/runtime-closure.edn').decode() == inventory
    names = set(archive.namelist())
    actual = {n for n in names if n.startswith('prototype/') and not n.endswith('/')}
    assert actual == set(closure), ('Runtime closure mismatch', actual ^ set(closure))
    assert not any(n.startswith(('ansatz/kernel/', 'ansatz/runtime/')) for n in names), 'Duplicated core classes'
    assert not any(n.endswith('__init.class') for n in names), 'Ansatz prototype/facade must remain source-loaded'
    for name in closure:
        assert archive.read(name) == (module / '../../experiments/lean-ir/src' / name).read_bytes(), name
for path in core:
    with zipfile.ZipFile(path) as archive:
        assert not pattern_entries(archive.namelist()), 'Pattern leaked into the core-only dependency closure'

spec = importlib.util.spec_from_file_location('pattern_profile', module / 'build-pattern-profile.py')
profile_builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profile_builder)
pinned = {name: data for name, data in profile_builder.pinned_entries(args.pattern_repository).items()
          if not name.startswith('META-INF/')}
pattern = []
for path in complete:
    with zipfile.ZipFile(path) as archive:
        names = set(archive.namelist())
        assert not any(n.startswith('pattern/llvm/') for n in names), 'No LLVM compiler dependency'
        if pattern_entries(names):
            assert hashlib.sha256(path.read_bytes()).hexdigest() == PATTERN_SHA256, 'Unexpected released Pattern artifact'
            props = archive.read('META-INF/maven/org.replikativ/pattern/pom.properties').decode()
            assert 'version=1.0.452' in props
            for name, data in pinned.items():
                assert archive.read(name) == data, 'Pattern source provenance mismatch: ' + name
            pattern.append({'sha256': PATTERN_SHA256, 'source_files_equal_to_git_pin': len(pinned),
                            'git_pin': profile_builder.PIN,
                            'aot_initializer_count': sum(n.endswith('__init.class') for n in names)})
assert len(pattern) == 1, 'One resolved published Pattern dependency required'

core_cp, module_cp = os.pathsep.join(map(str, core)), os.pathsep.join(map(str, complete))
with tempfile.TemporaryDirectory(prefix='clean-consumer-', dir=module / 'target') as staging:
    staging = Path(staging)
    for name in ['smoke.clj', 'Smoke.java', 'PreparedAcceptance.java', 'compiler-fixture.clj',
                 'compiler-lazy.clj', 'compiler-smoke.clj', 'CompilerSmoke.java']:
        shutil.copy2(module / 'consumer' / name, staging / name)
    fixtures = staging / 'compiler-fixtures.jar'
    with zipfile.ZipFile(fixtures, 'w') as archive:
        archive.write(module / '../../experiments/lean-ir/fixtures/boxed-scalar-wrapper-programs.jsonl',
                      'compiler-consumer/boxed-scalar-wrapper-programs.jsonl')
    fixture_cp = os.pathsep.join([module_cp, str(fixtures)])
    negative = "(require 'ansatz.core) (assert (nil? (clojure.java.io/resource \"ansatz/lean.clj\"))) (assert (try (Class/forName \"ansatz.lean.LeanRuntime\") false (catch ClassNotFoundException _ true))) (println :core-alone-passed)"
    run(['java', '-Xmx384m', '-Xss8m', '-cp', core_cp, 'clojure.main', '-e', negative], cwd=staging)
    run(['java', '-Xmx384m', '-Xss8m', '-cp', module_cp, 'clojure.main', 'smoke.clj'], cwd=staging)
    run(['java', '-Xmx384m', '-Xss8m', '-cp', fixture_cp, 'clojure.main', 'compiler-lazy.clj'], cwd=staging)
    run(['javac', '-J-Xmx384m', '--release', '11', '-cp', module_cp, '-d', str(staging),
         'Smoke.java', 'PreparedAcceptance.java', 'CompilerSmoke.java'], cwd=staging)
    runtime = os.pathsep.join([fixture_cp, str(staging)])
    run(['java', '-Xmx384m', '-Xss8m', '-cp', runtime, 'Smoke'], cwd=staging)
    run(['java', '-Xmx384m', '-Xss8m', '-cp', runtime, 'clojure.main', 'compiler-smoke.clj'], cwd=staging)
print(json.dumps({'schema': 'optional-lean-module-inputs/2', 'pattern': pattern,
                  'jars_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in core + complete}}, indent=2))
print('Clean jar Clojure/Java compiler packaging gate passed; genuine prepared acceptance remains separate.')
