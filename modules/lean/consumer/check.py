#!/usr/bin/env python3
"""Clean jar packaging/load gate, not a substitute for prepared frontend acceptance.
Run only after coordinated JVM permission: python3 consumer/check.py --core-classpath <jar-only-cp>.
Classpath must contain pinned core + its Maven dependency jars; optional is added here.
"""
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import zipfile
import xml.etree.ElementTree as ET

module = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--core-classpath', required=True)
parser.add_argument('--core-version', required=True)
args = parser.parse_args()
core = [Path(p).resolve() for p in args.core_classpath.split(os.pathsep)]
if not core or any(not p.is_file() or p.suffix != '.jar' for p in core):
    parser.error('core classpath must contain only explicit jar files')
core_metadata = []
for core_jar in core:
    with zipfile.ZipFile(core_jar) as archive:
        entry = 'META-INF/maven/org.replikativ/ansatz/pom.properties'
        if entry in archive.namelist():
            properties = dict(line.split('=', 1) for line in archive.read(entry).decode().splitlines()
                              if '=' in line and not line.startswith('#'))
            core_metadata.append(properties.get('version'))
assert core_metadata == [args.core_version], 'core classpath must contain one matching versioned core jar'
optional = module / 'target/ansatz-lean.jar'
closure = re.findall(r'"(prototype/[^" ]+)"', (module / 'runtime-closure.edn').read_text())
with zipfile.ZipFile(optional) as archive:
    pom = ET.fromstring(archive.read('META-INF/maven/org.replikativ/ansatz-lean/pom.xml'))
    ns = {'m': 'http://maven.apache.org/POM/4.0.0'}
    dependencies = pom.findall('m:dependencies/m:dependency', ns)
    core_dependencies = [dep for dep in dependencies
                         if dep.findtext('m:groupId', namespaces=ns) == 'org.replikativ'
                         and dep.findtext('m:artifactId', namespaces=ns) == 'ansatz']
    assert len(core_dependencies) == 1, 'one explicit core Maven dependency required'
    assert core_dependencies[0].findtext('m:version', namespaces=ns) == args.core_version, 'pinned core POM version'
    assert not any(node.tag.rsplit('}', 1)[-1] in {'systemPath', 'local/root'} for node in pom.iter()), 'local-path POM dependency'
    names = set(archive.namelist())
    actual = {name for name in names if name.startswith('prototype/') and not name.endswith('/')}
    assert actual == set(closure), ('runtime closure mismatch', actual ^ set(closure))
    assert all(not name.startswith(('ansatz/kernel/', 'ansatz/runtime/')) for name in names), 'duplicated core classes'
    assert not any(name.endswith('__init.class') for name in names), 'unexpected AOT'
    for name in closure:
        assert archive.read(name) == (module / '../../experiments/lean-ir/src' / name).read_bytes(), name
core_cp = os.pathsep.join(map(str, core))
optional_cp = os.pathsep.join([core_cp, str(optional)])
(module / 'target').mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='clean-consumer-', dir=module / 'target') as staging:
    staging = Path(staging)
    for name in ['smoke.clj', 'Smoke.java', 'PreparedAcceptance.java']:
        shutil.copy2(module / 'consumer' / name, staging / name)
    negative = "(require 'ansatz.core) (assert (nil? (clojure.java.io/resource \"ansatz/lean.clj\"))) (assert (try (Class/forName \"ansatz.lean.LeanRuntime\") false (catch ClassNotFoundException _ true))) (println :core-alone-passed)"
    subprocess.run(['java', '-cp', core_cp, 'clojure.main', '-e', negative], cwd=staging, check=True)
    subprocess.run(['java', '-cp', optional_cp, 'clojure.main', 'smoke.clj'], cwd=staging, check=True)
    subprocess.run(['javac', '--release', '11', '-cp', optional_cp, '-d', str(staging), 'Smoke.java', 'PreparedAcceptance.java'], cwd=staging, check=True)
    subprocess.run(['java', '-cp', os.pathsep.join([optional_cp, str(staging)]), 'Smoke'], cwd=staging, check=True)
print('Clean jar Clojure/Java packaging gate passed; genuine prepared acceptance remains separate.')
