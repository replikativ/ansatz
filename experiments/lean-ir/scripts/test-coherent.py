#!/usr/bin/env python3
"""Fixture-free coherent infrastructure checks, never restore or guest execution.

Build all 24 Java sources into one fresh class directory. Run the 28 host models
and six namespace definitions, ten Python metadata tests, then a separate JVM
whose copied source tree physically excludes coherent namespaces/AOT outputs.
This is component CI, not a closed runtime/bootstrap attestation.
"""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--classpath', help='Explicit dependency basis for a reviewed local guard; default: CLI -Spath')
    p.add_argument('--java', default=shutil.which('java'))
    p.add_argument('--javac', default=shutil.which('javac'))
    args = p.parse_args()
    experiment = Path(__file__).resolve().parents[1]
    repo = experiment.parents[1]
    basis = args.classpath
    if basis is None:
        basis = subprocess.check_output(['clojure', '-J-Xmx128m', '-Srepro', '-Spath'], cwd=repo, text=True).strip()
    # Keep dependency jars; source/class roots are explicitly selected below.
    jars = [Path(x).resolve(strict=True) for x in basis.split(os.pathsep) if x.endswith('.jar')]
    if not jars or len(jars) != len(set(jars)):
        raise ValueError('explicit unique dependency jars required')
    clojure = [p for p in jars if p.name == 'clojure-1.12.0.jar']
    if len(clojure) != 1:
        raise ValueError('Clojure 1.12.0 compiler basis required; selected ' + ','.join(p.name for p in jars if p.name.startswith('clojure-'))[:256])
    print('Coherent compiler basis: ' + clojure[0].name, flush=True)
    java = sorted((repo / 'src-java').rglob('*.java')) + [experiment / 'java/prototype/TypedLongMemo.java']
    if len(java) != 24 or not all(p.is_file() for p in java):
        raise ValueError('all current 23 core Java sources plus TypedLongMemo required')
    (repo / 'target').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='coherent-ci-', dir=repo / 'target') as temporary:
        work = Path(temporary); classes = work / 'classes'; classes.mkdir()
        subprocess.run([args.javac, '-J-Xmx256m', '-source', '11', '-target', '11',
                        '-cp', str(clojure[0]), '-d', str(classes)] + list(map(str, java)), check=True)
        if len(list(classes.rglob('*.class'))) != 48:
            raise ValueError('expected complete fresh 48-class cohort')
        normal = os.pathsep.join(map(str, [classes, repo / 'src', repo / 'resources', experiment / 'src', experiment / 'test'] + jars))
        subprocess.run([args.java, '-Xmx384m', '-Xss8m', '-Dansatz.coherent.test.class-root=' + str(classes),
                        '-cp', normal, 'clojure.main', 'scripts/test-coherent.clj'], cwd=experiment, check=True)
        subprocess.run([sys.executable, 'scripts/coherent/test-materialize-pack.py'], cwd=experiment, check=True)
        # One physical source root, excluding ALL coherent controller/profile
        # namespaces. No normal repository source/AOT directory is in this JVM.
        legacy = work / 'legacy-source'; legacy.mkdir()
        for source_root in [repo / 'src', experiment / 'src']:
            for source in source_root.rglob('*'):
                if not source.is_file() or source.suffix not in ('.clj', '.cljc', '.edn'):
                    continue
                relative = source.relative_to(source_root)
                if relative.parts[0] == 'prototype' and source.name.startswith('coherent_'):
                    continue
                target = legacy / relative
                if target.exists():
                    raise ValueError('duplicate legacy source identity')
                target.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(source, target)
        probe = work / 'legacy-test/prototype/legacy_consumer_load_probe.clj'; probe.parent.mkdir(parents=True)
        shutil.copyfile(experiment / 'test/prototype/legacy_consumer_load_probe.clj', probe)
        legacy_resources = work / 'legacy-resources'; legacy_resources.mkdir()
        for source in (repo / 'resources').rglob('*'):
            if source.is_file():
                relative = source.relative_to(repo / 'resources')
                if relative.parts[0] == 'prototype' and source.name.startswith('coherent_'):
                    continue
                target = legacy_resources / relative
                target.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(source, target)
        isolated = os.pathsep.join(map(str, [legacy, probe.parents[1], classes, legacy_resources] + jars))
        subprocess.run([args.java, '-Xmx384m', '-Xss8m', '-cp', isolated, 'clojure.main',
                        '-m', 'prototype.legacy-consumer-load-probe', str(legacy)], check=True)
        print('COHERENT_LEGACY_FRESH_LOAD_PASS', flush=True)
    print('COHERENT_COMPONENT_CI_PASS', flush=True)


if __name__ == '__main__':
    main()
