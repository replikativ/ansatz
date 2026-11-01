# Extraction boundary and remaining package acceptance

Source-only proposal accompanying this internal skeleton. No public Java API has
been added. The next review decides whether the extracted resource/classpath
boundary is sound before public Java facade work begins.

## Inventory

- Runtime source: `src/ansatz/lean/jvm/ir.clj`, namespace `ansatz.lean.jvm.ir`.
- Runtime metadata: `resources/META-INF/ansatz-lean-jvm/runtime.edn`.
- Authoritative Java input: the existing research `Interpreter.java`, explicitly
  named and SHA-pinned in `runtime-closure.edn`. Build-time capture checks the
  exact bounded byte array again and writes only that file to the owned
  `target/java-source` staging tree; javac receives only this tree. No canonical
  source neighbors become inputs, even if they appear after initial audit. All
  compiled nested classes belong in the jar. No copy of that source is tracked in this module.
- Producer-only: `build.clj`, `ansatz_lean_jvm_build_audit.clj`, dependency/build
  configuration and strict inventory. These are not staged runtime namespaces.
- Tests: two source-loaded check files under `test/`, excluded from the jar.

The build stages only src/resources plus compiled interpreter classes and Maven
metadata. It does not stage experiments, prototype, the research j namespace,
benchmark/reference code, fixture evidence, native compiler or old resident
backend. The runtime namespace has no require graph beyond Clojure itself and
imports only Java reflection types. Its method wrappers dispatch to the canonical
engine; parsing, RC, IR semantics and initialization behavior remain in Java.

## Acceptance still required

1. Root source-reader audit and negative inventory/dependency tests in the existing
   JVM. Run adapter preparation models against an existing matching Class.
2. Reviewed producer build with explicit compiler heap/process bounds. Inspect jar
   entries/POM, confirm exactly one engine implementation and no prototype/research
   namespace resources, and ensure no tooling/local-root dependency is published.
3. Jar-only require using the normal namespace resource path, then linked-basis
   preparation/execution from an empty working directory. Consumer classpath must
   contain only resolved jars, not test/research source directories.
4. Existing engine/header/initialization regressions as appropriate. Interpreter
   source bytes must remain unchanged by packaging.
5. Only after review, add a real public Java facade backed by admitted generic
   artifact/project metadata and explicit branch/handle lifetime. Packaging this
   adapter does not by itself fulfill loadProject/loadArtifact or typed handles.

Native compilation service extraction, bundled helper/platform distribution,
resource-backed compiled artifacts, StoreManager, one-branch-per-Project reuse,
actual Init completion and generically checked entry evidence remain separate
work. Do not expose the fixed tutorial profile as a generic project loader.
