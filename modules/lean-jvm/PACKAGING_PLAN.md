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

## Accepted packaging boundary and remaining work

The root accepted source-reader inventory/capture audits (5 tests / 23 assertions)
and adapter preparation models (3 tests / 9 assertions) in the retained JVM.
The captured-source producer build passed with a 384 MiB heap. The built jar has
144 entries, 129 Java 17 interpreter classes, one canonical Clojure adapter
resource, and only Clojure 1.12.0 as its direct POM dependency. The Java-only
consumer passed with the SDK plus three normal Clojure jars, from an empty
working directory, with no research source roots or Clojure CLI on its classpath.
It reused one precompiled engine for results 37 and 42, then closed it; no old
backend namespace loaded. The actual archive audit and six rejection cases passed.
Portable hashes and actual receipts are in `validation.json`.

The final feature was rebased onto the newer byte-get landing as an ancestry-only
change; its Java engine, producer and adapter bytes were unchanged. Earlier jar
acceptance is retained separately rather than relabeled as final evidence.
A consumer using both optional modules together was not run; the old module was
preserved by the source diff. No public Java facade or generic artifact/project
loader has been accepted. Those need admitted metadata, typed entry evidence and
an explicit branch/handle lifetime contract before implementation claims.

Native compilation service extraction, bundled helper/platform distribution,
resource-backed compiled artifacts, StoreManager, one-branch-per-Project reuse,
actual Init completion and generically checked entry evidence remain separate
work. Do not expose the fixed tutorial profile as a generic project loader.
