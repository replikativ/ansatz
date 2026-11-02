# Explicit native producer bundle

The maintained native helper sources live in
[tools/lean-producer](../../../tools/lean-producer/README.md). This directory owns
bundle descriptors and release/packaging records; it is not a second helper
source tree. Descriptor source paths refer to the extracted bundle's layout.

Precompiled artifact execution needs only the optional SDK and its ordinary
Maven dependencies. Trusted source compilation additionally needs an explicit
official Lean installation, writable compiler cache, Linux `prlimit`, and an
independently supplied native producer bundle. Compilation can execute native
metaprograms and compile-time IO. It is not a sandbox.

The initial bundle profile is Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, target
`x86_64-unknown-linux-gnu`, 64-bit words. Its data-only
`producer-bundle.json` follows [the example](producer-bundle.example.json).
Each of the three helpers includes its original Lean source. The SDK pins the
six hashes independently and validates bounded regular files, path containment,
source bytes and executable bytes. A supplied hash or claimed version alone
cannot authorize another helper. Stripping or rebuilding a binary changes its
identity and requires a separately reviewed producer cohort.

The bundle is outside the runtime JAR. No helper binary, Lean sysroot, source
checkout, Python or Clojure CLI is a runtime dependency of precompiled artifact
loading. The source service invokes these three native helpers itself; Java
callers do not run a separate exporter command. The retired fixed tutorial
exporter is not required by the canonical source service.

## General-call v2 producer

General signature discovery (`ProjectOptions.Builder.function`) requires the v2
entry helper. Its [published descriptor](producer-bundle-v2.example.json) also
pins a diagnostics-aware typed source helper: warnings and informational frontend
messages remain on stderr, while stdout is structural JSON. Compiler errors still
fail. Diagnostics bytes remain bounded, hashed and included in cache/artifact
provenance; they are not ignored or parsed as declarations.

The v2 producer admits up to 1,024 explicitly selected host functions,
subject to the separate request-byte and IR/artifact budgets. Previous helper
cohorts retain their 16-entry preparation limit; previously prepared artifacts
remain loadable. Function arity has a separate bound of 64 arguments.

The maintained sources are
[NativeGeneralEntryEvidence.lean](../../../tools/lean-producer/src/NativeGeneralEntryEvidence.lean),
[NativeStartupEvidence.lean](../../../tools/lean-producer/src/NativeStartupEvidence.lean)
and [TypedSourceExport.lean](../../../tools/lean-producer/src/TypedSourceExport.lean).
The [frozen v1 entry source](../../../tools/lean-producer/legacy/NativeEntryEvidence.lean)
remains compatibility evidence. Moving these files does not change admitted
source/binary pairs; rebuilding or editing a helper requires cohort admission.

The v2 archive is published in ansatz-stores and its public download has been
verified against the [recorded archive hash](candidate-v2.json). The SDK admits a
producer binary with its exact source/binary pair; mixing independently valid
hashes is rejected. The v1 bundle remains supported by the current SDK for explicit
legacy `natFunction`, `stringFunction`, and `main` requests. SDK releases before `0.2.580`
require the [v1 bundle](https://github.com/replikativ/ansatz-stores/releases/tag/lean-native-producer-4.33.1-v1);
it does not admit the newer v2 producer cohort.

## Published Linux bundle

The independently verified bundle is published in the
[Lean native producer 4.33.1 v2 release](https://github.com/replikativ/ansatz-stores/releases/tag/lean-native-producer-4.33.1-v2).
It is 156,010,308 bytes; its SHA-256 is
`3f5e229791eb49a41cb705ef78446ec0e1b3dcfdc64e58eeebd96152f3aeb56a`.
The release server reports the same uploaded byte size and digest.

On the supported Linux x86-64 profile, download and verify it, then extract into
a new empty directory. Extraction needs tar with zstd support:

```sh
curl --fail --location --output ansatz-lean-native-producer.tar.zst https://github.com/replikativ/ansatz-stores/releases/download/lean-native-producer-4.33.1-v2/ansatz-lean-native-producer-4.33.1-linux-x86_64-v2.tar.zst
printf '%s  %s\n' '3f5e229791eb49a41cb705ef78446ec0e1b3dcfdc64e58eeebd96152f3aeb56a' 'ansatz-lean-native-producer.tar.zst' | sha256sum --check
mkdir lean-native-producer-4.33.1-v2
tar --zstd -xf ansatz-lean-native-producer.tar.zst -C lean-native-producer-4.33.1-v2
```

`producer-bundle.json` is at that directory's root, alongside `bin/`, original
producer sources and license/notice files. Pass this extracted directory as
`NativeCompilerOptions.producerBundle`, together with the explicitly installed
official Lean 4.33.1 sysroot at the pinned commit and a writable cache directory.
The SDK checks the actual source and executable bytes again before use. It does
not download or install this bundle automatically. The reviewed binaries contain
debug information and remain outside Maven runtime dependencies.
