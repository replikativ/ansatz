# Preparing a built Lake workspace

This implementation candidate consumes an already resolved and built Lake
workspace. It does not yet orchestrate dependency fetching or builds. The
prepared artifact runs through the existing Java interpreter and needs no Lake,
native Lean installation or source checkout at deployment.

Use the supported official Lean 4.33.1 toolchain and matching producer bundle.
Resolve and build your project with Lake first. Then select Lake mode explicitly:

```java
ProjectOptions options = ProjectOptions.builder(nativeCompiler)
    .builtLakeWorkspace()
    .rootModule("App")
    .function("App.calculate")
    .function("Domain.credit")
    .build();

try (LeanProject project = runtime.loadProject(workspaceDirectory, options)) {
    Object result = project.call("App.calculate", BigInteger.valueOf(32));
}
```

The same options work with `LeanPreparation.prepareProject` for build-time
artifact production. Clojure uses the existing functions with:

```clojure
{:compiler compiler-options
 :built-lake-workspace? true
 :root-module "App"
 :entries ["App.calculate" "Domain.credit"]}
```

The preparation CLI uses `--source-mode built-lake`; its default remains `local`.
The root is an actual built Lake module, not a filename or package name. Selected
functions may belong to the application or its imported dependencies. Existing
pure/IO [host bindings](FFI.md) work with eligible dependency declarations too.
Lake mode discovers imports itself; `sourceRoot` and manual `installedImport`
overrides are not supported in this mode.

## What preparation does

1. Check the toolchain declaration, existing manifest, materialized package
   directories and locked Git revisions. Path and Git dependencies are supported.
2. Ask pinned Lake to check `+Root:leanArts` with `--no-build --rehash --no-cache`.
   Stale or missing products fail; the SDK issues no build or update command.
3. Read Lake's search path and retire Lake before starting the SDK-owned bounded
   inventory reader directly. It reads compiled import headers, including
   transitive dependency modules, without overlapping two large native heaps.
4. Capture the workspace-owned compiled products unchanged. A generated empty
   import adapter supplies the existing producer context; application and library
   source implementations are not flattened, rewritten or recompiled.
5. Recheck products, optional sidecar absence, configuration and manifest bytes
   around native collection. Bind signatures, origin identities, IR and startup
   evidence into the prepared artifact. Official library products retain the
   existing trusted-toolchain custody policy.

Lake loads trusted configuration and can execute native code. Its own trace or
configuration caches may be updated. This retains the existing trusted-source
preparation contract; it is not an execution sandbox or a package authenticity
verification service. Concurrent rebuilds during collection cause a refusal.

## Scope and limits

The current profile supports Linux x86-64 and the pinned toolchain. The root
`lean-toolchain` must identify that supported release. Dependencies must already
be materialized and the requested root up to date. Package overrides, symlinked
paths and workspace modules shadowing official modules are refused.

The compiled non-Init closure is bounded at 128 modules; product custody, source
cache and artifact byte budgets also apply. Workspace products must live under
the resolved package directories. Successful resolution/building does not widen
runtime support: unsupported initialization, native externs, tasks or primitives
still fail at their documented boundary. Public entry signatures retain the
existing closed first-order type restrictions. Whole-module elaboration does
not imply that every function, path or input is executable or publicly callable.

Forking, live in-place reload, general Lake build orchestration and frontend
self-hosting are separate work. The ordinary source-DAG and older artifact paths
retain their previous scope.

## Validation and external project choices

The authored [two-package fixture](test/fixtures/lake-workspace/README.md) covers
cross-package calls, a dependency initializer and datatype, optional host binding,
stale and missing products, dependency rebuild/cache invalidation and collection
mutation. Its prepared Java/Clojure consumer runs without source/native tools.
The [native runner](test/lake_acceptance.clj) works on a fresh owned copy. CircleCI's
`test-lean-jvm-native` job installs hash-pinned Lean and producer archives, builds
this fixture and the pinned external callers, runs native references, and checks
fresh preparation plus Java/Clojure artifact execution against the exact SDK JAR
retained by `test-lean-jvm-sdk`. Both deployment jobs require this gate. The test
harness explicitly builds its fixtures; the SDK's no-build policy is unchanged.
Logs and the acceptance report are retained as CI artifacts. See
[the runner](../../bin/lean-jvm-native-ci) for local reproduction with supplied
native tools; the runtime/preparation namespaces must come from the SDK JAR.

The [external corpus](test/fixtures/lake-corpus/README.md) records upstream pins
and separate caller adapters. Current observations:

| Project / selected workload | Native build | JVM preparation and execution | Boundary |
| --- | --- | --- | --- |
| Functional Programming in Lean: insertion sort | Passed with unchanged upstream module | Nat array sort and sort-plus-original passed | Separate monomorphic IO adapters; upstream size and termination proofs, not a full sorting-correctness proof |
| lean4-cli, compatible upstream tag | Passed with unchanged library | Flag parsing, invalid input and list padding passed | Selected pure adapters; not a claim that all commands, handlers or IO services work |
| Local mcmc-lean: executable two-state example | Existing build inspected read-only | Outside this bounded campaign | Its recorded Lake setup has 3,279 import artifacts, beyond the 128-module profile; no full Mathlib image was loaded |

I recommend the FP Lean workload for the first tutorial article, with lean4-cli
as a second compatibility example. Mathlib-heavy projects remain a useful demand
signal and later coverage target. These observations establish selected behavior,
not performance parity or compatibility with arbitrary Lean projects.
