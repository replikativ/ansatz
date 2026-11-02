# Multi-file tutorial on the JVM

The first compatibility example is the unchanged three-file `first-lake/expected`
project from [Functional Programming in Lean](https://github.com/leanprover/fp-lean/tree/0abeea545d560a324e2561f7210fbd6ed154fa02/examples/first-lake/expected).
`Main.lean` imports `Greeting.lean`, which imports `Greeting/Basic.lean`. The Java
API captures and compiles that import graph, checks the requested `main : IO Unit`
with native Lean, then initializes and executes its code in the JVM interpreter.
Calling `runMain` twice reuses one Project and returns separate output strings.

Use revision `0abeea545d560a324e2561f7210fbd6ed154fa02` of
`https://github.com/leanprover/fp-lean`. Pass its
`examples/first-lake/expected` directory as the first argument to
[RunTutorial.java](RunTutorial.java). The source files need no edits. This profile
uses the explicitly supplied Lean **4.33.1** installation, rather than asking
Lake to install the tutorial checkout's toolchain.

Resolve the optional SDK and its normal Maven dependencies as described in the
[SDK guide](../README.md). With their JARs on `CLASSPATH`, a JDK 17 source launcher
can run the example:

```sh
java --class-path "$CLASSPATH" RunTutorial.java \
  "$FP_LEAN/examples/first-lake/expected" \
  "$LEAN_SYSROOT" "$PRODUCER_BUNDLE" "$COMPILER_CACHE"
```

The expected output is `Hello, world!` on two lines. The
[producer bundle](../producer/README.md) has a separate verified download; supply
its extracted directory explicitly. Automatic installation is not part of this
first profile.
The application does not run a separate exporter or preprocessing command.
Native source compilation can execute compile-time IO and is for trusted sources.
After compilation, reusable artifact loading can run without the native toolchain;
the [application-JAR consumer](../consumer/README.md) demonstrates that mode with
the original Ansatz interop example.

This is a small compatibility corpus, not general Lake compatibility.
The supported source profile covers Init and local acyclic imports. Std, Lean,
Mathlib, external dependencies, modern `module` headers, arbitrary native bindings,
and hosting the Lean frontend itself remain outside this profile. Java entry
execution also does not import these definitions or their proofs into the Ansatz
kernel or DSL environment.

The upstream tutorial is by David Thrane Christiansen and the Functional
Programming in Lean contributors, with Microsoft and Lean FRO attribution as
recorded in its pinned README. Consult the upstream licensing information; this
example links to its source and does not relicense or redistribute the tutorial
as Ansatz code. The SDK's own bundled example is original Ansatz code; Lean
runtime/Init provenance is recorded in its NOTICE.

The [acceptance receipt](acceptance.json) identifies the tested candidate SDK
bytes and observed Java launch. Later packaging/CI receipts identify release
bytes separately; neither receipt broadens the supported source profile.

## Clojure and Superficie

For the general-call API, add the optional SDK to your Clojure
classpath. Core Ansatz may be included in the same REPL. Set `LEAN_TUTORIAL`
to the pinned tutorial directory above and set the same three compiler variables
used in the Java command. This selection uses the legacy checked `IO Unit`
profile, which works with both admitted v1 and v2 producer bundles.

```clojure
(require '[ansatz.lean.jvm :as lean])

(def options
  {:compiler {:sysroot (System/getenv "LEAN_SYSROOT")
              :producer-bundle (System/getenv "PRODUCER_BUNDLE")
              :cache (System/getenv "COMPILER_CACHE")}
   :root-module "Main"
   :entries {"main" :io-unit}})

(with-open [runtime (lean/open)
            project (lean/load-project runtime (System/getenv "LEAN_TUTORIAL") options)]
  (lean/call project "main"))
```

The returned value is `{:value nil :stdout "Hello, world!\n" :stderr ""}`.
The Clojure wrapper converts the IO result to ordinary Clojure data; the Java
example above accesses the same captured output through its Java carrier.
`with-open` closes the Project before its owning runtime.

Superficie renders the same Clojure forms as:

```superficie
require('[ansatz.lean.jvm :as lean])

def options: {:compiler {:sysroot System/getenv("LEAN_SYSROOT"),
                         :producer-bundle System/getenv("PRODUCER_BUNDLE"),
                         :cache System/getenv("COMPILER_CACHE")},
              :root-module "Main", :entries {"main" :io-unit}}

with-open [runtime lean/open(),
           project lean/load-project(runtime,
                     System/getenv("LEAN_TUTORIAL"), options)]:
  lean/call(project, "main")
end
```

Superficie supplies the surface notation. The call still uses the Clojure API
and the same Java interpreter, codecs and checked Lean entry. The source-loading
example needs the explicitly configured native frontend; an application loading
a [prepared artifact](../PREPARATION.md) only needs the JVM dependencies.

The original acceptance receipt above covers the Java tutorial launch. The
Superficie form round trip is checked separately; execute this Clojure tutorial
example against the final released SDK as part of launch validation.
