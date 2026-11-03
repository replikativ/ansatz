# Pure JVM implementations of Lean functions

This is the candidate FFI API. It is implemented and exercised against a native
Lean reference corpus; release and v4 producer publication are still pending.

A Project can select Java or Clojure implementations of named Lean functions.
The Lean function must be a checked, closed, first-order pure definition marked
`@[noinline]`, with types supported by the v3 datatype boundary. Its ordinary Lean
body remains the reference implementation. Without a registry entry, the JVM
executes that Lean body. Native Lean also executes the ordinary body.

```lean
@[noinline] def normalize (n : Nat) : Nat := n + 1

def pipeline (n : Nat) : Nat := normalize n + normalize 3
```

There is no signature to repeat in the host registry. The native v4 entry
producer observes eligibility and the elaborated signature. Preparation binds
these observations to the original IR, source/module products, exact producer
source closure and executable. Older v3 evidence cannot authorize a binding.
The current v3 native bundle still supports ordinary source loading. Source
preparation for bindings requires the v4 candidate, which is not published yet.
Loading an already prepared artifact requires no native toolchain.

## Java

```java
HostBindings implementations = HostBindings.builder()
    .pure("normalize", "normalize/1", arguments ->
        ((BigInteger) arguments.get(0)).add(BigInteger.ONE))
    .build();

try (Lean runtime = Lean.open();
     InputStream input = Files.newInputStream(artifact);
     LeanProject project = runtime.loadArtifact(input, manifestSHA256, implementations)) {
    Object result = project.call("pipeline", BigInteger.valueOf(41));
    // result is BigInteger.valueOf(46)
}
```

The name is the same bounded dotted declaration name used by `function`/`call`.
The implementation ID is a diagnostic/version label; it is not a code hash or a
purity proof. The argument List is immutable and has the declaration's semantic
arity, including zero. Java uses the existing typed carriers: exact integers,
Boolean, String, immutable containers, LeanData, LeanBytes and the other
[documented value types](VALUE_EXAMPLES.md). Arguments contain no erased proofs,
runtime world parameter, raw guest Nodes or ownership tokens.

`loadProject(directory, options, implementations)` automatically adds binding
names to the native selection. For artifact-only deployment, explicitly select
those names with `ProjectOptions.Builder.function(name)` during preparation.
The combined entry/binding selection remains bounded by 1,024 names.

## Clojure

```clojure
(require '[ansatz.lean.jvm :as lean]
         '[clojure.java.io :as io])

(def implementations
  (lean/bindings
    {"normalize" {:implementation-id "normalize/1" :fn inc}}))

(with-open [runtime (lean/open)
            input (io/input-stream artifact)
            project (lean/load-artifact runtime input manifest-sha256 implementations)]
  (lean/call project "pipeline" 41)) ; => 46
```

Functions receive ordinary positional arguments. Clojure integer results are
normalized through the existing type-directed adapter. Custom datatype inputs
are detached tagged map views, so a record transformation can use
`(fn [message] (update-in message [:lean/fields 0] inc))`.

`lean/bindings` captures each supplied Var's current function value once. Changing
that Var later does not rebind an existing Project. Open a new Project with a new
registry to select another implementation. Transitive Vars, dynamic bindings and
mutable captures remain the application's responsibility.

## Constructing custom results

A function with only primitive inputs may still return a custom Lean datatype.
Use a factory to obtain its constructors from the admitted result type once at
linking; no additional datatype registration is required.

```java
HostBindings.builder().pureFactory("Interop.combine", "combine/1", signature -> {
    LeanType.Constructor constructor = signature.resultType().constructors().get(0);
    return arguments -> {
        String label = (String) arguments.get(2);
        BigInteger count = ((BigInteger) arguments.get(0)).add(
            BigInteger.valueOf(label.codePointCount(0, label.length())));
        return constructor.create(List.of(count, arguments.get(1)));
    };
}).build();
```

Factories receive a detached `HostBindings.Signature` with `argumentTypes()` and
`resultType()`. Clojure uses `:factory` instead of `:fn`:

```clojure
{"Interop.combine"
 {:implementation-id "combine/1"
  :factory
  (fn [{:keys [result-type]}]
    (let [type-id (.get (.nominalId result-type))
          constructor (.name (first (.constructors result-type)))]
      (fn [n enabled label]
        {:lean/type type-id
         :lean/constructor constructor
         :lean/fields [(+ n (.codePointCount ^String label 0 (.length ^String label)))
                       enabled]})))}}
```

All requested declarations and signatures are checked before any factory runs.
Factories run once per Project linking, before guest initialization. The registry
and factories are host configuration and are never stored in an artifact.

## Semantics and limits

The host implementation promises the same pure function as the Lean body. Types
establish representation compatibility, not semantic equivalence. Time, random
state, changing dynamic bindings or mutable state that changes the result do not
fit this contract. Compiler transformations may hoist, specialize or cache pure
calls; callback count and timing are not API guarantees. The pinned corpus tests
direct and boxed calls, closed constant calls, nullary values, List.map and the
audited String.any predicate worker.

This API does not add kernel axioms, import declarations into the Ansatz kernel,
or use host callbacks to admit proofs. Integration with proof mechanisms that
trust compiled evaluation requires a separate policy. Lean itself warns that an
incorrect implementation replacement can invalidate native_decide results;
ordinary kernel reduction and executable replacement are distinct paths.

Unexpected callback or result-conversion failures terminate the Project with
`HostFailure`. They do not select the reference body as a retry. Use a supported
Except result for expected domain failures. Fatal JVM Errors retain their
identity; interruption/cancellation retains the interrupt flag. A failed Project
can be closed, with its stopped packet retired through the audited heap/resource
protocol. External effects are not rolled back.

An unknown, unselected or ineligible declaration is refused before JVM initialization
with `BindingRejected`. Host code runs synchronously under the Project's execution
lease. Same-Project reentrancy, passing Lean functions as host values, IO-typed
host implementations, async callbacks, opaque Java resource handles and public
fork/replay remain follow-up work. Guest instruction budgets do not preempt
arbitrary in-process host work.

The [two-file example](examples/pure-ffi/README.md) and independent application-JAR
[consumer](consumer/PureFFISmoke.java) exercise both directions. The
[implementation contract](FFI_PLAN.md) records the remaining sequence.
