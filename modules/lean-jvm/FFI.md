# JVM host bindings for Lean

This API connects checked Lean declarations to Java or Clojure functions,
using the existing [value boundary](VALUE_EXAMPLES.md). Its matching native producer is
[published and verified](producer/README.md#host-binding-producer). Loading a
prepared artifact needs no native toolchain.

## Declaring a host import

Use a standard extern with an explicit `ansatz_jvm_` symbol:

```lean
@[extern "ansatz_jvm_length"] opaque length : String → Nat
@[extern "ansatz_jvm_read_config"] opaque readConfig : String → IO String
```

The marker opts a declaration into this bounded JVM binding profile. Only a sole
standard all/C extern with that prefix is admitted; arbitrary package externs do
not acquire binding authority. The registry uses the Lean declaration name,
such as `length`, rather than the native symbol. There is no automatic case conversion:
`readConfig` and `ansatz_jvm_read_config` are independent explicit names. A
namespaced declaration uses its full Lean name, for example `App.readConfig`. Signatures must be closed,
first-order and supported by the datatype boundary. A custom datatype used by a
bodyless declaration may need `deriving Inhabited` for Lean to construct its safe
opaque placeholder.

Every required import must have a matching registration. Missing bindings and wrong effects fail with `BindingRejected`; unsupported
signatures are rejected during entry preparation/admission. These checks precede
guest initialization and implementation factories. A safe opaque
inhabitant placeholder is not an executable fallback. Native execution of these
imports requires an actual native implementation.

For an optional replacement with an executable Lean fallback, retain a reference
body:

```lean
@[noinline] def normalize (n : Nat) : Nat := n + 1
@[noinline] def referenceRead (key : String) : IO String :=
  pure ("reference:" ++ key)
```

Without a registration, the JVM executes that body. Native Lean also executes
the reference body. Both pure and IO reference replacements are supported.

## Registering Java functions

```java
HostBindings implementations = HostBindings.builder()
    .pure("length", "length/1", arguments -> {
        String text = (String) arguments.get(0);
        return BigInteger.valueOf(text.codePointCount(0, text.length()));
    })
    .io("readConfig", "config/1", arguments -> {
        String key = (String) arguments.get(0);
        if (key.isEmpty()) throw LeanIOError.userError("Empty configuration key");
        return "configured:" + key;
    })
    .build();

try (Lean runtime = Lean.open();
     InputStream input = Files.newInputStream(artifact);
     LeanProject project = runtime.loadArtifact(input, manifestSHA256, implementations)) {
    // Call an admitted Lean entry that uses these imports.
}
```

The native producer derives the logical signature, effect and actual runtime ABI;
the registry does not repeat them. The implementation ID is a diagnostic/version
label, not a code hash or purity proof. Arguments are an immutable List of the
declaration's semantic arguments, including zero arguments. Erased proofs and
the IO world parameter are absent. An IO implementation returns its ordinary
payload; the adapter constructs the Lean IO result.

`loadProject(directory, options, implementations)` automatically selects registered
names. When preparing an artifact separately, explicitly select import and
replacement names with `ProjectOptions.Builder.function(name)`. The combined
entry/binding selection is bounded by 1,024 names. Source preparation requires
the matching host-binding producer; older producer evidence cannot authorize bindings.

For custom results, `pureFactory` and `ioFactory` receive a detached
`HostBindings.Signature` once during linking. Derive constructors from
`argumentTypes()` or `resultType()` without an additional datatype registration:

```java
HostBindings.builder().pureFactory("HostInterop.makeMessage", "message/1", signature -> {
    LeanType.Constructor constructor = signature.resultType().constructors().get(0);
    return arguments -> constructor.create(List.of(arguments.get(0), arguments.get(1)));
}).build();
```

Factories run only after the complete selection passes admission, before guest
initialization. Registries and factories are host configuration, never artifact
contents.

## Registering Clojure functions

```clojure
(require '[ansatz.lean.jvm :as lean])
(import '[ansatz.lean.jvm LeanIOError])

(def implementations
  (lean/bindings
    {"length" {:implementation-id "length/1"
               :fn (fn [^String text] (.codePointCount text 0 (.length text)))}
     "readConfig" {:implementation-id "config/1" :effect :io
                   :fn (fn [key]
                         (if (empty? key)
                           (throw (LeanIOError/userError "Empty configuration key"))
                           (str "configured:" key)))}}))
```

`:effect` defaults to `:pure`; use `:io` for an IO declaration. Functions receive
ordinary positional arguments and return the existing Clojure value carriers.
Custom inputs use detached tagged map views; for example,
`(fn [message] (update-in message [:lean/fields 0] inc))`. Use `:factory` instead
of `:fn` to receive `{:argument-types [...] :result-type ...}` once at linking.
The Java builder also offers `pureClojure`, `ioClojure` and their `Factory` forms.

## Semantics and failures

A pure host implementation promises purity and, for a reference replacement,
equivalence to the Lean body. No proof is required or inferred from Java typing.
Time, randomness or mutable state that changes the result violates that promise.
Compiler transformations and closed-value caches can move or share pure work;
callback count and timing are not API guarantees. IO bindings express synchronous
effects through Lean's IO sequence. Guest instruction budgets do not preempt
arbitrary in-process host work.

Each Project captures its callable targets once. Capturing a Clojure Var freezes
its current function value, not transitive Vars, dynamic bindings or mutable
captures. Open a new Project to change implementations. There is no live rebinding
or automatic retry.

An IO binding may throw `LeanIOError.userError(message)` or
`LeanIOError.unexpectedEof()`. The adapter returns the corresponding Lean IO error,
which Lean `try`/`catch` can handle. Clojure throws the same Java error values.
There is no implicit mapping from arbitrary Java exceptions to Lean errors.
Unexpected callback or conversion failures terminate the Project with
`HostFailure`; they do not retry a reference body. Fatal JVM Errors retain their
identity and cancellation preserves interruption. Close a failed Project;
external effects are not rolled back. Expected pure domain failures can use a
supported `Except` result.

Bindings add no kernel axioms, equations for opaque declarations, or proof
admission. Ordinary kernel reduction and executable implementation replacement
are distinct. Trusting compiled evaluation for proofs requires a separate policy.

Async callbacks, opaque Java resource handles, same-Project reentrancy,
function-valued arguments and public fork/replay are outside this profile.

## Implementation safety and examples

The publisher authenticates declaration/product identity, logical types, effect,
original Header and lowered ABI before creating a callback plan. The runtime
matches the actual pending request and descriptor by identity, exports detached
values, freezes object storage and validates the result against the admitted
type before resuming. Borrowed/owned input handling retains the existing ownership
protocol; host functions receive no guest Nodes, engines or ownership tokens.
Failure retires the actual stopped packet without replay or guessed cleanup.

The [reference example](examples/pure-ffi/README.md) includes an independent native
oracle. The [foreign-import example](examples/foreign-ffi/README.md) covers bodyless
imports and synchronous IO. Their prepared application-JAR consumers exercise the
SDK independently of source directories and native tools. See the
[release checks](RELEASE_CHECKLIST.md) for acceptance and publication gates.
