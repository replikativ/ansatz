# Synchronous typed EIO callbacks

`prototype.typed-eio/controller` adapts an explicitly admitted application extern
with the pinned Lean 4.33.1 `String → EIO String String` ABI. The service receives
an immutable host String and returns exactly `{:ok text}` or `{:error text}`.
Declared errors are ordinary Lean results; thrown JVM exceptions retain their
original cause and the raw runtime's canonical World/session diagnostics.

```clojure
(require '[prototype.typed-eio :as eio]
         '[prototype.project-loader :as project])

(def service
  (eio/controller
    {:signature eio/signature
     :builders {:ok ["str" ["str" ["anonymous"] "EIOResultBuilders"] "success"]
                :error ["str" ["str" ["anonymous"] "EIOResultBuilders"] "failure"]}
     :fn (fn [text] {:ok (str "service:" text)})}))

;; After independently linking/protecting the builder functions and admitting
;; (:binding service) under "ansatz_app_eio_text" in a fresh application prefix:
((:invoke! service) 1
  #(project/invoke-io loaded-project module exported-name ["λ 🦉"]
     {:arguments [:string] :result :string}))
```

The returned call owns a new Project, which the caller must close or retain.
The service controller neither creates a prefix nor authenticates helper code.
Its binding declares both helper roots for independent resident protection. It
checks the exact emitted two-parameter allocation bodies and runtime parameter
types before external effects; a missing or changed helper fails early. This is
an intentionally narrow initial profile rather than arbitrary EIO error codecs.

`invoke!` supplies a same-thread, nonreentrant callback allowance from 1 to 1024.
No permission exists during elaboration/compilation. Permission remains busy
through result encoding, helper execution, envelope validation and input release.
A failure after claiming permission poisons the remaining allowance. Exiting the
scope removes it even on exceptions. A new explicit invocation/fork can perform
effects again; this is not a global exactly-once protocol or an IO transaction.

The actual guest builders transfer an independently encoded String into
`EST.Out.ok` or `.error`. After checking the envelope, the adapter releases its
owned input occurrence once; persistent RC-zero and native inputs follow the
machine's existing ownership rules. Partial failures retain explicit input,
payload and result-owner stages. During helper failure the outer raw checkpoint
remains authoritative; the adapter does not substitute an older snapshot or
guess whether an in-flight payload has transferred. No automatic cleanup or
rollback follows an unknown failure.

The fixtures in [typed-eio](../fixtures/typed-eio/provenance.json) are actual native
exports from the pinned toolchain. Both have empty initialization action lists.
The tests lower those bytes and execute the real `run`, `handled` and `twice`
wrappers on reference, mutable and JVM backends. They cover Unicode, success,
handled/unhandled domain errors, both sequenced callbacks, managed/persistent
input ownership, scope/reentry denial and canonical JVM failure diagnostics.
The actual Lean `run` wrapper constructs `IO.Error.userError`; the host adapter
does not duplicate that representation.

These tests establish the local IR/adapter path. Genuine source loading with a
fresh hosted application prefix and public `Project.invoke-io`, including failure
disposal, remains a separate campaign gate. No async, generic FFI or production
performance claim follows from this slice.

The [focused validation](../measurements/typed-eio-host-values.json) passed 28 tests /
642 assertions with a 384 MiB heap, about 449 MiB peak group RSS and all 711 input
hashes unchanged after process disposal. The prior 27-test run passed before the
additional poisoned-permission regression.
