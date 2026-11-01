# Closed hosted application consumer

The optional seventh compatibility profile is
`ansatz-producer50f-hosted-application-consumer/1`, constructed with
`globals-consumer-factory/make-hosted-application-factory`. It retains the
producer50f archive/recipe provenance separately from the loaded consumer code.
This is experimental source-level compatibility infrastructure, not a released
Lean frontend package or full application acceptance claim.

Its runtime member domain contains exactly 260 rows: the sixth profile's 257
plus `binding_dependencies.clj`, `source_inductive_preparation.clj` and
`typed_eio.clj`. The existing three Project caller resources are a separate
inventory; Project invocation and failure-disposal changes update that caller
identity without adding runtime members. A trusted fresh launcher must verify
actual selected resource/class paths and bytes, class CodeSource, and absence of
Clojure AOT shadows before loading project namespaces. Disk hashes alone do not
attest already loaded Vars.

The seventh profile pins eight reviewed original-member substitutions:
`kernel_host.clj`, `raw_interop.clj`, `resident_frontend.clj`; Java sources
`Expr.java`, `ExprStore.java`, `TypeChecker.java`; and compiled `Expr.class` and
`TypeChecker.class`. The Java cohort removes local expression-address equality
from pointer comparison. Old/corrected source or class mixing rejects even when
the caller recomputes a whole-inventory digest. Existing reconstruction additions
and permitted substitutions retain their externally accepted whole-digest pins.
The first six profile inventories and their source/class validation rules remain
unchanged; callers cannot provide an extra substitution policy.

The newly compiled class cohort has the same 47 member IDs as its pre-fix build,
plus the separately unchanged `TypedLongMemo.class` member. Field, method and
class descriptors match the historical selected classes. Descriptor equality is
not a behavioral equivalence claim. The three HeapOverlay class bytes also
change because the fresh build targets classfile version 55, whereas those
historical files used version 69; their source bytes are unchanged. Every actual
class byte remains independently pinned. This does not establish a minimum JVM
version for the full library.

The [focused validation record](../measurements/hosted-application-consumer.json)
reports **81 tests / 3,480 assertions** across compatibility, bootstrap, archive,
normalization and fixed native-readiness provenance regressions. Archive/compiler
transport in those factory checks is modeled; tiny Source identity and handler
provenance are real. The run used corrected Java classes, a 384 MiB heap and
768 MiB process-group RSS cap, and verified all 775 input pins after process
disposal. It performs no full hosted frontend restore or strict Init check.

The seventh factory authenticates two distinct class domains. Original archived
producer class files remain hashed against the original build inventory; its
resolver must provide every producer row, including all 42 kernel class files.
Actual loaded classes use the fixed corrected Expr/TypeChecker pins while all
other kernel classes keep their original pins. The legacy six profiles retain
their original loaded-class policy. A valid corrected class cannot hide damaged
producer bytes, and resolved disk files cannot substitute for loaded identity.

A genuine fresh constructor passed with all 260 runtime resources, three caller
resources and 11 public caller operations. It acquired no native leases and
performed no archive invocation, guest step, strict check, readiness issuance or
Project operation. All 1,508 input pins matched after process disposal. This gate
is separate from another actual archive restore. After that restore, ordinary
inductive preparation and EIO
builder linking must precede graph/evaluator sealing, with independently trusted
helpers and actual sessions sharing exact binding/function objects. Neither
source membership nor this factory authorizes those later operations by itself.
