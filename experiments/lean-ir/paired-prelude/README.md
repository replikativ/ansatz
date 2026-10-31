# Fresh matched Prelude producer

This producer reads the genuine pinned `Init.Prelude` private import closure once.
It exports all five actual ModuleData parts and the exact 2,314 private
ConstantInfo objects through the existing lean4export schema, including unsafe
compiler markers, full theorem/opaque values, hints and complete families.
The native temporary Environment is only the exporter's lookup carrier. An exact pinned private Kernel.Environment layout view carries a genuine
`SMap.fromHashMap` imported constant map; no `finalizeImport`, `addDecl`, proof replay or imported-extension callback runs here.
`mkEmptyEnvironment` runs the registered empty-state initializers for its lookup
carrier; those states are never transported or claimed as guest initialization.

Build from this checkout, using a read-only lean4export source checkout:

```sh
LEAN4EXPORT_SOURCE=/path/to/lean4export experiments/lean-ir/paired-prelude/build.sh
python3 experiments/lean-ir/paired-prelude/run.py experiments/lean-ir/target/matched-prelude-pair
```

The runner refuses existing outputs. A failed directory remains unadmitted and
must be inspected. `pair-audit.json` is written only after exact source/domain/
shape/name/dependency/family audits succeed. `correspondence.json` associates
source private-part root 2 and every original CI array index with its typed Name
and complete canonical checking shape, expressed in the same exporter DAG
indices. `module-file-cohort.json` hashes every actual mapped compiled module
part before and after the run. `build-cohort.json` binds actual helper, exporter,
compiler/shared-library and executable bytes, including a dirty exporter source
hash rather than trusting a checkout revision alone.

This is a producer/module logical correspondence receipt. It does not certify
Java graph normalization, typed scalar ingress, finalization, runtime initializer
coverage, guest associations, local checking, generated IR, or execution. Those
are separate consumers/gates. Existing private record mirrors and graph writer
are copied from the ModuleDataTransport producer and bound by the build receipt;
the temporary lookup-carrier view also mirrors the pinned Kernel.Environment
field order/types and is never transported. Module-part selection follows pinned `ImportedModule.mainModule?`/`getData?`.

Resource use: compiling modules imports Lean and has measured approximately
900 MiB peak RSS; `LEAN_NUM_THREADS=1` serializes compilation. Producer and store
conversion require their own measured resource slots. Python audits cap each
input at 64 MiB and 200,000 records. No JVM is started by build or pair runner.

`typed-scalars.json` binds every source immediate field above INT_MAX to an
actual typed source owner (`Name.num`, `Literal.natVal`, or `IR.LitVal.num`) and
its exact graph node ID, field index and unsigned decimal payload. The source
walker covers complete theorem/opaque bodies (`value? true`) and the genuine
`IR.declMapExt` arrays using pinned CompilerM's export entry type. The independent
audit rejects any missing/extra claim; structural similarity is insufficient.

The root-coordinated retained JVM can load `store_only.clj` and invoke:

```clojure
(matched-prelude.store-only/import! pair-directory new-store-directory
  {:pair-audit-sha256 independently-pinned-digest})
```

This refuses existing store output, requires an explicit expected audit digest
and exact input leaf set, independently checks Java typed/display Name ingress,
uses the existing streaming writer without a testing prefix, and publishes its
format2 manifest last. It returns actual captured branch-root witnesses in the
manifest. It never hydrates an Env or creates derived indexes. A later session
must open and retain the actual store/source leases; a receipt alone is no guest
association authority.

Mutation tests use the actual generated pair and keep source artifacts read-only:

```sh
PAIRED_PRELUDE_FIXTURE=/absolute/path/to/pair python3 -m unittest discover \
  -s experiments/lean-ir/paired-prelude -p 'test_*.py'
```

They cover complete native acceptance and rejection of altered checking bodies,
typed Names, source CI indices, display collisions, missing/changed scalar claims
and signed scalar domains. Native source/build validation and Python tests are
bounded; the repository JVM suite must be run separately under the root's shared
resource coordination. Store import itself is exercised in the retained JVM.
