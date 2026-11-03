# External Lake assessment callers

These authored callers exercise unchanged external dependencies; they are not a
finished launch demo. [provenance.json](provenance.json) pins exact upstream
revisions and source hashes. [validation.json](validation.json) records the
selected preparation/artifact checks and their observational timings. Dependency source and build products are not
redistributed here.

Use a scratch parent directory containing:

- `lean4-cli`: the pinned upstream checkout.
- `fp-lean`: the pinned upstream checkout, including its `examples` package.
- `cli`: a copy of this directory's `cli` caller.
- `fp-sort`: a copy of this directory's `fp-sort` caller.

Build callers explicitly with Lean 4.33.1 before invoking built-workspace mode.
Lake resolves the FP Lean package's pinned Subverso dependency during that build.
The upstream projects' sources and configuration remain unchanged; the callers
select the SDK's supported toolchain and expose monomorphic boundary functions.

`cli` exercises actual argument parsing, positive/negative flags, invalid input
and generic list padding. It deliberately projects parser errors to a String;
it does not expose the library's function-containing command datatype.

`fp-sort` imports the complete upstream insertion-sort module and exposes Nat
array IO functions. The module has array-size and termination proofs; this is
not a claim of a full functional sorting-correctness proof. Sharing diagnostics
are captured, but allocation-dependent trace counts are not equality promises.

The [optional corpus runner](../../lake_corpus.clj) accepts paths to already
built callers, prepares artifacts and checks Java/Clojure-visible behavior.
The [scope guide](../../../LAKE.md) distinguishes preparation, execution and
unsupported large-project boundaries. Demo and article publication follow the
separate launch review.

Each caller includes `Oracle.lean` and captured `native.stdout`/`native.stderr`
from its pinned native reference. Run the CLI oracle with `lake env lean --run
Oracle.lean`; run the sorting oracle with `lake env lean Oracle.lean` (it uses
`#eval` because the imported tutorial already defines `main`). Both native
references use `-M384 -j1` in the recorded check. JVM checks compare values and
IO results rather than allocation-dependent sharing-trace counts.
