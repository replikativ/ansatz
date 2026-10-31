# Native entry-type and bridge evidence

This is an isolated backend gate, not a public API or Java checking certificate.
The accepted Export.lean, native tutorial service and fixed six-row runner stay
unchanged. A separate opt-in NativeEntryEvidence tool inspects the actual compiled
module `.olean` under the same trusted pinned native toolchain. The build service
must bind its tool/request/output hashes to the source, `.olean`, per-module local
IR and original initialization-plan captures before consuming its result.

The original compiler APIs establish the selection:

- `Declaration.lean:ConstantInfo` supplies actual kind, type and universe params.
- `Meta.isDefEq` in the actual imported Environment compares a closed monomorphic
  type with built-in IO Unit/Nat→Nat/String→String templates. The native process
  computes this equality; a caller signature tag is only a request.
- `Compiler/IR/CompilerM.lean:145-170` exports the original interpreter's raw and
  boxed declaration lookup. The boxed lookup uses the base constant's module
  index, then actual module IR entries. The tool calls these actual exported
  functions; it does not append a suffix and guess that a bridge exists.
- `LCNF/ExplicitBoxing.lean:34-89` generates owned boxed bridges, including void
  world arguments. For example actual main._boxed has tagged owned→object, while
  raw main is void owned→object. Those are different original declarations.

## Requests and output

`--entries REQUESTS.json` imports the real compiled module and exports a
new `lean-native-entry-evidence/1` JSON object. Request schema is
`lean-native-entry-requests/1`, with a structured `module` Name and one to sixteen entries, each containing an
exact structured Name and a signature tag `io-unit`, `nat-to-nat` or
`string-to-string`. Numeric Name components are decimal strings in UInt64 range;
they never come from display-name parsing.

For each selected constant the output carries actual CI kind/level parameters,
bounded complete structural type, expected type and the actual native DefEq
check's algorithm/transparency. Open universes/metavariables, unsafe/partial
entries, extern/implemented-by entry redirects, non-definition/opaque kinds and
unsupported ABI shapes reject. Regular and builtin IO Unit initializer functions
are explicitly rejected as entries and annotated on dependency rows; they cannot
masquerade as ordinary main merely because getInitFnNameFor? returned none. Type metadata is preserved; syntax-valued mdata
is an explicit initial unsupported frontier rather than silently dropped.

Partial source definitions become opaque CIs, so `ConstantInfo.isPartial` alone
does not establish this policy. The helper also calls the original compiler's
`LCNF.declIsNotUnsafe`, which checks the actual unsafe-recursive implementation
for an opaque declaration. The native negative fixture caught and verifies this
distinction.

The output includes both raw and selected callable Names/ABIs. Prefer the actual
interpreter boxed lookup result when present; otherwise admit the actual raw
declaration only when it is already one owned boxed argument/result. Every
selected declaration is retained from the actual base-index lookup in an exact-name
forced map (not re-looked-up via its generated name), and its full static FAP/PAP closure are exported with exact
IR, compiler runtime role/initializer metadata, actual module provenance and
redirect associations. Missing declarations reject. Dynamic AP is reported and
never described as complete dynamic closure.

Rows read after importing `.olean` are not source-local rows from a live source
compilation. Record their actual compiled-module origin. The `.olean` does not
retain the compiler's original all-local declaration order, so this tool does not
manufacture an initialization plan. Original per-module plans must come from the
unchanged source-phase exporter. Initialized dependency roles remain present and
require a separate runtime binding/initialization policy before execution.
The additional ordered initializer-attribute inventory preserves actual regular
and builtin module/IR entries, including anonymous targets. It is not an execution
receipt or a reconstructed source-local initialization plan. The existing
`isIOUnitInitFn` source predicate already includes builtin IO Unit initializers.

Bounds: 64 KiB requests, sixteen entries, type depth128/8192 nodes/128KiB text per
type, 2048 declarations, bounded IR depth/work and 16MiB final output. The native
process retains the existing external RSS/wall/CPU/output supervision. Argument
or unsupported-profile failure publishes no successful evidence object.

## Ordinary project discovery

`--header SOURCE` uses actual `Parser.parseHeader` and
`Elab.HeaderSyntax.imports`, preserving requested import flags, implicit ordinary
and meta Init requests, module-system mode and parser byte position (line-ending normalization is explicitly disabled). It rejects
actual header errors. It does not compile/evaluate the body or infer imports with
a regex. A build service can select captured source files, discover exact typed
dependencies and compile `.olean`s in dependency order before requesting entry
evidence. Source digests/paths remain bound by its actual process receipt.
The initial exact-byte profile rejects CRLF headers rather than normalizing them
and returning an offset into different bytes. LF ordinary/module/quoted imports
were exercised. Supporting normalized files with an original-byte offset map is
a separate extension.

## Consumer gates and tests

A new consumer must require an actual trusted native build invocation or pinned
artifact receipt for this tool version, not accept a caller-made equality map.
It verifies typed Names, CI type, template/check profile, exact raw/selected ABI,
exact declaration IR/ABI and compatible role/initializer metadata against any
existing source export (whose source-local provenance has a different scope), module/source provenance,
initialization requirements and current runtime capabilities. Canonical Headers
are reserved before bodies, and typed handles bind the exact prepared Header,
source/cohort and ProjectVersion. No Headerless extension or raw-ABI type proof.

Required native gates: IO Unit main with real tagged world bridge; Nat and String
identities including an actually borrowed raw worker; aliases accepted by native
DefEq; wrong signature, universe-polymorphic, unsafe/partial, missing-name and
unsupported-kind negatives; actual numeric/string Name distinction; transitive
imports and source initialization metadata consistency. Compare exported selected
IR against actual original compiler rows, then execute through the explicit
budgeted Java driver separately. No native/JVM run is claimed by this design.

The implementation is NativeEntryEvidence.lean with an independent research build
script; Export.lean remains byte-identical SHA
3311d15c99dc91b599771e328475f2a65a70a0c4fe4c71bfe82b1c2883499f95.
The coordinated native gate compiled the helper and all three fixture modules.
Eight requested entries passed, including imported aliases; their actual raw and
selected callable IR matched unchanged source-phase exports. Nat and String raw
workers were genuinely borrowed; the original lookup selected owned bridges.
Fourteen negative requests rejected with their expected diagnostics, including
partial definitions, wrong types, unsupported kinds, numeric/string Names, and
named/anonymous regular/builtin initializers. A separate ordinary IO entry allowed
inspection of the original initializer inventory.

Typecheck and all runtime/export processes retained the 900 MiB group RSS and
2 GiB available-memory floor. Static linking required a separately authorized
1.3 GiB group bound: final standard `leanc -O2 -rdynamic` link peaked at
1,072,716 KiB. The final typecheck peaked at 918,308 KiB and request execution at
317,540 KiB. Earlier failed typechecks, resource-stopped links and the caught
partial-definition gap remain in the raw gate journal. No JVM was launched or
typed handle executed in this worker gate. `entry-evidence-validation.json`
records portable byte pins and the boundary of this result.
