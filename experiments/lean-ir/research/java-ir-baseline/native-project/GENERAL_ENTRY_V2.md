# Opt-in native entry evidence v2

Implementation candidate:
`experiments/lean-ir/lean/NativeGeneralEntryEvidence.lean`.
The accepted v1 producer source and binaries remain unchanged. This candidate
has not been compiled or executed by its source author. Native production,
source comparison, codec/lifetime integration and documentation review are
separate gates; no merge or publication is authorized by this document.

## Request and descriptor

The new executable accepts `--entries REQUESTS.json`. The request has exactly
`schema`, `module` and `entries`; each entry has exactly `name`:

```json
{
  "schema": "lean-native-entry-requests/2",
  "module": ["str", ["anonymous"], "Main"],
  "entries": [{"name": ["str", ["anonymous"], "combine"]}]
}
```

The actual imported ConstantInfo determines the descriptor. The caller supplies
no accepted flag, type, arity or erased ABI hint. The descriptor has exactly the
root prototype's three keys:

```json
{
  "arguments": [{"kind": "nat"}, {"kind": "int"}],
  "result": {
    "kind": "option",
    "element": {
      "kind": "product",
      "first": {"kind": "bool"},
      "second": {"kind": "string"}
    }
  },
  "effect": "io"
}
```

Primitives are `nat`, `int`, `bool`, `string`, `unit`; product uses `first` and
`second`; option/list use `element`. Bounds are at most 64 explicit arguments,
type depth strictly below 32 and 512 total descriptor nodes across all argument
and result trees. The native Expr encoder has a separate bounded depth of 256,
so a long argument telescope and nested result do not silently reduce those
independent descriptor limits. Existing byte, IR, Name and output bounds remain.

The native classifier probes for `IO payload` before reducing another forall.
This prevents IO's internal world arrow from becoming a user argument. It then
normalizes supported value types in the native Meta context. It reconstructs a
closed canonical type using anonymous default binders, Prod universe arguments
`[zero, zero]`, Option/List `[zero]`, and the original Unit/IO abbreviations. An
actual default-transparency `Lean.Meta.isDefEq` checks the whole original type
against that reconstruction. Both actual and expected Exprs are exported.

Only explicit, nondependent, closed monomorphic value binders are admitted.
Implicit/instance binders, proofs, type formers, open/dependent types, higher-order
data, arbitrary user records, other effects, unsafe/partial entries, externs,
redirects and explicitly initialized entry bindings fail explicitly. Erased
proof arguments are never fabricated as a zero token. Initialized entry bindings
retain v1's refusal pending a distinct checked constant-load policy.

## Actual callable and output

Output schema is `lean-native-entry-evidence/2`, producer
`NativeGeneralEntryEvidence.exportEntries`. Each entry retains v1's original
ConstantInfo identity/module and raw/callable ABI evidence, plus:

- `typeCheck.signature`: the structured descriptor above.
- `typeCheck.algorithm`, `transparency`, `expectedType`: actual native DefEq facts.
- `semanticArity`: public argument count.
- `runtimeArity`: public arguments plus one internal world for IO.
- `argumentPlan`: ordered user-argument indexes, then canonical IO world when needed.
- `resultABI`: ordinary boxed lane or the specific raw-nullary-Bool UInt8 case.
- `codecWitnesses`: actual persisted compiler constructor-layout observations.

The original C interpreter lookup functions are retained. The boxed lookup uses
its base-name module index; no suffix heuristic or local replacement getter
establishes imported lookup authority. The exact returned declaration is forced
into closure export instead of re-looking up a generated name through a different
visibility path. Callable parameters must have exact runtime arity, owned borrow
flags and object/tobject/tagged lanes. Nullary raw object/tobject/tagged results
are accepted; nullary Bool may additionally use raw UInt8. No underapplication,
overapplication or arbitrary closure-returning ABI is inferred from source arity.
A mismatch is `UnsupportedCallableABI`.

The original interpreter itself supports broader `call_boxed` behavior, including
nullary loads and over/underapplication; this direct exact-arity profile does not
claim that entire API. Static dependency closure, startup evidence and the positive
runtime capability profile remain independent requirements. A supported signature
is not a claim that every operation in its body is implemented.

## Layout witnesses and staged codecs

`codecWitnesses.families` deduplicates all Prod/Option/List families appearing in
the arguments/results, plus `EST.Out` for IO. For each, the helper exports actual
`nameToImpureType`, `hasTrivialImpureStructure?`, `getCtorLayout`, constructor
index/object/USize/scalar extents, and each field's actual storage/index/offset.
These are native compiler metadata bound to the producer/source cohort. They do
not authorize callers to construct Nodes or mark an arbitrary graph safe.

Initial execution work should use primitive arguments and primitive/container
results. Int uses the engine's existing mathematical signed carriers, not an
`Int.ofNat`/`Int.negSucc` Node encoding. Bool/Unit need exact scalar codecs, not
truthiness or null. Output trees must be copied into immutable host values while
the real root result remains owned, with bounded depth/nodes and cycle checks;
release that root once after successful decoding. IO's actual EST.Out envelope
owns its payload. No borrowed payload escapes before its wrapper is retired.

Container inputs are a later owned-allocation gate. Prefer same-engine checked
constructor codecs or an issuer-bound arena/factory using these witnessed
layouts and prepublished owner journals. Per-call graph imports or reflective
ad-hoc Node construction would violate the current lifetime profile. A descriptor
for a container argument can therefore exist before that input codec is enabled;
the host must refuse unsupported marshalling before any guest invocation.

Persisted native layouts avoid hardcoding nominal constructor layouts. Native
make/match/round-trip witness functions are still useful acceptance evidence,
especially for Bool boxing, Unit erasure, Int and IO. They must be genuinely
compiled, source-bound and compared, not merely represented by claimed tags.
Generated wrapper functions are necessary only when implementing an additional
call/ownership adaptation; their original source/type/IR relationship must be
recorded honestly rather than labeled original-entry IR.

## Compatibility and next gates

Keep v1 requests/evidence and their native helper cohort accepted separately.
V2 readers must validate the exact descriptor, reconstruct expected Exprs,
compare original source/callable rows and actual ABIs, and preserve an issued
receipt. Artifact support should use an explicit required v2-entry feature or a
new artifact schema; old readers must reject before startup. Never route an
unknown structured signature through v1's fallback String branch.

The next native corpus should cover mixed multi-argument primitives, signed
values beyond long, Bool/Unit, empty/some/nested Option, products, empty/nonempty
List, IO of each enabled result, aliases, zero-argument constants and negative
implicit/proof/dependent/unsafe/extern/callable cases. Verify original imported C
lookup and exact emitted descriptors before wiring artifact readers and codecs.

## Pinned source references

All references below are to Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, inspected with `git show`:

- `src/library/ir_interpreter.cpp:1061`: original `call_boxed` selection, nullary
  constant loading and application; `:1105` supplies IO world.
- `src/Lean/Compiler/IR/CompilerM.lean:143`: original raw interpreter lookup;
  `:157` boxed lookup uses the base-name module index.
- `src/Lean/Compiler/LCNF/ExplicitBoxing.lean:30`: boxed-version predicate;
  `:46` generates boxed parameters with `borrow=false` and boxes results.
- `src/Lean/Compiler/LCNF/ToImpureType.lean:15`: enum lowering; `:70` native Int
  representation; `:119` impure types; `:163` field storage; `:190` layout
  generation; `:278` persisted layout query.
- `src/Lean/Compiler/LCNF/MonoTypes.lean:53` and `ToImpure.lean:103`: trivial
  structure/erasure rules mean a nominal constructor is not a layout proof.
- `src/Lean/Compiler/IR/Basic.lean:149`: authoritative CtorInfo field extents.
- `src/Init/Prelude.lean:107,233,563,2924,2978`: Bool, Unit, Prod, Option, List.
- `src/Init/Data/Int/Basic.lean:46,60`: Int's source constructors and native externs.
- `src/Init/System/ST.lean:66,77` and `src/Init/System/IO.lean:140`: EST.Out,
  hidden world function and IO's actual error/result definition.
- `src/include/lean/lean.h:3027`: IO world is `lean_box(0)`.
- `src/Lean/Compiler/IR/UnboxResult.lean:15`: `[unbox]` exists but explicitly has
  no effect at this pin; it must not be cited as an active Option optimization.

## SDK validation seam

`ansatz.lean.jvm.entry` now shares descriptor, document, callable-row, and codec-witness validation between the compiler receipt issuer, portable artifact reader, and publisher. Validation alone issues no receipt or runtime capability. Each issuer retains its existing byte limits, original native/source IR comparison, provenance, file custody, and opaque identity checks.

The compiler evidence configuration accepts `:entry-schema 1` (default) or `2`. A producer bundle derives this value from the independently admitted entry source/binary pair. Schema 1 keeps its existing requests and rejects `:signature "auto"` before compiler/path access. Schema 2 emits name-only requests; callers may request `"auto"` or constrain the result to an existing legacy signature. The outer portable artifact remains `lean-native-local-project/2`; the nested entry evidence and admitted producer cohort distinguish the versions. The published v1 bundle is unchanged.

The metadata-only models in `modules/lean-jvm/test/entry_checks.clj` exercise the existing v1 application archive and the root-observed 13-entry, 38-row v2 fixture, including descriptor/ABI/plan/witness/provenance mutations. Fixture digests and producer pins are recorded beside the fixture. These models do not constitute native execution or end-to-end v2 SDK acceptance.
