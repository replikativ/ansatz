# Explicit guest implementations of exported symbols

The Java research engine can bind an unavailable original extern Header to an
actual original fdecl Header in the same accepted source. Calls then execute the
existing guest implementation through the ordinary engine and demand-code path.
The original extern and target rows, hashes, dependencies, parameter IDs and
bodies remain unchanged. No host implementation of MetaM is introduced.

## API and authority

```java
Program bound = Program.bindGuestExports(base, new GuestExportBinding[] {
    new GuestExportBinding(originHeader, implementationHeader)
});
```

The optional research facade offers
`(bind-guest-exports basis [[origin-header implementation-header]])`, returning a
new basis. Install its Program at the existing idle/host/code boundary. Both
Headers must already be registered as their exact issued identities.

This is trusted host configuration. The adapter must verify original raw bytes,
exact typed Names, source cohort and the upstream export association before
binding. Header construction or a matching symbol/ABI does not prove that a body
implements that symbol. The catalogue reader/resource stays outside the engine;
a binding contains no callback, guest value, native resource or mapped index.
The engine does not automatically accept compiler-output `redirect` metadata as
an authority capability.

The bounded profile requires:

- An unavailable standard c/all extern origin and a distinct direct fdecl target
  from the exact same SourceBinding.
- Matching raw argument types, borrow flags, arity and result type. Physical OBJ
  lane equivalence is insufficient: object/tobject and erased/void remain distinct.
  Parameter register IDs may differ and are preserved independently.
- Supported execution lanes and non-nullary, non-initialized functions. Nullary
  cache/global aliases and initializer aliases require a separate contract.
- No symbol reserved in the native registry, including recognized unavailable
  primitives; no existing host-symbol binding. Later host registrations also
  cannot conflict with a bound guest export.

A batch validates into private staging state and publishes one immutable Program
only after all entries pass. Repeating the same binding is a no-op. An inherited
binding cannot be changed; source Function/Header identities and prepared bodies
cannot be replaced. Alias targets must be fdecls, so alias chains/self-cycles are
rejected. Ordinary implementation-body recursion through the original extern is
legal and remains budgeted.

Exact borrow matching supplies no new ownership adapter. Existing typed root/AP
borrow limitations remain; use a genuine owning guest wrapper when required.
The positive borrowed test uses direct FAP inside an owning wrapper with explicit
INC/DEC. Existing native primitive fences cannot be bypassed with an export
alias because native symbols are reserved. This feature makes no broader claim
about raw borrowed closures or generic external ownership adaptation.

## Dispatch, suspension and forks

Each Program has an immutable origin-slot → actual Function table. Header/body
registration, materialization and eager extension preserve it. Descendant
validation also preserves inherited non-null entries. Function objects are never
mutated, so a parent and two sibling forks may retain different immutable binding
choices from the same previously unavailable origin.

Root, direct FAP, self-tail call, and fully applied closures resolve to the real
implementation before body entry or argument/capture consumption. Underapplied
closures keep the original logical callable and capture order. Actual parameter
register IDs, active Function and PreparedBody always belong to the implementation.
Its certified pointer sites therefore retain the correct body association.

No target PreparedBody is installed in the origin slot. If the implementation
body is absent, the explicit driver issues its ordinary CodeRequest for the
**implementation Header**, retaining actual arguments once. Existing header/hash,
descendant, once-only reply and ownership checks govern resumption. Genuine guest
code may then suspend for an unrelated explicit HostCall normally. Recursive
execution requires the implementation body already prepared.

Non-nullary redirects add no new mutable cache or initialization state. Existing
nullary constants called by an implementation retain their own cache IDs and
owner credits. Fork copies the ordinary activation/argument/cache graph and
shares immutable Program metadata. Native intrinsics and host calls bypass the
new export lookup; unavailable extern dispatch uses one indexed table lookup,
without catalogue access or synthetic IR bodies. No common Node field is added.

## Authentic Lean examples

At pinned Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`:

| Original extern | Symbol | Actual exported fdecl |
| --- | --- | --- |
| Lean.Meta.whnf | lean_whnf | Lean.Meta.whnfImp |
| Lean.Meta.inferType | lean_infer_type | Lean.Meta.inferTypeImp |

Both raw sides have owned `[object,object,tobject,object,tobject,void] → object`.
Their genuine boxed wrappers instead have tagged world lanes and forward to their
own corresponding unboxed declaration. Keep those original wrappers.

`Lean/Meta/Basic.lean:765–779,833–840` explicitly describes the forward-declaration
mechanism. The actual export attributes are at `Meta/WHNF.lean:1103` and
`Meta/InferType.lean:237`. `Compiler/ExportAttr.lean:54–72` supplies the export
metadata; `Compiler/LCNF/EmitC.lean:240–252` emits its C symbol.
`LCNF/ToDecl.lean:170–176` rejects exported borrowed parameters unless annotations
are suppressed; both source sides explicitly suppress them. The original base
CAS rows here contain redirect:null, so the pinned source/export evidence is a
separate part of the adapter's authority.

The [eight-row fixture](../test/fixtures/java-guest-export-runtime/README.md)
pins both pairs and four genuine boxed wrappers. Header-only tests request the
exact implementation Header and original SHA, then stop. Boxed tests execute only
the actual forwarding wrapper before the same request. Placeholder carriers in
these stopped requests are not asserted valid MetaM contexts. No implementation
body or kernel checking operation is executed by those tests.

## Verification and limits

A separately compiled Java 11 jar passed in a retained 256 MiB REPL. Eighteen new
tests pass with 117 recursive and 122 explicit assertions. They cover transactional
registration, source/Header/raw-ABI adversaries, reserved/host conflicts, sparse
parameter IDs, positive UInt32 lanes, borrowed wrapper accounting, normal alias
recursion, partial/oversaturated application, preflight owners, separate sibling
bindings, code/host suspension and forks, constant caches, real pointer-site
certificates and the authentic stopped Meta requests.

Existing Header, demand-code, host, generation, baseline, continuation and
Task.map suites also pass against that isolated artifact. The runner includes
both new driver suites and their expected counts. Full integration gate and real
frontend acceptance remain separate root work; this feature alone establishes
neither command elaboration nor complete Meta/kernel interoperability. No Init,
full image or native frontend was loaded for this implementation.

Root integration: the Java 11 standalone jar passes the complete 384 MiB gate,
740 test executions / 21,672 assertions across 79 suites, with exit status zero.
The existing proof-carrying String position suites and their expected-count
contract remain included alongside the new export suites. Independent dispatch,
Program-generation and ownership review found no blocker. This gate exercises
the authentic stopped Meta requests; it does not execute their implementation
bodies or establish valid guest MetaM contexts.
