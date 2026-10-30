# Native ST.Ref execution on the Java engine

Implemented research profile, 2026-10-29. Reference: pinned Lean
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, `src/Init/System/ST.lean:186–197`
and `src/runtime/io.cpp:1426–1535`. This is the engine's single-threaded guest-ref
model, not Lean's native multi-threaded atomic/ref scheduling implementation.

The [logical sharing foundation](JAVA_LOGICAL_SHARING.md) now preserves native
MT/persistent ref publication: incoming payloads are marked before set/swap,
without creating a task manager or adding atomic cross-thread guarantees. Fresh
ST refs retain their existing unmarked behavior.

## Exact declarations and ownership

The six original extern ABIs, including both erased parameters and the final
world parameter, are registered as builtins. They no longer require HostExtern
registration or a HostRequest. All placeholders must be the canonical erased
Long zero, so an ignored argument cannot silently discard an owned object.

| Primitive | Result and ownership |
| --- | --- |
| `lean_st_mk_ref` | Transfer the owned value into a fresh ref with RC1. |
| `lean_st_ref_get` | Borrow the ref and retain its payload for an owned result. |
| `lean_st_ref_set` | Transfer the new value to the ref and release its old payload; return Unit. |
| `lean_st_ref_swap` | Transfer the new value to the ref and its old payload to the caller. |
| `lean_st_ref_take` | Transfer the old payload to the caller and leave the ref empty. |
| `lean_st_ref_ptr_eq` | Borrow both refs and compare their cell identities; return UInt8 Bool. |

Refs have a distinct runtime kind. Ordinary constructors, arrays and closures
cannot be used as refs. Persistent RC-zero refs remain mutable. Set can refill an
empty cell; get/take/swap on an empty cell give a named error instead of emulating
a native MT spin. No concurrency, blocking-read or atomic cross-thread guarantee
is implied. A same-value set/swap of a positive-RC payload requires a distinct
owned incoming credit; a borrowed field view is not an owned update argument.

Static typed FAP calls preserve their original borrow contract and acquire no
extra ref credits. Direct external invocation or PAP construction for borrowed
ref primitives rejects before taking root ownership. Use the genuine owned
compiler-generated `_boxed` wrappers, which release their owned ref arguments
explicitly after the borrowed primitive call. The engine does not invent an
implicit wrapper or double-adapt borrowed arguments. mkRef has no borrowed input
and is callable at an owned root entry.

## Fork and failure behavior

Refs, payload aliases and cycles use the existing graph memo during eagerFork.
Each branch receives its own mutable cells and graph while sharing immutable code.
Reference counts copy with their existing owner envelope; fork creates no extra
credits. The tests exercise a real self-cycle, fork it, break it through the
original set wrapper in each branch and check the resulting owner counts.

Invalid placeholder/kind/empty/alias operations validate before their relevant
effects. If normal guest execution fails, the existing failed-frame cleanup
limitations still apply; tests discard the failed execution rather than retry
or claim restoration of owned arguments. In particular, recursive frame unwind
and closing its caches do not prove cleanup of failed invocation arguments.

## Bounded evidence

[The fixture](../test/fixtures/java-ref-runtime/README.md) contains the six original
declarations and their six genuine generated boxed wrappers, with a separate
derived-file digest and original blob identities. Only display-only top-level
pretty text was removed.

Each driver passes 10 focused tests / 98 assertions. The combined isolated jar
gate passes 386 test executions / 13,750 assertions at 384 MiB. Independent review
checks exact ABI matching, ownership, empty refill, same-value updates, borrowed
entry guards and the fixture transformation.

The [implementation record](../measurements/java-ir-ref-runtime-2026-10-29.edn)
pins source, jar and fixture bytes and records the complete ordinary-computation
control. Its allocation stays at 1,515,859.52 bytes per RBMap execution. CPU timings
vary across this shared-machine session; no speedup or stable CPU-overhead estimate
is claimed.

The genuine nine-node ppExt probe now installs its real prepared globals through
the graph API, forks at code demand, prepares the two original initializer bodies
and reads the saved PPFns record using native ref-get. It makes **zero host
requests** and leaves the five callbacks and both global sentinels unprepared.
It still does not execute the complete parser or elaborate a Lean file.

Selected positive-owner graph import, full prepared frontend state, additional
runtime families and module/kernel carriers remain the next campaign work.
