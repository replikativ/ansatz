# ByteArray runtime and prepared state

The research Java engine executes the original ByteArray.mk, get, size and push
externs and their genuine boxed wrappers from pinned Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The eight-row
[fixture](../test/fixtures/java-byte-array-runtime/README.md) pins original CAS
identities and the derived fixture digest. These are the four ByteArray extern
roots in the original header inventory; this does not cover every Lean ByteArray
operation.

ByteArray has a distinct private kind, zero object fields, raw byte capacity and
private logical size. It uses the existing optional Node metadata slot, without
enlarging every constructor. This is a width-one scalar array; generic scalar
arrays and FloatArray remain unsupported. Constructor projections, scalar unbox
and object-array operations reject it even if a host mutates its public tag.

`mk` validates the entire live object-array prefix before allocating or consuming
the container. Bytes carry no child reference credits. `push` preserves Lean's
copy-on-write behavior: unique buffers with room mutate; shared/persistent buffers
or growth allocate and copy the live bytes, then consume the old container once.
Growth uses twice the required size, bounded to 16 MiB per buffer. `get` is the
proof-backed `fget`, so invalid indices reject instead of adopting the different
checked native getter's zero result. Raw borrowed get/size cannot enter through
host roots, partial applications or imported closures; original boxed wrappers
provide the owning boundary.

PreparedGraph explicitly adds a ByteArray descriptor with a cloned live byte
payload. The Clojure facade accepts ordered, counted collections of unsigned
integers 0..255; Java accepts a raw byte array. No constructor 1 KiB scalar cap is
applied to this different kind, while the existing 16 MiB aggregate graph scalar
budget still applies. ByteArrays have no outgoing guest edges. Existing default
persistent and selected-owner profiles retain their counting rules. Fork copies
both logical-size metadata and the complete capacity buffer through the existing
identity memo, preserving aliases while isolating writes at the same index.

Thirteen tests pass in each driver: 118 assertions recursively and 122 with
explicit continuations. They cover real ABIs, import cloning/bounds, selected
owner aliases, exact transfer counters, growth and spare-capacity copy-on-write,
fork alias/payload isolation, kind fences, invalid mk/get/proof preflight, borrowed
PAP/import fences and aggregate import budget rejection before publication. Failed
explicit execution retains the existing terminal cleanup restriction; these tests
do not claim general unwinding of owned failed frames. Independent static review
found no blocker; its substantive test gaps were added. The combined isolated jar
gate passes 520 executions / 17,060 assertions across 61 suites at 384 MiB.

The larger source-derived companion capsule imports and forks in the retained
384 MiB REPL: 82,272 reachable Nodes, 1,723 positive selected-owner credits,
80,549 persistent Nodes, 134,537 scalar bytes, 2,725 Headers and 43 globals.
This includes 90 ByteArrays containing 294 live bytes. The child census matches
and all Node roots are distinct, while immediate scalar globals remain equal.
Single observed install/fork times were 92.5/28.2 ms, excluding JSON parsing,
Header registration and descriptor preparation; these are not steady benchmarks.

This is a bounded research runtime gate, not an authenticated public frontend
bundle. The capsule's 43 globals come from a partial static code inventory; 55
new closure targets still need further code/global fixed-point expansion. Original
header execution was previously blocked at ptrAddrUnsafe after 72 loaded bodies;
identity-only pointer support is a separate reviewed change. Complete Lean file
loading, elaboration, IO coverage, native physical pointers and self-hosting are
not established by this gate.
