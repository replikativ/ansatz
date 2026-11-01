# Portable checkpoint support

The optional runtime consumer requires `prototype.checkpoint-wire` and
`prototype.bootstrap-archive/verify-function-rows`. Earlier campaign validation
loaded both from a separately pinned `target/consumer-support/src` directory.
The factory reference landed in commit `68cdc41a`, while those implementations
remained outside tracked source. Fresh source classpaths therefore could not
require the consumer correctly. This change tracks the exact implementations
already present in the pinned producer/consumer inventory:

| Resource | SHA-256 |
| --- | --- |
| `prototype/checkpoint_wire.clj` | `77faed12af25aee0080d34215f425f94a23746dd6434513e570ddd6bcbf60965` |
| `prototype/bootstrap_archive.clj` | `adf662957c23ded35277b30b941f1419d6c69b125944dea6e7f705e2e724ed00` |

The previous tracked archive file (`95799052…`) is an exact prefix of the latter;
the remaining 4,362 bytes define the streamed function verifier. Its historical
`DRAFT` comment remains byte-for-byte to preserve the already pinned resource.
`declaration_store.clj` already matched its support copy and is unchanged. This
repairs source availability without widening a compatibility profile or changing
an existing snapshot, archive format, parser, or producer identity.

## Streamed function verification

`verify-function-rows` requires an expected archive SHA-256, the pinned Lean
commit and a trusted function comparison callback. It validates the header,
record shapes, table counts and duplicate keys, state placement, `next-id`, end
trailer and EOF while scanning. The callback receives each archived function and
returns an equal name and canonical function from a caller-owned trusted table.
The factory compares refreshed extern ABI bodies against independently pinned
declaration rows before returning its canonical references.

Results become available only after the **complete byte stream** matches its
expected digest. The callback can execute before the final digest check and must
remain a trusted, side-effect-free comparison; this API does not sandbox it or
undo its effects. No partial function map is returned on failure. The result
contains canonical functions, header, reservation boundary, SHA-256 and bytes.
It neither restores a second World nor validates the skipped heap/global values
or their guest references/ownership. The archive's separate restore path retains
its complete-world validation contract.

## Wire framing

The wire layer serializes bounded individual rows with closed guest carrier/tag
readers, strict UTF-8, exact float bit carriers and metadata-aware data comparison.
Framed reads require a positive length no larger than 64 MiB before allocating
the payload. Premature EOF is an error. A one-open bounded stream reader probes
at most one excess byte and leaves a borrowed stream open. These are byte and
framing contracts, not arbitrary decoder CPU/depth bounds. Direct `decode`
receives caller-provided bytes and does not itself impose the framing size cap.
No reader evaluation or generic Java serialization is used.

## Fresh source verification

Compile the normal Java kernel/runtime sources and the optional tracked
`java/prototype/TypedLongMemo.java` as documented in the experiment README. The
optional consumer's source helpers use JDK 17's `HexFormat`; Java compilation
still targets 11, and the recorded validation runs on JDK 25. A
fresh JVM must select the current wire/archive/factory/profile/consumer source
resources and reject stale AOT `__init.class` resources before requiring them.
The portable proof excludes historical support source directories and records
actual selected resource hashes and class origins. Successful loading establishes
current-source availability; it does not authenticate a historical consumer build
or prove genuine Lean frontend compatibility.

Dedicated tests exercise canonical entry identity and metadata, digest commit
semantics, comparison failures, malformed archive structure, framing/UTF-8,
floating bit fidelity, borrowed stream ownership and public Name interning.
The [validation record](../measurements/portable-checkpoint-support.json) reports
27 focused tests / 1,232 assertions and 1,021 complete optional runtime tests /
93,863 assertions, with actual current source/class selection checks and no
historical source or class fallback. All input hashes matched after each root-owned
process was disposed. These checks establish current-source availability and
regression coverage, not historical consumer identity or genuine frontend execution.
