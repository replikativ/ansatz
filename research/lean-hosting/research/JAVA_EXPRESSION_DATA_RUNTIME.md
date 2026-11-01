# Expr and Level computed-data scalars

The research Java engine implements the exact original `Lean.Expr.mkData`,
`Lean.Expr.mkAppData`, and `Lean.Level.mkData` extern tuples. These produce U64
cache words for genuine guest constructors. They do not define an Expr/Level
object representation, add Node state, change the importer, or replace Meta code.

The [six-row fixture](../test/fixtures/java-expression-data-runtime/README.md)
preserves accepted typed Names and original blob hashes from index
`74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`.
Its provenance pins Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
source contents, and Apache 2.0 license. Exact ABI matching includes raw types,
result, all arities and all ownership bits; all three tuples have no borrows.
The boxed wrappers are original guest IR, including their unboxing and release
instructions.

| Primitive | Exact raw ABI | Native rule |
| --- | --- | --- |
| Expr.mkData | U64, tobject, U32, U8, U8, U8, U8 → U64 | Low 32 hash bits; approximate depth clamped to 255 in bits 32–39; four flags in 40–43; Nat range in 44–63. |
| Expr.mkAppData | U64, U64 → U64 | Low 32 bits of native mixHash on full words; max extracted depth + 1 saturated at 255; OR four flags; max unsigned 20-bit range. |
| Level.mkData | U64, tobject, U8, U8 → U64 | Low 32 hash bits; flags in bits 32 and 33; bits 34–39 zero; Nat depth in bits 40–63. |

Pinned anchors are `src/Lean/Expr.lean:118–182`, `src/Lean/Level.lean:25–108`,
`src/kernel/expr.cpp:105–125`, `src/kernel/level.cpp:44–51`, and
`src/runtime/hash.h:15–25`. The existing Java `mixHash` matches native wrapping
64-bit arithmetic, including the second XOR with the multiplier (not another
multiply). Packing uses unsigned shifts and masks; negative Java long bit
patterns remain exact U64 words internally. Existing external U64 transport
returns nonnegative Long/BigInteger values without reinterpreting logical Ints.

The profile accepts logical Nat carriers Long/BigInteger, rejects negative or
nonnumeric values, and checks Expr range ≤ 1,048,575 and Level depth ≤ 16,777,215
before narrowing. Native panic paths become named bounded rejections. U32/U64
lanes are validated at public transport boundaries, and every Bool must be
exactly 0 or 1. Seven-argument Expr and four-argument Level dispatch run before
the generic three-argument path in both internal-slot and external entry paths.
These successful owning Nat operands fit native immediate bounds: their Java
carriers are uncounted and consumption requires no DEC or host callback.

Invalid primitive arguments publish no result and do not allocate, store,
retain, or release guest values. An original boxed wrapper may already have
released an owned hash box before reaching a malformed primitive argument;
this is its original guest instruction sequence, not a transactional wrapper
promise. Failed-body cleanup retains the engine's existing limitations.

The focused suite covers native valid-domain vectors through raw roots and
original boxed FAPs, exact ABI/borrow adversaries, Nat and depth boundaries,
individual flag validation, internal seven-argument FAP rejection, malformed
owned Node operands without consumption, boxed partial application and forks,
U64 host suspension/replies/forks, and authenticated original-wrapper demand
loading with CodeRequest/fork. The native oracle compares all 160 vectors in
both Lean `--run` and C/native with runtime argv inputs. It never invokes native
panic domains and makes no native timing, heap, Init, or whole-frontend claim.

Validation in a retained 256 MiB REPL passes 9 focused tests / 517 assertions
in each driver. Related baseline, extern, scalar, U64, host, generation, header,
and code-demand suites pass 170 executions / 4,153 assertions across both
drivers. Java compiles with `--release 11`. The full repository gate and genuine
frontend command are left to integration; no Init/full-image replay ran here.

Root integration: the complete Java 11 isolated-jar gate exits 0 at 384 MiB,
835 test executions / 23,662 assertions across 87 suites, including the disabled
logical control foundation. Independent review checked exact native packing,
depth saturation, full-word application hashing, raw ABI and dispatcher routing.
The parent also reran all 160 runtime-input native vectors through both --run
and C/native execution, with matching bits and zero stderr. This is scalar-cache
compatibility evidence; it neither changes the kernel's AST classes nor asserts
complete frontend elaboration.
