# Original UInt64 and hash declarations

The 28 rows are 14 original header-inventory extern declarations and their 14
genuine compiler-generated boxed wrappers from Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Each original CAS blob was bounded,
SHA256 checked, and checked for its exact structured Name before removing only
optional top-level `pretty`. Original bodies, ABIs, dependencies and runtime
metadata are unchanged. Per-record original hashes and the separately pinned
derived fixture hash have different meanings.

Selection includes every original-inventory extern with a UInt64 input/result,
every UInt64-prefixed root, and String.hash/mixHash. It includes Float.ofBits,
Float.ofModel and UInt64.toFloat as **descriptive deferred Float boundaries**;
their presence alone does not authorize Float execution. The separate
[Float fixture and runtime gate](../java-f64-runtime/README.md) now validates them. Lean.Expr.mkData is likewise
a separate metadata-packing binding, not UInt64 arithmetic. Lean.getGithash is
a version-string query, so it is not selected by a misleading `hash` substring.
No absent UInt64 arithmetic/conversion declarations or wrappers were invented.

This is a source fixture, not a runtime result, native oracle, complete body
closure or frontend compatibility claim. A UInt64-only test program must select
its supported subset explicitly.

## Compiled hash-source arithmetic oracle

`native-hash-oracle.json` records a separately executed **compiled pinned
hash-source arithmetic oracle**, not a full Lean runtime ABI oracle. Its
reproducer fetches `hash.cpp` and `hash.h` at the pinned commit and checks their
SHA256 before copying them **verbatim**. The only replacement scaffolding is an
empty `runtime/debug.h` and a `runtime/int.h` supplying `std::uint64_t` plus
`std::size_t`. The generated driver calls the original functions; it does not
rewrite their algorithms. The results authenticate both scaffolding and driver
hashes. Upstream copyright/MurmurHash attribution remains in copied sources;
the exact pinned Apache2 license is included as `UPSTREAM-LICENSE`.

The observed compiler was `g++ (Ubuntu 15.2.0-16ubuntu1) 15.2.0`, C++11/O2 on
little-endian x86_64. Compile and execution exit codes were both 0. The driver
checks 64-bit pointer/uint64 width and little endianness. Compiler processes have
a 256 MiB address-space limit, 30/35-second CPU limit and 60-second wall timeout;
the executable has a 64 MiB limit and 10-second wall timeout. These are resource
limits, not measured Lean/JVM memory or performance results.

All 16 vectors match the independent Python source-arithmetic reference: eight
UTF8 String hashes (empty/NUL/multibyte and 7/8/9-byte boundaries), four mixHash
pairs including high bits, and four Name-hash arithmetic compositions. Name
compositions supply the Prelude's 1723 seed and large-numeric 17 rule in the driver;
they do not construct native Names or execute compiled Prelude bodies. No Lean
heap, value ABI, native String object, interpreter, or JVM is exercised.

From the repository root, with an existing local Lean git object database:

```sh
python3 experiments/lean-ir/test/fixtures/java-u64-runtime/native-hash-oracle.py \
  --lean-source path/to/lean4 \
  --output target/java-u64-runtime-v1/native-oracle
```

The optional `--python-reference` argument checks a source-derived JSON vector
file during the run. The recorded result includes that file's SHA256 and 16
matching cases. Output, generated driver, shims and executable stay in the
ignored build directory; the tracked result is a bounded evidence snapshot.

## Genuine Name construction and cached hash bodies

`name-rows.json` is a separate 11-row static body closure, pinned by
`name-provenance.edn`. It does not change the main 28-row fixture's hash. Roots
are `Lean.Name.str._override`, `Lean.Name.num._override`,
`Lean.Name.hash._override`, and the getter's genuine `._boxed` wrapper. Plain
`Lean.Name.str`, `Lean.Name.num`, and `Lean.Name.hash` do not have declaration
rows in this base CAS; these exact compiled override Names do.

The complete actual FAP/PAP closure adds four externs (`String.hash`, `mixHash`,
`Nat.decLt`, `UInt64.ofNatLT`) and three original closed constants: anonymous
hash 1723, large numeric fallback 17, and Nat bound `2^64`. Those constants have
ordinary closed-body semantics, not initialized-global sentinels. No Expr,
Float, unsupported extern, substitute constructor, or synthesized hash getter
is needed. Constructor and getter bodies perform genuine U64 SSet/SProj after
two object fields; the numeric constructor executes its actual Nat comparison.

Both constructors consume their parent and component inputs as declared. The
raw getter borrows its Name and returns U64; its boxed wrapper owns/decrements
the Name and returns the genuine eight-byte U64 box. Callers needing a retained
Name must supply a separate owned credit when using that wrapper. Shared extern
rows duplicated across the two fixtures retain identical original hashes; a
combined Program should deduplicate exact Names rather than register twice.

Extraction authenticated only 12,958 original bytes, retained every original
body/ABI, and removed optional pretty text. Closure traversal follows actual
FAP/PAP sites including closed constants, with a 32-row/1 MiB source ceiling.
This is source evidence only; no JVM, Name execution or parser acceptance was
performed by the extractor. Upstream attribution/license below also applies.

Upstream sources and license are pinned in `provenance.edn`. Derived material
is distributed under upstream [Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
See the pinned [IR interpreter](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/library/ir_interpreter.cpp)
and [runtime headers](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/include/lean/lean.h).
