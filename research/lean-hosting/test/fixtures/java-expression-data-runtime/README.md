# Original Expr and Level scalar data

Six accepted-CAS rows contain the exact three extern declarations and their
original boxed wrappers. Each record preserves its typed Name and raw original
blob SHA256. Only the top-level `pretty` field is removed; bodies are unchanged.
The accepted index and pinned upstream source hashes are in `provenance.edn`.

| Original root | Native symbol | Raw parameters → result (all owned) |
| --- | --- | --- |
| `Lean.Expr.mkData` | `lean_expr_mk_data` | U64, Nat, U32, Bool, Bool, Bool, Bool → U64 |
| `Lean.Expr.mkAppData` | `lean_expr_mk_app_data` | U64, U64 → U64 |
| `Lean.Level.mkData` | `lean_level_mk_data` | U64, Nat, Bool, Bool → U64 |

These compute scalar cache words. They do not allocate or supply an Expr/Level
representation. Expr range is at most 1,048,575, and Level depth at most
16,777,215. Expr approximate depth saturates at 255. A Bool is exactly 0 or 1.
Native out-of-range panic paths are excluded from the oracle.

`DataOracle.lean` parses decimal runtime arguments and calls the genuine native
primitives. `native-vectors.json` contains 160 valid-domain input/output vectors:
80 Expr combinations, 16 Level combinations, and 64 application combinations
including arbitrary high-bit U64 cache words. Both installed Lean `--run` and
C/native match every vector, with exit 0 and empty stderr. Inputs come through
argv rather than compile-time expressions. The observed toolchain is Lean
4.33.1 at commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

Run `python3 path/to/native-oracle.py` from any directory. It checks committed
source/vector hashes before executing Lean, compares both output traces, and
prints a receipt. It never rewrites source, vectors, or the checked receipt.
Compiler artifacts and captured streams are repository-local temporary files
removed after completion/error. Each command has wall/CPU limits, a 512 MiB file
cap, no core dump, one runtime/linker thread, and a 64 KiB acceptance bound per
captured stream. There is no address-space cap or memory/timing claim. Recorded
binary/runtime/compiler/generated hashes describe the successful run, not the
accepted checkpoint producer or bit-identical regenerated executables.

Upstream rows and source are from Lean, copyright Microsoft Corporation and
Lean contributors, under Apache 2.0; the pinned `LICENSE` digest is recorded in
provenance. This fixture adds no native replacement for Meta functions and no
AST/import storage claim. See [the scalar runtime report](../../../research/JAVA_EXPRESSION_DATA_RUNTIME.md).
