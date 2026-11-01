# Original Expr equality runtime evidence

Pinned Lean commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` (4.33.1).
Accepted original index: `74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`.

`original-rows.json` contains 74 exact original declaration rows for the two
borrowed externs, genuine owned boxed wrappers, Expr/Level constructors and their
static dependencies. Only optional top-level `pretty` is omitted; each stored
SHA identifies complete original CAS bytes. No initialized dependency is present.
`layout-source-rows.json` separately retains original source comparator/layout
rows and dependencies. `layout-evidence.json` collects compiled constructor infos
from those rows: all Expr/Level, DataValue, Syntax and Preresolved layouts used by
the port are authenticated here rather than inferred from source field order.
Source file hashes and fixture hashes are in `provenance.json`. Upstream code is
Apache-2.0; see `LICENSE` and source headers.

`ExprEqualityOracle.lean`, `native-golden.txt`, and `native-observation.json` are
independent official-toolchain evidence produced in a separate bounded native
source experiment. All 54 ordinary source-constructed cases passed both `--run`
and generated-C/native modes. The observation records accepted executable/runtime
hashes and measured subprocess bounds, not a fresh reproducible toolchain build.
It makes no forged-cache/cycle, JVM throughput, or native heartbeat parity claim.
Historical absolute paths in its command receipts describe that observation;
they are not required paths for verification or a portable build recipe.

Run `python3 verify-native.py` to check the pinned source, receipt and golden.
Optional `--run-output PATH --native-output PATH` checks independently generated
outputs against that same immutable golden. The verifier does not invoke a
compiler, execute the Lean program, or regenerate evidence/goldens.

The Java focused suite also uses explicitly labeled graph/layout models for
cache collisions, low32/upper-word rules, invalid heads, native padding, cycles,
limits and private closure guards. Such models are not claimed to be well-typed
native-produced ASTs or successful kernel checking. Genuine original constructor
and wrapper paths are tested separately.

Two additional scalar constructor dependencies are supported: exact UInt8→UInt32
widening and UInt64→UInt8 low8-bit narrowing. Their genuine boxed wrappers are
included. Focused JVM vectors cover every byte, raw high64-bit words and invalid
external lanes; source lean.h2044/2164 specifies the casts. These vectors are not
claimed to be a separately executed native cast oracle.
