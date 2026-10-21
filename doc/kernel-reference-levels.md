# Pinned C++ universe comparator controls

Five cases in `test-data/kernel-reference/levels.edn` record actual calls to the
Lean 4.33.1 C++ kernel comparator `lean::is_geq(lhs,rhs)`, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. These are small reference-compatibility
regressions, not a complete universe solver specification. The test translates
`geq(lhs,rhs)` into Ansatz's `level<=(rhs,lhs)`; no kernel algorithm changes.

| Comparison | Lean C++ | Ansatz | Tenet JVM |
| --- | --- | --- | --- |
| `succ(imax(u,v)) ≥ v` | false | false | true |
| `u+2 ≥ 1` | true | true | true |
| `3 ≥ u+1` | false | false | false |
| `imax(u,0) ≥ 0` | true | true | true |
| `0 ≥ imax(u,0)` | true | true | true |

The first inequality is universally valid: if `v=0`, its left side is 1; if
`v>0`, it is `max(u,v)+1`. Lean's conservative comparator returns false anyway.
False therefore does not establish a mathematical counterexample or rejection of
an actual Lean declaration. This test protects the current reference policy;
adopting a stronger universe solver requires an explicit compatibility decision.
The third inequality has the counterexample `u=3`. `imax(u,0)=0` by definition.

The Tenet observations use `keithadler/tenet-jvm` commit
`152055eb146cf8dd701f2073e92edd4324890d52`; Ansatz Java sources were unchanged
from `e3379e29c064576ba389d1a18ccb83a546e297c4`. A separate five-case Java harness
confirmed every table entry. Tenet is not a dependency of the regression test.
No fixture or implementation content was copied from Tenet.

## Oracle identity and reproduction

`scripts/kernel-reference/level.cpp` is an independent minimal API caller. It
uses the pinned source headers and installed `libleancpp.a` plus corresponding
Lean runtime. This executes the **C++ kernel** implementation; it does not call
the separately implemented Lean function `Lean.Level.geq`, substitute a
mathematical solver, or derive results only by reading source. The output is
five JSON lines. A recorded run compiled and exited 0 with results
`false,true,false,true,true`.

Observed SHA256s from that run:

| Input | SHA256 |
| --- | --- |
| `scripts/kernel-reference/level.cpp` | `0bbe52737c99c34dda78872d44a67d3779b79d330f54b6a8e61ae84f7166aa20` |
| pinned `src/kernel/level.h` | `c8bd15369a7defcde87a5e0b750ab46512c28ce0a4de30f9be3eff8e3069c483` |
| pinned `src/kernel/level.cpp` | `7cb927c6fabd9fb843f548443494d3673a08074e26fe32b679e80f4664fc7f25` |
| installed `lib/lean/libleancpp.a` | `71c73a927e93d1d7884622f44696a3b897867e6da4279448f18b2f0d2d5d6857` |
| installed `lib/lean/libleanshared.so` | `23d636cac1cadcba37beac30eff9b9b20d66cee726cf5defb4ae39f1284a3e5a` |
| installed `include/lean/lean.h` | `02af0040283143b264e3a44b06b348b6973ae6037fa8f550701c83dd7a062ace` |
| installed `include/lean/config.h` | `96ed10a3e427a82e47901e0ef96c74d04da3a58054be680750e21099c996a722` |

With an existing pinned source checkout and installed matching toolchain, set
`LEAN_SOURCE` and `LEAN_PREFIX` to their locations, then run from this repository:

```bash
pin=819816b2e0a3bf405af45ae5c7af2491d8f5bee6
probe=.tmp/kernel-reference
mkdir -p "$probe/headers"
git -C "$LEAN_SOURCE" archive "$pin" src |
  tar -x -C "$probe/headers" --wildcards --no-anchored '*.h'
"$LEAN_PREFIX/bin/lean" --version
c++ -std=c++17 -O0 -I"$probe/headers/src" -I"$LEAN_PREFIX/include" \
  scripts/kernel-reference/level.cpp -L"$LEAN_PREFIX/lib/lean" \
  -Wl,-rpath,"$LEAN_PREFIX/lib/lean" -lleancpp -lleanshared \
  -L"$LEAN_PREFIX/lib" -Wl,-rpath,"$LEAN_PREFIX/lib" -lc++ -lc++abi \
  -o "$probe/level"
"$probe/level"
```

The recorded compiler was GCC 15.2 on Linux. Installed Lean uses libc++; its
libc++ and libc++abi are linked explicitly. Matching libc++ development headers
were unavailable, so system C++ headers were used for the tiny caller. Its
boundary contains only `const char*` and pointer-sized Lean name/level wrappers,
with size assertions; no standard-library object crosses that boundary. Both
libstdc++ and libc++ were loaded. This is narrow API evidence, not a supported
recipe for arbitrary C++ embedding. Use matching libc++ headers/tooling where
available. Headers came from `git archive` of the pin; the source checkout's
working tree was not read or modified. The installed config defines
`LEAN_MIMALLOC`. Initialization is paired once: utility initialization already
initializes the runtime; explicitly initializing it again caused an earlier
failed setup attempt. All level/name values die before finalization.

The successful compiler/probe were externally guarded: process-group sampled
RSS 512 MiB, time 120 s each, MemAvailable floor 1 GiB. Compiler peak sampled RSS was
139,763,712 bytes; probe 2,441,216 bytes; both exited 0 and no guard fired. Short
process samples are lower bounds, not performance claims. No full Lean build or
network download was needed. The shell commands above do not themselves impose
those external limits; use a process supervisor under constrained resources.

Run the Clojure regression with the repository's compiled Java kernel:

```bash
clj -M:test -n ansatz.kernel.level-reference-test
```

This corpus intentionally excludes the Tenet bundled positive NDJSONs, which
were exported with Lean 4.35.0-rc4 and 4.34.1 and would be cross-version checks.
