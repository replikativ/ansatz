# Append cursor native oracle

This separate Ansatz-authored ordinary Lean probe preserves the validated
writing application's original source files. `AppendOracle.lean` uses the same
public IO operations on native and JVM backends; seed all six named files with
`seed` in a fresh working tree before invoking `appendCursorOracle` or `main`.
No custom externs or IO replacements are used.

The pinned Lean 4.33.1 native run returned exit 0, empty stdout/stderr, and:

| File | Final bytes (hex) |
| --- | --- |
| append-initial | empty |
| append-rewind | empty |
| append-rewind-flush | empty |
| append-write-flush-truncate | 7365656458 |
| append-rewind-write | 736565645859 |
| append-write-truncate | 736565640058 |

The first five observations are in the synchronization-boundary parity domain.
The last case deliberately truncates unsynchronized buffered native output:
native closes to `seed\0X`, while write-through JVM output closes to `seedX`.
That difference is expected and must be recorded rather than counted as parity.

Lean opens O_APPEND and then uses fdopen("a"); the initial logical cursor on
this pinned Linux/glibc runtime is zero, unlike an initial-seek-to-EOF model.
After writes it follows the resulting appended offset; rewind resets it to zero.
The JDK append channel's position getter reports EOF and cannot represent that
cursor. The provider therefore tracks a separate logical append offset while
retaining actual kernel append writes. See [FILESYSTEM.md](../../FILESYSTEM.md).

[provenance.json](provenance.json) records source and native observations. This
native evidence and provider regression do not replace execution of this exact
probe through the rebuilt public JVM source/artifact pipeline.
