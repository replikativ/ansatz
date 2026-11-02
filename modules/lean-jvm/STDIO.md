# Supplied input and captured output

This describes the Campaign 2 candidate. See the [compatibility ledger](COMPATIBILITY.md)
for the published/candidate boundary and remaining runtime work.

`InvocationOptions` supplies finite input for one function call. It does not
take over process-global stdin or expose OS handles. Existing calls keep their
signatures and use empty input. Reusing a configured function starts its input
at position zero on each invocation.

For an entry such as the unchanged FP Lean `HelloName.main : IO Unit`:

```java
LeanFunction greet = project.function("main");
IOResult<?> answer = (IOResult<?>) greet.invokeWith(
    InvocationOptions.stdinText("Ada\n"));
System.out.print(answer.stdout());
```

The Project convenience is `project.callWith("main", options, arguments...)`.
Options are separate from explicit Lean arguments; a `List String` main still
receives that list as an ordinary argument. Native preparation and entry selection
are unchanged.

```clojure
(lean/call-with-options project "main" {:stdin "Ada\n"})
;; IO result includes :value, :stdout, :stderr, :stdout-bytes, :stderr-bytes.

(def greet (lean/function project "main" {:stdin "Ada\n"}))
(greet) ; fresh supplied input each time, same checked Project and code
```

The existing `lean/call` and two-argument `lean/function` retain their three-key
IO result maps. Option-bearing calls add defensive byte-array snapshots. Use
`vec` when comparing byte arrays by value in Clojure.

## Values, limits and errors

- Java options are immutable. `stdinBytes(byte[])` copies the caller's bytes;
  getters return copies. `stdinText(String)` rejects malformed UTF-16 and encodes
  UTF-8. Clojure accepts mutually exclusive `:stdin` text or `:stdin-bytes` byte
  array, with optional `:stdout-limit-bytes` and `:stderr-limit-bytes`.
- Input is limited to one MiB. Each output channel defaults to sixteen MiB;
  `withOutputLimits(stdoutBytes, stderrBytes)` may tighten these limits, including
  zero. Invalid options and host arguments are refused before guest execution,
  leaving a healthy Project reusable.
- Raw output bytes are authoritative. `IOResult.stdoutBytes()` and
  `stderrBytes()` return defensive snapshots. Text getters decode the complete
  capture using Java UTF-8 replacement, so a valid character split across writes
  is decoded after its fragments are combined. Malformed raw output can have a
  different replacement grouping from Lean's own string decoder; use bytes for
  exact output.
- Supplied input uses native-Handle-like semantics. `read` and `getLine` share
  one cursor. A line includes LF, preserves CR and embedded NUL, and decodes
  malformed UTF-8 using pinned Lean's lossy recovery. EOF returns empty input.
  This deliberately differs from Lean's separate `Stream.ofBuffer` semantics.
- Stdout/stderr accept byte and text writes, flush, and report non-TTY status.
  Wrong-direction operations return catchable `IO.Error.userError`; they do not
  silently return EOF or discard output. Uncaught guest IO errors retain the
  SDK's `GuestIOError` behavior.
- Exceeding resource limits or cancellation is a host policy failure, not a
  guest IO error. Execution failures retire that Project branch; create/load a
  new Project for further execution. Output space is checked before a write is
  published. Initialization captures count toward the first IO call's limits;
  a limit too small for that pending prefix is refused before guest execution.

For example, byte input and tighter limits are explicit:

```java
InvocationOptions input = InvocationOptions.stdinBytes(new byte[] {65, 0, 66, 10})
    .withOutputLimits(4096, 4096);
IOResult<?> answer = (IOResult<?>) project.function("main").invokeWith(input);
byte[] output = answer.stdoutBytes();
```

## Lifetime and fork boundaries

Standard stream objects belong to an invocation epoch. Retaining an escaped
stream and invoking it during a later call does not consume the later call's
input: stale IO methods return a guest error. Stale `isTty` is a terminal refusal
because its BaseIO result has no IO-error envelope. Code that stores standard
streams in initialized globals for later calls is outside this profile. Stdio
redirection setters are also outside public admission.

The internal engine copies cursors, epochs and capture state on its existing
fork path and shares only private immutable input bytes. This does not expose a
public Project fork API. The separately authenticated internal
`Stream.ofBuffer`/custom-stdio context cannot overlap a supplied invocation
context; installing it over an existing default stdin root is refused before
ownership changes.

## Compatibility examples and verification

The [unchanged input examples](examples/fp-lean-io/README.md) cover HelloName,
EarlyReturn and ForMIO. The instrumented insertion-sort CLI has a separate
sharing-provenance limitation after projecting an IO result; adding stdin does
not remove it. Its [explicit array adapters](examples/fp-lean-sort/README.md)
remain available. Feline requires a following filesystem/resource-lifetime slice.

[CapturedStdioChecks](test-java/CapturedStdioChecks.java) exercises actual engine
ownership, bytes, directions, epochs, cancellation, limits and independent fork
cursors. [InvocationOptionsChecks](test-java/InvocationOptionsChecks.java) covers
value snapshots and conversion. The explicit
[stdio acceptance gate](test/stdio_acceptance.clj) compares unchanged programs
and byte/line behavior with official native Lean, and checks artifact admission.
The local acceptance run passes 60 checks across 15 native cases. The
[application-JAR consumer](consumer/StdIOSmoke.java) separately exercises the
public Java and Clojure APIs with the prepared artifact and no native frontend.
Run it from the module with the built SDK plus ordinary dependencies:

```sh
java -Xmx384m -Xss8m -cp "$SDK_CLASSPATH" clojure.main test/stdio_acceptance.clj \
  "$LEAN_SYSROOT" "$PRODUCER_BUNDLE" "$NEW_OUTPUT_DIRECTORY"
```

Native preparation has a separate two-GiB host-MemAvailable admission floor;
this is not a JVM heap requirement. Refusal now reports `ResourceLimit` and the
observed available memory, including whether no native process was started.
