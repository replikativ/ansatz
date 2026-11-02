# Bounded read-only filesystem services

The integration candidate runs the unchanged two-file [Feline tutorial](examples/fp-lean-feline/README.md)
with explicit read-only regular-file services and captured stdin/stdout/stderr.
This is a bounded Linux profile, not unrestricted native IO or a filesystem sandbox.
Default `Lean.open()` projects still refuse required filesystem services.

The runtime context applies equally to source and prepared-artifact loading:

```java
HostServices services = HostServices.builder()
    .files(ReadOnlyFiles.root(Path.of("data")))
    .build();
try (Lean runtime = Lean.open(services);
     LeanProject project = runtime.loadArtifact(loader, "lean/feline.zip", manifestSHA256)) {
    IOResult<?> result = (IOResult<?>) project.callWith("main",
        InvocationOptions.stdinText("from stdin\n"), List.of("first.txt", "-"));
    // result.value(): UInt32 exit status; raw output: result.stdoutBytes()
}
```

```clojure
(import '[ansatz.lean.jvm HostServices ReadOnlyFiles])
(require '[ansatz.lean.jvm :as lean] '[clojure.java.io :as io])
(def services
  (-> (HostServices/builder)
      (.files (ReadOnlyFiles/root (.toPath (io/file "data"))))
      (.build)))
;; Pass services to (lean/open services), then use the ordinary source/artifact API.
;; (lean/call-with-options project "main" {:stdin "from stdin\n"} ["first.txt" "-"])
```

Artifacts contain the authenticated required IR and compiler provenance, not host
root paths or executable filesystem providers. Opening checks the required
service before entering JVM startup. Source preparation still uses the trusted
native frontend and can execute native metaprograms/initializers independently
of these runtime permissions. Filesystem operations during JVM initialization
are refused in this first profile.

Each Project gets a separate session with real read-only FileChannels. Guest
Handle aliases share a channel/cursor. The last guest reference closes the
handle; Project close also sweeps its resource ledger. A failed branch has a
separate stopped-engine retirement certificate before its heap can be discarded.
If a channel close throws, its uncertain resource custody stays in the ledger
and blocks successful retirement; cleanup still attempts the other resources.
An uncertain close is never retried, even if the channel reports itself closed.
This does not execute guest finally blocks or roll back earlier reads/output.
Two Projects cannot share session ownership. Public forks remain unavailable;
the internal eager fork refuses a filesystem session.

The default limits are **32 live handles**, **1 MiB per read/line request**,
**16 MiB total physical bytes read**, **10,000 operations**, and **4,096 UTF-8
path bytes**. Total bytes and operations accumulate across the **Project session**,
including repeated calls and buffered prefetch/rereads. `ReadOnlyFiles.limits`
sets these bounds; `workingDirectory` selects a relative guest directory.
Runtime instruction/time, string/conversion and output limits remain independent.
Deadline/interrupt checks are cooperative; local filesystem calls are synchronous.

The configured root and ancestors must be a trusted namespace without hostile
concurrent path replacement. Guest paths are relative, with no parent components,
symlinks or special-file opens. Metadata can truthfully report a directory, but
opening it is a terminal `FilesystemPolicy` refusal, not native directory-error
parity. Changing ordinary file contents is not snapshotted. This profile does
not grant writes, directory enumeration, processes, networking or arbitrary FFI.

Metadata uses public Linux JDK unix attributes: access/modify times, size, type
and hard-link count. The supported domain requires nonnegative sizes/link counts
in the exposed signed JDK ranges and epoch seconds in [-9223372036, 9223372035]
for exact nanoseconds. Exotic filesystem/provider values outside these domains
are unsupported. Compiler-generated layout evidence preserves field placement;
source field order is not the native scalar order.

Read/getLine share a buffered cursor; lines include LF and preserve CR/NUL.
Invalid UTF-8 uses the pinned native-style recovery rule. Empty writes succeed
without mutation; nonempty writes/putStr on read-only handles produce the guest
bad-descriptor error. Flush synchronizes the buffered read position; regular
file TTY detection returns false.

Failed nonempty write/putStr sets the handle's sticky FILE error indicator, as
in the pinned native runtime. Positive byte reads, zero-sized reads, empty writes
and flush do not clear it; an empty EOF result from a nonzero byte read does.
Native getLine checks this indicator even when it read bytes successfully, then
uses the thread's ambient native errno, which this JVM provider cannot reproduce
faithfully. Therefore getLine while that indicator remains set is an explicit
terminal `FilesystemPolicy` refusal before consuming the line. It does not
invent an errno or return a false success. Calling getLine in the sticky-error state
is outside the supported profile; ordinary reads and subsequent empty-EOF
clearing remain supported. Identified provider read failures also preserve the
indicator. This does not affect unchanged Feline, which never writes to its
read-only file handles.

Only identified Linux NIO failures receive guest IO.Error encodings. Metadata
uses negative libuv codes represented as UInt32, while Handle failures use
positive errno. Embedded-NUL filenames use the pinned positive EINVAL case.
Unknown provider failures, limits, cancellation and path-policy refusal stay
terminal host outcomes. General uncaught IO.Error details remain limited to
`userError`; having all constructor factories does not expand the host decoder.

Validation helpers are [filesystem_acceptance.clj](test/filesystem_acceptance.clj).
Native comparisons cover regular files/stdin; policy refusals are tested separately.
The [application-JAR consumer](consumer/FelineSmoke.java) exercises Java/Clojure
without native Lean or source compilation.
