# Bounded regular-file filesystem services

The integration candidate runs the unchanged two-file [Feline tutorial](examples/fp-lean-feline/README.md)
with explicit read-only regular-file services and captured stdin/stdout/stderr.
The same provider now has explicit opt-in regular-file writing. This is a bounded
Linux profile, not unrestricted native IO or a filesystem sandbox.
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

Each Project gets a separate session with real mode-aware FileChannels. Guest
Handle aliases share a channel/cursor. The last guest reference closes the
handle; Project close also sweeps its resource ledger. A failed branch has a
separate stopped-engine retirement certificate before its heap can be discarded.
If a channel close throws, its uncertain resource custody stays in the ledger
and blocks successful retirement; cleanup still attempts the other resources.
An uncertain close is never retried, even if the channel reports itself closed.
This does not execute guest finally blocks or roll back earlier filesystem effects.
A failed/cancelled invocation can leave created, truncated or partly written files,
even when no guest result was published. Effects are never automatically replayed.
Two Projects cannot share session ownership. Public forks remain unavailable;
the internal eager fork refuses a filesystem session.

The default limits are **32 live handles**, **1 MiB per read/line request**,
**16 MiB total physical bytes read**, **1 MiB per write/putStr**,
**16 MiB total physical bytes written**, **10,000 operations**, and **4,096 UTF-8
path bytes**. Total bytes and operations accumulate across the **Project session**,
including repeated calls and buffered prefetch/rereads. `ReadOnlyFiles.limits`
sets the read/general bounds; `FileAccess.limits` supplies the same options and
`writeLimits(perWriteBytes, totalWriteBytes)` sets independent physical-write
bounds. `workingDirectory` selects a relative guest directory. Rewinds/reopens
never reset totals. Partial bytes accepted before a failure count toward writes.
Runtime instruction/time, string/conversion and output limits remain independent.
Deadline/interrupt checks are cooperative; local filesystem calls are synchronous.

The configured root and ancestors must already exist in a trusted namespace
without hostile concurrent path replacement. Writable integrations must trust all
hard-link aliases and exclude concurrent content and namespace mutation during
writable handle use. Hard links can mutate aliases outside the configured root;
this provider is not adversarial confinement. Independent Projects are not isolated
transactions. Construction and opening a Project never create the root or cwd. Guest paths are relative, with no parent components,
symlinks or special-file opens. Metadata can truthfully report a directory, but
opening it is a terminal `FilesystemPolicy` refusal, not native directory-error
parity. Read-only contents remain live rather than snapshotted. Directory operations,
`realPath`, `currentDir`, mutable process cwd, symlink/hard-link creation,
permissions, processes, networking and arbitrary FFI remain unavailable.

Metadata uses public Linux JDK unix attributes: access/modify times, size, type
and hard-link count. The supported domain requires nonnegative sizes/link counts
in the exposed signed JDK ranges and epoch seconds in [-9223372036, 9223372035]
for exact nanoseconds. Exotic filesystem/provider values outside these domains
are unsupported. Compiler-generated layout evidence preserves field placement;
source field order is not the native scalar order.

## Explicit writable authority

```java
HostServices writable = HostServices.builder()
    .fileAccess(FileAccess.readWrite(Path.of("data")).writeLimits(1048576, 16777216))
    .build();
```

`FileAccess.readOnly(root)` and the existing `ReadOnlyFiles.root(root)` grant no
writes. Existing `Builder.files(ReadOnlyFiles)` calls retain that authority.
`Builder.fileAccess(FileAccess)` selects the neutral policy without overloading
the existing `files` method (including its null-rejection source behavior).
`HostServices.files()` remains the compatibility getter for configurations passed
through that facade; `fileAccess()` returns the neutral policy. An artifact carries
neither roots nor write permission. The v2 regular-file descriptor identifies
available audited intrinsics and never grants runtime authority. A read-only
policy refuses non-read opens before creation/truncation with `FilesystemPolicy`.

All five pinned Lean 4.33.1 modes are admitted under explicit writable authority:
`.read` requires an existing file; `.write` creates or truncates immediately;
`.writeNew` uses atomic CREATE_NEW and preserves existing bytes on EEXIST;
`.readWrite` requires an existing file and never creates; `.append` creates when
missing and uses real append for every write, including after `rewind`. On the
pinned Linux runtime, Lean uses open(O_APPEND) followed by fdopen("a"), so the
initial logical cursor is zero even on an existing file. Append writes advance
the logical cursor to their actual resulting EOF; rewind and flush preserve their
ordinary cursor semantics independently of the JDK append-channel position getter.
Creation
uses Linux provider defaults (0666 subject to umask). Only existing ancestors and
an operation-appropriate missing leaf are permitted.

Output is **write-through**, unlike libc FILE output buffering. Bytes may become
visible and failures may surface before native fflush/close. Native parity applies
at explicit synchronization boundaries within this regular-file domain, not to
unsynchronized cross-handle visibility, buffered-error timing or delayed native
truncate anomalies. `write` preserves binary bytes; `putStr` writes exact UTF-8,
including embedded NUL, without newline conversion. UTF-8 extent and request/total
budgets are checked before output allocation/mutation. Physical short writes are
completed in bounded chunks; observed partial acceptance remains accounted if a
later chunk or publication fails. A quota/cancellation refusal does not undo any
prior open or write effects.

`flush` reconciles input read-ahead and synchronizes the logical cursor. It never
calls fsync/FileChannel.force and promises no durability. `rewind` models the pinned
native fseek-to-zero: it clears EOF but preserves sticky ferror. `truncate` sets
length to the logical cursor in the write-through domain; concurrent-shrink cases
that would require POSIX extension are explicitly refused, since NIO truncate
does not extend. Truncation preserves descriptor offset and any input prefetch, as POSIX ftruncate
does; failure to restore NIO's clamped offset is terminal after the mutation.
Read-only truncate yields positive EINVAL without setting ferror.

Update streams require flush or positioning between output and input, and
positioning between input and output unless input encountered EOF. `flush` after
ordinary input does not authorize input-to-output. Known undefined sequences are
terminal pre-effect policy refusals. Aliases share direction, indicators and cursor.

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

Only identified Linux NIO exception types or exact default-provider strerror
reasons receive guest IO.Error encodings (including space, read-only filesystem,
quota and invalid-operation failures). Unknown reasons never become guessed EIO
or EACCES. Disk-quota EDQUOT uses the pinned native default otherError constructor. Metadata
uses negative libuv codes represented as UInt32, while Handle failures use
positive errno. Embedded-NUL filenames use the pinned positive EINVAL case.
Unknown provider failures, limits, cancellation and path-policy refusal stay
terminal host outcomes. General uncaught IO.Error details remain limited to
`userError`; having all constructor factories does not expand the host decoder.

Validation helpers are [filesystem_acceptance.clj](test/filesystem_acceptance.clj).
Native comparisons cover regular files/stdin; policy refusals are tested separately.
The [application-JAR consumer](consumer/FelineSmoke.java) exercises Java/Clojure
without native Lean or source compilation.

The authored [writing application](examples/filesystem-writing/README.md) and
[definitions-only harness](test/filesystem_writing.clj) add source/cache/artifact
and native receipt campaigns, including final file bytes. They are separate from
unchanged Feline provenance. Focused JDK provider tests cover modes, cursor rules,
write budgets, partial writes and resource custody; those checks alone do not
establish public SDK/native parity. Initializer filesystem IO and forks remain
refused. The candidate passes the writing application's source/cache/artifact
campaign against native output and final file bytes, the five supported append
oracle cases, and isolated Java/Clojure application-JAR calls. Native-free
lifecycle checks cover read-only refusal, budget failures after creation or
truncation, and cancellation after actual writes, including resource retirement
and preserved external effects. These are source-tree validation results, not
a claim that older published SDK versions contain this interface.
