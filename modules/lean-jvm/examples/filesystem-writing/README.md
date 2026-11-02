# Ordinary regular-file writing application

This is an Ansatz-authored application and native differential probe, not an
upstream or third-party application. `WriterLib.lean` uses ordinary `Init` IO:
it reads text and binary input, writes transformed output, creates a new file,
checks the existing-file error, updates/truncates binary output and appends a log.
It exercises all five modes and UTF-8 with embedded NUL. Each output handle is
explicitly synchronized before observations. No custom externs or IO replacements
are used. `Main.lean` and `NativeOracle.lean` call the same `runWriter` definition.

The definitions-only [harness](../../test/filesystem_writing.clj) provides separate
source/cache/artifact and native campaigns over fresh equivalent trees. It records
stdout, stderr, exit, source hashes, and final bytes for every regular file.
Loading the harness creates no files, projects, JVMs or native processes. Native
campaigns retain the 2 GiB available-memory floor and bounded processes. The pinned native compile/oracle campaign passed with `bytes=2; exists=17` and
retained final-file receipts. Source/cache/artifact and Java/Clojure consumer
campaigns still require a rebuilt SDK; provider tests and native execution alone
do not establish public SDK parity. [provenance.json](provenance.json) records
the authored source hashes and native runtime pin.

The pinned Feline application and its provenance remain unchanged as read-only
regression evidence. See [FILESYSTEM.md](../../FILESYSTEM.md) for the write-through
compatibility domain, explicit host authority, side effects and deferred APIs.
