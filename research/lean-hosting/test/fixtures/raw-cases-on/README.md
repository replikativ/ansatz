# Captured RAW constructor fixtures

The manifest records the pinned Lean commit, actual native full-expression oracle,
raw ModuleData round-trip verification, original JVM matrix and source hashes.
These are test inputs for a constructor, not an admitted Environment or a runtime
profile certificate.

The two deterministic gzip files decompress to portable generic ModuleData DAGs.
Every captured object/node line is unchanged. Only `.olean` filenames in the
external JSON manifest were replaced by logical basenames; original capture and
node-line hashes record that transformation. No original `.olean` file is opened
by the portable tests. Tests bound decompression, verify both byte hashes and
validate the complete DAG before using it.

The program fixtures are the exact captured local IR and 252 authenticated
imported CAS rows. The original extern row remains unchanged. The inspected
closure required no export aliases; this absence is recorded explicitly.
The bounded panic factory text records the exact previously tested trusted HOST
controller prefix in a JSON text envelope. Tests execute a standard Clojure test-support namespace and
verify its implementation body against this inert text after normalizing final
newline framing; they never evaluate the
fixture text as code. This capability does not emulate native stderr/backtraces.

`producers/` preserves the helper, native oracle and transport source used for
these captures. The build recipe text is an archival copy from the repository's
native transport directory, not a script intended to run from this fixture folder.
Regeneration requires the pinned SDK and fresh native verification; updating a
fixture hash alone is not new native evidence. CI consumes these captures and
does not install or invoke a Lean SDK, native exporter or LLVM.
