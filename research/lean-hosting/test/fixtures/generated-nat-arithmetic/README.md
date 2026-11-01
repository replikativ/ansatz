# Original arithmetic compiler shape

`HostedArithmetic.lean` and `original-output.jsonl` are the parent's existing
source export from the pinned Lean 4.33.1 cohort. The output contains a manifest
with empty initialization actions and two genuine fdecls for `hostedStep` and its
owned boxed wrapper. The root borrows its Nat, creates tagged 1, calls original
`Nat.add`, and returns the owned result. No compiler instructions were changed.

`original-nat-add.json` is the exact accepted original CAS blob, including its
pretty field; its raw SHA is recorded in `provenance.json`. Its typed Name and ABI
are checked independently at runtime through the actual authenticated demand
resolver and current canonical Header. This fixture does not authorize execution.

The worker copied/hash-checked small metadata only and ran no JVM/native process.
The files are structural models, not a generated receipt from a real filesystem
command. Fresh runtime acceptance remains pending. Upstream Lean is Apache-2.0;
this fixture preserves source facts and original generated declarations.
