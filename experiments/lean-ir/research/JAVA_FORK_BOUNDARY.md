# Fork capture and branch-local mutation

The Java engine already copies only when `eagerFork` is requested. “Eager”
describes copying the reachable graph during that call, not continuous snapshots
during execution. Keep that implementation as the alias/ownership oracle.

SCI's related design is in `src/sci/impl/world.cljc` and `doc/forking.md` in
the SCI repository. Stable handles select dense lineage-local slots. Fork takes
an exclusive world gate, waits for active forms to finish, copies slots and
cooperatively forks host values. Ordinary SCI fork does not capture a running
continuation; a long form can therefore delay it indefinitely.

The explicit Java driver already stops between instructions. A future concurrent
fork request can rendezvous there, then copy live control state and resume the
parent. It must not copy native Java frames or interrupt a host effect midway.
The recursive driver can remain a closed-call execution strategy in the same
runtime; its active Java stack is not a capture boundary.

Copying only the current register arrays is insufficient. Java `Node` contains
mutable RC, liveness, tag, field and scalar storage. Destruction clears fields;
`rc == 1` enables destructive updates. Both branch isolation and aliases would
break if these objects were shared directly.

## Candidate experiment

1. Give logical nodes stable IDs and put branch-local RC, liveness and payload
   realization in compact dense records. Payload edges refer to stable IDs.
2. At an explicit instruction boundary, copy control state and branch records;
   share program data and frozen payload storage. Keep capture work synchronous
   and on demand. This still costs time proportional to copied state.
3. Before a destructive payload update, obtain private storage and update that
   branch's realization. All aliases must resolve through the same branch record.
4. Treat logical RC=1 and physical payload exclusivity separately. Both branches
   may have RC=1 while sharing frozen storage; each must copy before writing.
5. Keep host effects/resources subject to explicit share/copy/reject policy.
   Include constants, pending applications, result ownership, output and private
   runtime functions in the capture contract, as the current oracle does.

Measure direct execution, slot lookup overhead, capture bytes/time, and sparse
versus dense post-fork writes against the eager oracle. Test aliasing, repeated
forks, destruction, RC=0 persistent descendants, partial applications and parent
close. Consider page-level COW only if copying dense branch records is material;
RC writes can dirty pages even without logical payload updates.

This is a design candidate, not an implemented cheap-fork backend. The Program,
IR semantics and test corpus should remain shared rather than creating another
interpreter implementation. Efficient provider startup/imports takes priority.
