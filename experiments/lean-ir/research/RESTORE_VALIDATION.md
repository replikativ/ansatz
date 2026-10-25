# Checkpoint world validation allocation

Four eligibility checks in `restore-consumer/world!` now use the codec's
validation visitor instead of building and discarding transformed wire values.
The same reference, range, heap-node, quiescence and finalizer-root checks still
run. Validation returns the original World and preserves its function bodies and
guest Refs. Custom sequences retain the codec's existing transforming fallback.
`preparation!` still returns its transformed wire representation.

A JVM component experiment measured approximately **28.6% less allocation** for
this validation workload. Elapsed timings varied in both directions; they do not
establish a speedup.

| Median allocation per 20 validations | Bytes |
| --- | ---: |
| Previous `world!` | 66,678,720 |
| Validation-only calls | 47,598,840 |

The experiment called the actual old and new private `world!` functions on one
prebuilt, valid **modeled** World. The baseline was the complete module at
`167e5ded`, with only its namespace renamed; the changed module was `c9cbc17`.
It used ThreadMXBean current-thread allocation counters, five warmup batches per
variant and seven alternating paired trials of twenty validations. Decoding,
world construction, tests and file I/O were outside the measured batches.

The model retained unchanged payloads from 39 previously authenticated checkpoint
frames: sixteen functions, fourteen heap nodes, five globals and four imported
declarations, totaling 38,934 input bytes. It added **32 synthetic referent nodes,
four synthetic closure-target functions and two finalizer wrapper nodes** to make
the sampled graph valid without loading the complete archive. The resulting
World contained twenty functions, 48 heap nodes and five globals. The four
imported declaration payloads were retained, but this particular `world!` gate
does not walk their bodies.

This measures allocation during small modeled-world validation. It does not
measure full restore latency, a complete authentic World, retained-heap savings,
Java kernel checking, guest execution or frontend performance. Historical sample
artifacts and the comparison harness remain external experiment inputs; they are
not required for the portable tests or distributed as a full checkpoint fixture.

The component gate passed **19 tests and 284 assertions**, including old/new
acceptance and error parity, unchanged authentic payload identities and existing
codec regressions. It used a 384 MiB Java heap and 768 MiB process-group RSS cap.
The guarded process exited and was disposed; all 349 input pins matched afterward.
Evidence identities:

- Plan: `539d538c370d7b2df39bb3e46112e7bda31dba69aa34938d7d9b9eebf912d178`.
- Results: `2287ab79ecaf1427f837214e711a8cddb9942752b4c5e52bf51990ae0c5cee29`.
- Receipt: `79657615780e0b5f4f44e1407e42b4de849faab5a3ae7ac59eb0851d767421c1`.

The five [portable whole-world tests](../test/prototype/restore_validation_test.clj)
cover all four changed callsite families, identities, malformed values and
metadata, custom sequence fallbacks, live/dead references, range boundaries and
the retained preparation transformation. They run with the twelve codec tests
through [bin/run-unittests](../../../bin/run-unittests), in a separate JVM with
experimental paths scoped to that process. The normal experimental test runner
also includes them. These tests require no historical checkpoint, Lean SDK or
native Source.
