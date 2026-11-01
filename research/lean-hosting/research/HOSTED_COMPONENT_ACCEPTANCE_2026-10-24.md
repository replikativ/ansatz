# Hosted Project component acceptance, 2026-10-24

The new 1983 runtime completed genuine Project Nat/String callbacks and the P1/P2
native-reset and retained-version gates in one guarded warm session. A later
chain harness error ended that session with exit 1. These are accepted components
within a failed capture, not a successful whole campaign or normal session cleanup.
The [portable evidence record](../measurements/hosted-component-acceptance.json)
keeps component results and the terminal failure separate. The earlier
[standalone 42e3 P1](../measurements/public-project-p1.json) remains an independent
successful exit 0 run; its receipt is not acceptance of the new runtime.

## What executed successfully

Fresh strict checking covered all 65,994 Init constants with the existing explicit
15-assumption policy. The actual restored frontend/compiler, source publication,
Java checking and final checked imports ran through public Project APIs; these
were not modeled compiler transports. The fixed runtime was Lean 4.33.1 source/IR
on the mutable Ansatz backend with a 3 GiB heap. Its selected consumer was
`19836dccbf0b9edcb0bea2f87cfa4a46d8792eab1a1cf5f1010f53f2fec0bbcb`, with
unchanged c32 caller,257 runtime rows and48 historical Java class files.

The application branch loaded actual `ProjectAppAbiA.lean` using two explicitly
admitted value-only host bindings. Public calls entered Lean, called the Clojure
Nat/String functions, and returned through Lean:41→42, a Nat above 64 bits→its
successor, empty String→itself, and `λ 🦉`→itself. Host counters stayed zero during
compilation and became exactly 2 Nat + 2 String callbacks during the four calls.
All four child Projects, both application Projects and four application-owned
Context wrappers closed normally. The original admission/baseline Source stayed
borrowed. Large Nat value correctness is not a claim about physical MPZ boxing.

P1 loaded actual `GraphChainA.lean`, issued its FileHandle/Project and returned
Nat41 and the Unicode input through two distinct, closed child versions. Its
parent remained retained for P2. A separate public-call profile also closed its
16 call children and eight baseline forks; those samples do not change the P1
controller's semantic call-count 2.

P2 loaded independent roots A and D, including actual native Init reset and a
fresh checked final union. Issued readiness covered 631 native modules and matched
the captured ordered-selection descriptor. Current-version calls distinguished
D's Nat+100 and String-doubling semantics from A's identity functions. P2 closed,
then two calls on retained P1 still returned its old values. All six P2/current/
retained call children closed. The original P1 finish then closed both its parents;
P2's passed result followed. Native query order and final guard parity were not
independently observed, and the record does not claim either.

## Where the session stopped

The next three-file chain loaded and issued an actual Project, and A42 / B52 / C152
assertions and their three call-child closures completed. The harness then passed
a `java.nio.file.Path` to `clojure.java.io/input-stream` during its late source-hash
check. That adapter does not accept Path. The escaping IllegalArgumentException
made the guarded REPL terminal; it was not bypassed or retried. The chain stage
never returned, and its empty/loaded parent Projects did not close normally.
Post-disposal hashing independently matched all three written files to fixtures,
but that does not complete the failed stage's lifecycle assertions.

The guard disposed the process after 8,874.276 seconds, with exit 1, peak group RSS
3,698,782,208 bytes and minimum system available memory 1,394,003,968 bytes. This was
a harness failure, not a memory/fuel guard stop. The borrowed baseline Context,
Source and lease did not receive normal whole-session shutdown. Process disposal
is separate from logical resource cleanup. Split chain profiling, diamond loading
and semantic edit/reload were not executed or accepted.

The terminal postcheck records all 1,293 unique initial/externally admitted inputs
matching after disposal; independent review streamed that exact union again.
The 16 raw journal records form a verified hash chain through the failed stage and
failed session close. A supplemental pin-map file was saved after disposal to
make the audit reproducible; it did not change original launch membership.
Hashes for the actual plan/payload, app/P1/P2 results, terminal receipt/postcheck
and journal are preserved in the portable record.

## Performance and next gates

Restore plus fresh checking took 327.111 seconds. P1 public loading took 563.520 seconds
and its two controller calls 363.122 milliseconds. These are scoped integration
observations, not competitive benchmarks or native slowdown ratios. P2's stored
`advancing-load` timing is a recent slice, not total P2 elapsed time. Neither
heap deltas nor group RSS establish allocated bytes or retained dominators.

Before another long run, a bounded harness smoke must execute actual String/File/
Path inputs, written source hashes and complete post-run assertions with explicitly
modeled transport. Lexical balance alone missed this failure. Preserve the failed
capture, use fresh stage files and outputs, and run actual reader/compiler checks
under the coordinated small-JVM lane. Never reuse a failed stage or invent cleanup.

The next real gates are complete chain closure/profile, diamond and changed-source
reload with retained old versions; owned failed-operation disposal; synchronous
typed EIO/IO host callbacks; coherent source-inductive/structure activation; and
packaging/Java bindings. General packages, local initializers, arbitrary external
IO, production memory/resource behavior and competitive performance remain outside
this accepted profile. No release or whole-campaign completion is established here.
