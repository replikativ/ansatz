# Closed Java calls beneath resident admission

Status: opt-in research integration, tested with selector and resident boundary
models. Current-head genuine hosted source loading through this tier has **not**
been established. No public default or optional-module dependency changes.

`resident/call` still uses the ordinary World runtime. The trusted internal
`resident/call-with-executor` seam selects an executor under the Context lock,
after the ordinary file/version/readiness/closure/ABI/codec gates and before
argument encoding. Nil alone declines. Invalid selection rejects; executor
failure never retries. Matching completion is validated before it becomes the
authoritative cleanup checkpoint; inconsistent replies remain separately named
diagnostic evidence.

## The first region

Load `java-ir-baseline/repl.clj`, `pure-region.clj` and `pure-provider.clj` in the
research REPL. `java-ir-pure-provider/selector` accepts the isolated Java class
basis. Pass the resulting selector to `resident/call-with-executor` with the
same Context, FileHandle, Name, values and codec signature used by `call`.

The selector resolves the current checked Java Env using the protected guest
kernel helpers, carrying their actual updated World/session. It classifies the
logical source definition, not merely the boxed compiler helper: safe definition,
no universes, exact explicit Nat/String argument/result types. Aliases, implicit,
instance, proof and dependent arguments decline. The classifier does not check or
authenticate arbitrary caller-supplied Envs.

Original admitted rows come from source authorization or the prepared catalogue.
Their legacy lowering must match the current executable image, including parameter
metadata. The first profile is acyclic, boxed, no-extern and excludes dynamic
applications, partial application, globals, joins/loops and sharing observations.
Unsupported profiles select ordinary execution before application entry. This
deliberately narrow integration does not accelerate arbitrary application code.
Adding authenticated stock Nat externs and recursive control flow is subsequent
work, using the existing native route guards and Java dispatch limits.

Each selected invocation creates a fresh private engine. Decode borrows the
legacy Nat/String arguments; only immutable JVM numbers/strings enter and leave
the engine. No Java guest Node, closure, stream, cache or mutable machine escapes.
The Java result is encoded into the actual legacy World. Each owned argument
occurrence is then released once; borrowed arguments remain for resident cleanup.
Failure preserves the latest World, argument vector, remaining owned indices,
entry/stage facts and any encoded result. Private engine abandonment grants no
general failed-frame RC cleanup authority.

`machine/complete-closed-call` publishes canonical terminal controls using the
actual ownership World. It requires identical executable images and unchanged
idle entry/ownership controls. It preserves actual heap and legacy statistics;
it does not pretend the reference machine executed Java dispatches or provide an
instruction-exact checkpoint. Another ordinary call can start from this packet.

Resident cleanup now checkpoints each successful borrowed release and the result
release. A later cleanup or Context-construction failure cannot reissue already
discharged owners. Completed invocation evidence and currently owning obligations
are separate facts. Best-effort diagnostic callbacks cannot invalidate completion.

## Verification and next gate

The bounded checks include large Nats, supplementary Unicode/NUL, owning and
borrowed heap leaves, duplicate/mixed aliases, exact executable identity, invalid
logical signatures, pre-entry rejection, no fallback after execution failure,
encoding/release failure checkpoints and subsequent ordinary execution. The
selector tests are unit models, and resident tests use a modeled compiler transport;
neither substitutes for genuine frontend acceptance.

The [recorded isolated-engine gate](../measurements/java-ir-pure-provider-2026-10-28.edn)
passes 96 test executions / 4,304 assertions in 384 MiB, including the prior
runtime checks and 24 new boundary/selector/ownership model tests. Development
used the retained REPL; one fresh JVM checked final class/namespace isolation.

The next acceptance uses one retained freshly checked provider: load the original
`GraphChainA.lean` Nat/String definitions, demonstrate Java selection/completion,
then edited and retained versions. Extend to arithmetic before claiming useful
project acceleration. The historical full provider needs about 3.7 GiB process
RSS; allocate a bounded provider JVM only when host headroom can support it.
Keep all ordinary development in the small REPL. Do not infer a smaller current
bootstrap heap from small application-region memory.

General heap forking, callbacks/effects, stable Java packaging and bidirectional
DSL declaration/theorem publication remain the later gates in the
[campaign](LEAN_HOSTING_CAMPAIGN.md). The explicit-continuation and recursive
drivers share one Java value/runtime implementation; this adapter is not another
interpreter.
