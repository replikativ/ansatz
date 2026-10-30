# Original sequential frontend on the Java interpreter

The pinned authority is Lean `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
(4.33.1). This gate uses original `Lean.Elab.Frontend.processCommand` IR,
not a replacement parser/elaborator or the earlier Clojure-hosted frontend.
It is separate from complete `Lean.Language.Lean` file/snapshot support.

## Acceptance sequence

1. Construct the real guest environment and original parser/command state.
2. Process `prelude\naxiom HostedSort : Sort 1\n` with `Elab.async=false` and
   `debug.skipKernelTC=false`. Require actual successful checked kernel admission,
   correct ConstantInfo/type, and per-command diagnostics before processing EOF.
3. Extend the corpus to a theorem and executable definition, including rejected
   inputs. Keep logical admission separate from executable IR publication.
4. Add matching imported environments, module IO, and representative project files.
5. Complete queued tasks/pending waits/snapshots and full file diagnostics.

The sequential entry does not import modules, initialize the frontend, or preserve
whole-file diagnostics automatically. Its top-level elaborator resets messages;
end-of-file success or environment membership alone is insufficient evidence.

## Runtime observations

The integrated synchronous runtime passes 87 suites / 867 test executions /
23,979 assertions in an isolated Java 11 jar with a 384 MiB heap. Its separate
[original-program oracle](../measurements/java-sync-task-oracle-2026-10-30.edn)
validates bounded synchronous dependency behavior, not declaration elaboration.

In a retained 384 MiB REPL, the original sequential frontend's setup completed:
real input context, parsed `prelude` header without imports/errors, genuine
`mkEmptyEnvironment` payload, original `setMainModule`, options, command state,
and state Ref. Only the ordinary four-field Frontend.State record was assembled
by the research adapter from source-verified fields; no frontend body was replaced.

The first `processCommand._boxed` attempt stopped at the unsupported original
`Lean.profileit` extern. The accumulated probe budget at that boundary was
302,957 interpreter work units and 494 additional demanded code bodies (excluding
196 bodies already demanded for the parent environment). No checked declaration
or complete command result was established. These are demand/work counts, not
speed or allocation measurements.

## Value and ownership boundaries

`Lean.mkEmptyEnvironment` returns an IO result: the successful wrapper has tag 0,
one object field and no scalar bytes. The environment payload has tag 0, eight
object fields and one Bool byte. Retain the payload before releasing its wrapper,
or borrow it while the wrapper's owner remains live. A constructor tag alone does
not establish a guest type or Java-kernel association.

The first research attempt mistakenly supplied the wrapper to `setMainModule`;
it failed before declaration processing. The corrected attempt above uses the
payload, and the harness now checks its layout before guest calls. Similarly,
the earlier genuine-environment release experiment released the IO wrapper
containing the environment; it was not a direct environment-root release.

The idle prepared parent is retained. Experiments fork all external roots,
including the owned IO result, so a terminal failed child does not force another
JVM launch or parent reconstruction. Code catalogue storage stays host-scoped.
Failed states preserve diagnostics; arbitrary failed-state unwinding is not claimed.
