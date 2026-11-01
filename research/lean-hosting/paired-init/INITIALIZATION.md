# Full Init initialization choices

Pinned authority: Lean 819816b2e0a3bf405af45ae5c7af2491d8f5bee6,
Compiler/InitAttr.lean:159–201 and library/ir_interpreter.cpp:1192–1208.

The pair observes exactly one regular initialization requirement after the original
selected/private + full-IR deduplication: Init.Data.Random's IO.stdGenRef initializer.
The actual declaration/initializer typed names and both part roots are recorded in
source-metadata.json. No builtinInitAttr payload is present. Native init execution
status is not a property of serialized ModuleData, and global presence does not
prove which initializer ran or how often.

There is no passive per-module "was initialized" query in lean_run_mod_init_core.
Its implementation resolves the exact native symbol, calls init_fn(builtin=0),
propagates an IO error, and returns true only for a successful call; absence returns
false. Calling it as a "query" can run an initializer. Individual generated native
module initializers have their own private one-time guards. Returning true in a
Java no-native-symbol profile merely because a captured global exists would change
that profile, and cannot be justified by the current captured image alone.

Option A: new captured-seed producer, explicit native-initialization profile.
Read the genuine interpretedModInits IO.Ref and record membership for all 631
modules, before/after capture, tied to the exact captured graph digest and native
producer/executable/library/symbol cohort. Native-positive status needs an actual
successful original runModInitCore call (module/package/phases and result/error),
not just symbol lookup or name/global presence. Run such native initialization
before capturing the globals that its side effects establish; record every event
and bind the final graph to the event receipt. This creates a NEW seed/profile,
not retroactive authority over the old 534-global seed. The Java import policy
would need an explicit reviewed simulation of those genuine once-only native
initializers with source-coupled captured state, per-module identity/order and
fork lifetime. The original interpretedModInits contents must remain authentic;
do not insert native-initialized modules into it just to skip fallback.

Option B: preserve the current genuine negative native-symbol path and perform
original interpreted fallback. This requires the actual runInit/evalConst path,
the original Random initFn, IO.getRandomBytes(8) through a deliberately specified
virtual entropy provider, ByteArray.toUInt64LE!, mkStdGen, IO.mkRef, and genuine
initialized-global replacement semantics. The entropy bytes are an explicit host
policy input, not inferred/randomly fabricated results. The resulting stdGenRef
will differ from the old captured occurrence; the old owner must retire through
its genuine protocol, and initialized-global lookup/fork/source binding must all
observe the new occurrence. Preserve original insertion into interpretedModInits
and the original exception/partial-state order if initialization fails. A successful
new initialization is not evidence that the old captured initialization occurred.

Recommended research order: finish artifact evidence, keep existing Prelude
experiments, and evaluate the small single-Random-init interpreted path as a
separate coherent runtime feature. If true captured native module reuse is desired,
produce a new source-coupled seed/status receipt rather than altering old receipts.
Neither option is implemented or accepted by this document.
