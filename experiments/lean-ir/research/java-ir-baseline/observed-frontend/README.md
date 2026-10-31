# Observed original frontend command companion

`lean/ObservedFrontendCommand.lean` is a separately authorized source companion
for Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. It is not an
alias or replacement-body claim for `Lean.Elab.Frontend.processCommand`.
The companion follows that pinned function's parser, state updates and original
`elabCommandAtFrontend` call, with one explicit pre-elaboration host boundary.
`contract.json` fixes its actual exported ABI/layout and source policy requirements.

The parser executes once, through the original `Parser.parseCommand` in the
original profiling composition. The actual parser Syntax and MessageLog are
passed to a mandatory local `BaseIO Unit` extern **before** original top-level
elaboration resets messages. The original elaborator executes once after the
reviewed gate replies. The returned owned Observation retains that same Syntax,
parser state/log, final elaboration log, actual InputContext, original pre-command
Frontend.State and UTF-8 start/end positions. It distinguishes eoi, exit, import
and other commands. An explicit exit or a late import never establishes EOF.
These source/IR call facts are not a runtime acceptance measurement.

## Build and admit a new source cohort

From `experiments/lean-ir`, with the pinned toolchain available:

```sh
python3 scripts/produce-observed-frontend.py \
  --exporter /path/to/accepted/lean-ir-export \
  --output target/observed-frontend-source-1
```

The exporter must have the already reviewed SHA fixed in the runner. The runner
pins the actual 4.33.1/commit toolchain and its standard library search path,
sets one Lean thread, monitors resident memory at 1.2GiB and system MemAvailable
at a 1.5GiB floor, and applies finite CPU/wall/output limits. It never invokes the
companion, runs a source `main`, builds a new linked image, imports a checkpoint
or exports an imported closure. Outputs include exact copied source, original
`local-ir.jsonl`, `export-receipt.json`, complete headers, a compiled layout/call
site audit, `overlay-spec.json`, and a last-written bundle manifest. Failed
attempts leave diagnostics and no admission candidate manifest. Output directories
must be new, preserving earlier evidence.

Authenticate this bundle with the existing
`ansatz.research.ir.source-setup/authenticate-overlay!`, supplying independently
reviewed expected pins, actual source and accepted exporter paths. The generated
spec describes the source-setup keys but is not self-authenticating permission.
The source overlay must be included in a NEW ordered composite CodeReceipt before
minting its SourceBinding and parent. Never append it beneath an existing live
Source/Run or bypass the maximum overlay bound. The bundle's raw row SHA hashes
exclude the trailing newline, as required by the existing source setup.

The exported local initialization plan is empty. Closed literal Name/String
helpers retain their actual `closed` metadata and normal cache lifecycle. No
kernel environment association or checking claim is created by this overlay.
Its new gate is a policy-specific host specification; it is not in the original
375258-row catalogue or the descriptor bootstrap's original extern inventory.
The caller must register this exact ABI before issuing its canonical Header.

## Gate and ownership contract

Actual gate symbol: `ansatz_observed_frontend_gate_v1`. Its raw ABI is five borrowed
parameters `[object, object, tobject, object, object]`, then an owned erased-world
`void`, returning `tagged`. The five semantic values are actual InputContext,
pre-command Frontend.State, parsed Syntax, returned ModuleParserState and parser
MessageLog, in that order. Success is direct Unit `Long0`, not an invented
IO.Result wrapper. All object arguments are borrowed. Retain explicitly before
keeping any beyond the paused call; release each actual owner through the normal
resumable protocol. A rejected/unhandled gate leaves a paused request/journal,
not a rewindable parser state or a successful command. It has no default handler.

The provider must verify the current actual request, canonical gate Header,
Source/receipt/engine/branch/Program and expected original companion invocation.
`compiled-layout.json` records the unique main FAP site and its successor original
elaboration call, including exact variable bindings. At suspension the active
canonical main Function/prepared body, request destination and actual next Body
must match; checking only the extern's symbol or ABI does not prevent a direct or
spurious gate call. Root and consumer integration must validate the real runtime
fields rather than reconstruct a Body from JSON as an authority token.

Observation ctor is tag0, eight object slots and four scalar bytes. Object order:
input, before, command, parsed, parserMessages, elaborationMessages, startPos,
endPos. Booleans at bytes64..67 are terminal/eoi/exit/lateImport. The companion's
actual declared types and original emitted constructor/stores pin this layout;
the consumer still checks real liveness/kind/field identity, not only size/tag.
A successful call returns its original IO/EST result around that owned object.
Elaboration exceptions can prevent Observation return; retain the actual parser
occurrences and request history in the host journal before approval so that
failure cannot hide diagnostics or fabricate cleanup.

## First structural policy and remaining boundaries

The reviewed host gate policy inspects the actual borrowed Syntax with explicit
node/depth/Name/byte bounds. It does not accept a caller Boolean or regex-derived
root/body. Initially allow admitted standard definition/theorem/axiom roots and
namespace/section/end commands, retaining existing declaration-kind restrictions.
Deny all command/term/tactic `set_option`, including nested/local forms, and
`unlock_limits`; deny initialization, plugin, extern/export/meta/attribute/custom
command requirements outside the separately reviewed profile. Attribute syntax
such as `noinline` needs an explicit admitted rule, never blanket attribute
permission. No change to original compiler callback identity, effective protected
options, source map/version or strict checking guards is implied by this helper.
Imported/custom macro expansion that mutates options requires an additional
actual-consumer proof; a source spelling policy is not universal macro authority.

The consuming controller keeps the actual parser MessageLog from the gate and
checks it separately through original `MessageLog.hasErrors` at a normal root
boundary, comparing exact log/Syntax identities against the returned Observation.
Post-elaboration messages cannot replace this check: original elaboration resets
its log. A recovered parser error may leave checked publication history, but must
prevent successful CommandReceipt/file issuance. The provider can deny visible
errors before elaboration when it has authenticated error observation there;
it must never infer success from final recovering=false or Syntax.hasMissing=false.
The final elaboration/compiler log, real eoi at captured UTF-8 end, effective
options and all strict versions remain separate mandatory checks.

## Required coordinated runtime probes

No JVM is launched by the producer. Before accepting general file capability,
run the real gate/companion on empty/comments-only, namespace/end with Unicode,
ordinary definition and theorem commands; verify original parser and elaborator
execution, exact root identities and ownership cleanup. Negative cases: syntax
error recovered before a valid command, unterminated trailing comment, explicit
exit with remaining input, late import, nested/local protected options, unsupported
custom macro/attribute and spurious direct gate calls. Record actual parser and
elaborator diagnostics separately, including failures after checked publication.
This helper supplies observation, not the v0 association, strict publication,
complete generated IR, callable entry, module import or finished-file authority.
