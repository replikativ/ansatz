# Native startup evidence fixtures

Source fixtures, not accepted output. No author Lean/JVM execution has occurred.
Compile using the configured pinned official 4.33.1 toolchain/exporter under the
root's bounded native slot, in a fresh private module output directory. Preserve
actual per-module source/local stream/olean/IR hashes and process receipts.
Do not replace the accepted entry-helper corpus or binaries.

| Input | Required gate |
| --- | --- |
| Init-request.json | Actual ordinary Init metadata, one selected Random named pair, original60 closure coverage plus genuine boxed/codec rows |
| StartupNamed.lean | Additional actual named numberRef/action tuple and native IO(target type) proof |
| StartupAnonymous.lean | Actual anonymous regular pair and IO Unit proof; unsupported activation, never fake target publication |
| StartupBuiltin.lean | Preserve actual builtin tuples; unsupported activation, never append to regular loop |
| StartupPhase.lean | Preserve module's original meta/runtime declarations and actual effective phases under ordinary private import |
| SelectionChecks.lean | Pure source-selection models: duplicate first/IR lists and phase matrix; no fabricated module attrs |
| header-ordinary.lean | No prelude/module; explicit ordinary import plus original inserted ordinary+meta Init |
| header-prelude.lean | Actual prelude token; no inserted Init prefix |
| header-explicit-meta.lean | Actual module+prelude+explicit meta flag distinct from automatic Init meta import |
| header-module.lean | Actual module mode; original public import flags |
| header-invalid-meta.lean | Original legacy meta-import parser error, header=null |
| header-invalid-all-public.lean | Original public+all parser error, header=null |
| header-crlf-unicode.lean | Exact CRLF/Unicode byte extent and original raw parser/source spans |
| header-quoted-name.lean | One literal string component A.B; do not split into two module components |
| invalid-meta-request.json | Refuse meta substitution before import |
| invalid-profile-request.json | Refuse unsupported mode before import |
| invalid-numeric-module-request.json | Reject Name.num module component before path resolution/import |

Additional root gate: supply exact CRLF and Unicode/comment header bytes, not
line-normalized copies, and assert sourceUTF8Bytes/parserEndByte/spans. The helper
does not run entry or initializer actions in Java. Native module imports may
execute genuine native initialization while gathering metadata; record that
effect boundary rather than calling these fixture imports metadata-only.
