# Generated mutual declaration checkpoint

This source checkpoint extends the checked adapter to original
`Declaration.mutualDefnDecl` (tag5). It does not permit unsafe or partial source
commands, arbitrary unsafe axioms, opaque declarations, quotient initialization
or inductive declarations. Existing safe-single projection and publication paths
keep their prior rules. Worker validation is source-only; coordinated model and
actual guest-command execution remain pending.

Pinned Lean819816b2e0a3bf405af45ae5c7af2491d8f5bee6 defines tag5 as a proper list
of DefinitionVal. Native safety bytes0/1/2 are unsafe/safe/partial; Java uses1/0/2.
The new general value projection preserves exact names, ordered universes, type,
body, hints and `all` metadata. The old safe-single projection is unchanged.
The actual list defines this group; `all` is retained, not rewritten or used as
a replacement for its membership.

`TypeChecker.checkMutualDefinitions` already implements the native group rule:
require uniform non-safe safety and ordered universe parameters, check every
header against the old Env, install all headers, then check every body against
the extended Env. Duplicate/shadowing names, invalid types/bodies and mixed/safe
groups fail. The adapter bounds one group to256 members and the aggregate local
domain to its existing explicit declaration limit. The checker fuel remains a
bounded per-check policy, not native heartbeat parity.

One actual ELAB request produces one atomic candidate snapshot, publication and
version. Every member has its actual original payload in the candidate map.
Publication uses the existing genuine `postCheckMutualDefinitions._boxed` once;
full checkedConstants readback must preserve the complete old+new domain and
every member's name, kind, payload identity, safety and checking shape before
commit/reply. Original borrowed declarations remain anchored through helper
and callback-capable cleanup. Failure does not partially commit members or
silently unwind an uncertain operation.

The publication helper is already present in the authenticated252-row Shim
stream, SHA93a58e710315bb140f3799695aeeaaa687f6fd9cca1f3acc1f06660059de8a0b.
The current tracked Shim source is byte-identical to its accepted source,
SHA8d4fa0f2c8cd8b38ae1637945521a584c2f90de0a3820a1ef8b812d993f7ec03.
The boxed helper row SHA is
207d5e16f064f53671ef724b88884d10de17b762021631371842069739805536;
its ABI is owned object,owned tobject→object. Its raw original declaration
borrows the Declaration. Header/HostGuest policy selection still requires the
actual authenticated helper and is not inferred from the tracked source text.

Generated admission additionally requires an opaque private-registry M1 scope.
M1 creates it only after the actual parser-error helper returned false, the
actual source GateReceipt was accepted and the Unit reply succeeded. Its dynamic
binding exists only around the actual process-command runtime dispatch. Each
borrow checks the same live engine/source/adapter/private file marker/command
index, current unclaimed ELAB request and actual root Header. The still-issued
source gate must describe a nonterminal command; EOF/exit/import and closed
providers cannot grant this permission. Scope registry entries weakly reference
the Run holder, and completion/failure revokes the scope. No public Boolean,
function-name heuristic or empty token constructor authorizes a group.

Eight model families exercise actual projection/strict Java group checking,
invalid groups, original-payload readback, atomic candidate construction and
mocked scope/lifecycle negatives. These models are not source-parser output,
native publication or runtime acceptance. Root's retained runtime executed all
eight models with54 assertions successfully. A genuine recursive source reached
completed checked publications, then exposed the earlier incorrect linear-history
assumption; that failed command did not issue a receipt and was not resumed.
The separate DAG correction validates all branches and selects the actual final
map. A fresh actual recursive command/file acceptance remains required.

The next distinct families remain separate work: safety-specific single unsafe
definitions, safe opaques, canonical quotient generation, and complete source
inductive generation/encoding/reprojection/publication. Existing imported-CI or
Java checker support alone does not enable their frontend adapter paths.
