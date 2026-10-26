# Compiled persistent source versions

Status: bounded M6 cache/image fixtures. Separate native A/B elaboration and
source-value evidence are available; hosted source-edit acceptance is separate.
No new loader, invocation engine, handle registry or version store is proposed.

## Native source versions

`lean/CompiledVersionA.lean` and `lean/CompiledVersionB.lean` define the same
`CompiledVersionProbe` names. The exporter receives that same explicit main
module name for both independent frontend runs. A's `sum64` accumulates `acc+n`;
B accumulates `acc+n+1`. Their native source values are 55 and 65 for `(10,0)`.
`entry` and `identity64` retain identical actual IR.

The same-named `chosenOp` declaration changes its actual external symbol from
`lean_uint64_add` to `lean_uint64_sub`; `externCall` retains identical source IR.
The native interpreter cannot run this local external alias without a native
implementation object. Its attempted invocation failed and remains recorded.
The final `main` prints explicitly labeled ordinary UInt64 arithmetic values
13/5, which are source-value oracles, not proof of the custom alias's FFI route.
The exporter still supplies the real changed external declaration/ABI.

See [native export evidence](../measurements/compiled-version-native-export.json).
The fixture streams are exact independent exports, not map-edited positive
evidence. They do not constitute self-hosted Lean compilation or source admission.

## Bounded cache and handle checks

The pure runtime tests use public raw/interop session constructors with explicit
compiler options and a shared code cache. They retain A and B Worlds/sessions,
call old/new/old, resume saved A siblings after B runs, and retain callable
Clojure handles to their original session images. Wrong-image session/World
pairings and stale selected facts reject before adoption.

Each selected invocation must pair the actual typed-tail artifact with its
executed `:specialized` result. Changed sum source or changed actual extern
wrapper dependencies require distinct keys/artifacts; old artifacts remain
usable in their retained image. Unchanged generic `entry`/`identity64` code
reuses the same cached artifact with observable cache hits. A changed multi-root
represented region invalidates as a whole; this does not promise per-root reuse
inside that region. Separate explicit selections isolate the source and wrapper
dependency checks.

Resident FileHandles use the existing identity-frontend model in independently
prepared A/B images. Public `with-externs` preserves each image's selection/cache
and separate host bindings. A handle is called with retained A Context, B with B
Context; cross-generation handles reject before encoding. The actual native
scalar code was preinstalled in those images. The modeled identity loader does
not accept a genuine source edit or establish a self-hosted compiler path.

## Existing actual edit path and remaining acceptance

`program_install.clj` protects all previously installed names (`:203`, `:247`),
and `eval_const.clj:167` only reuses exact previously authorized IR/runtime rows.
Loading different same-name code into an already published image is deliberately
not an overwrite operation.

The necessary clean-image path already exists. `project_loader/open-project`
retains a pristine prepublication native Context. `prepare-load` (`:241`) forks
its retained `:baseline`, not the previously published `:context`, captures the
provider anew once per request and schedules the source graph. `finish-load!`
(`:411`) issues a distinct persistent ProjectVersion. A source edit can therefore
build B from that clean seed while A keeps its Context/FileHandles. No replacement
registry is needed, and a caller may also retain an explicit module seed before A.

The next genuine gate must run that existing path on an accepted current
source/class cohort: load A, change the provider's source, re-elaborate/check B
from the pristine baseline, call B, then call retained A again. Repeat with a
dependent module whose source is unchanged but whose imported dependency changed.
Keep Source/provider leases alive through retained contexts and failure evidence.
Native exports, separate prepared images and modeled FileHandles do not discharge
that gate. General dependent reuse is not established by JIT caller-cache reuse.

There is also a compiler-selection convenience gap: a pristine session cannot
preselect names not yet loaded, and resident currently has no thin selection
setter after loading. The [selection API plan](COMPILER_SELECTION_API_PLAN.md)
separates that small adapter from later FileHandle-bound root discovery. Neither
should mint checking/import authority or eagerly type Init.
