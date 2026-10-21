# Optional resident source publication

`prototype.resident-source` adds `load-and-publish` over the existing public
resident APIs. This is an experimental consumer, outside Ansatz's normal source
and AOT paths. It does not replace the authenticated runtime or change the
producer checkpoint's build identity.

The existing `resident/load-source` returns an admitted FileHandle, but discards
the full successful compilation packet. Source publication needs that actual
packet: its original Environment, envelope, unit and executable identities cannot
be reconstructed from the handle or content digest. `load-and-publish` compiles
once and registers the result immediately, before dropping the previous
Environment owner in the returned branch.

```clojure
(publication/load-and-publish context request
  {:profile :standalone
   :configuration independent-configuration})
;; => {:context ..., :success ..., :diagnostics ..., :file ...,
;;     :publication {:module ..., :unit-digest ..., :profile ...}}
```

`request` has the existing resident source request shape: explicit text, file
name, module Name, roots and initialization policy. Publication requires
`:initialization :defer` and accepts no inline `:calls`. Both supported profiles
require initializer-free classic source modules; requiring deferral prevents
initializers from running before that restriction is checked. Compilation can
still execute elaborator code and explicit host callbacks. This operation does
not provide effect rollback.

`:standalone` requires no imports. `:over-init` requires the exact supported
ordinary Init import profile. These select the existing production registration
operations; they do not accept arbitrary dependency graphs or module-system
visibility combinations. Registration rejects an already-published module name
in the same branch. Editing a published module starts from an earlier fork.

## Configuration and publication authority

The configuration must independently capture the trusted functions, host
bindings, selected kernel helpers and frontend configuration required by
`resident/adoption-readiness!`. The prepared snapshot supplies the borrowed
catalogue. Publication additionally validates the exporter, guest Name encoder,
both pinned IR-export targets, and the fixed root,
constant-map and quotient helpers used by source registration. Their transitive
executable closures must match the independent registry. This consumer does not
load missing helpers, infer trust from the compilation world, or replace host
bindings.

Actual registration checks the successful compilation packet against the target
world: original unit object, admitted executable identities, Environment payload,
protected checking association, requested imports and initializer actions. A
same-content unit from an independent branch is not interchangeable. The returned
publication descriptor borrows registry metadata; it grants no extra authority.

Publication and import preparation are distinct operations. Publication stores
actual owned ModuleData and retains its Environment in the world's registry. It
does not rebuild the next file's imported Environment. Assembly, guest
finalization and strict checking remain necessary before compiling B against A.
The [actual source-fork experiment](../measurements/prelude-semantic-forks.json)
establishes that lower-level path separately from this new API.

## Persistent branch ownership

The operation locks its input Context and derives a new persistent branch, as
`resident/load-source` does. The original Context remains open and unchanged.
The new branch inherits its Options owner, receives the compiler-owned new
Environment and releases the previous Environment owner only in that branch.
Publication retains its own Environment owner and owns its ModuleData. Public
`resident/adopt-prepared` then adopts the resulting branch's Context roots.

FileHandles borrow admitted unit identity. Closing a Context consumes its
Environment and Options owners; it does not unregister publications, invalidate
independent forks, or close the externally owned artifact Store/source lease.
Those resources must outlive all users.

Ordinary compilation failure does not publish. A diagnostic Context can be
returned only when its actual partial Environment has a live checked
association. Otherwise the operation preserves the actual completed packet in
terminal failure evidence instead of constructing an unchecked Context.

Exceptions retain the input snapshot, actual completed compilation, any completed
registration, latest helper result/world/session, operation phase and named root
ownership states. Lower-layer failure checkpoints remain intact. These are
diagnostic ownership records, not permission to retry guest effects, splice
snapshots or infer cleanup from an older world. No borrowed source lease is
closed by the consumer.

## Validation boundary

The [validation receipt](../measurements/resident-source-publication-validation.json)
records the focused tests, full prototype suite, source hashes and independent
review. Actual frontend acceptance of this operation is tracked separately.

Focused tests model the frontend/export environment while exercising captured
native identity IR, guest Name encoding, raw execution, production registration,
modeled starting Java Environment associations and resident calls. They do not
perform fresh kernel checking themselves. They distinguish that boundary
from a genuine full-frontend execution of the new API. The fresh prelude source
fork result above already runs the real frontend, but uses the lower-level
orchestration; a separate acceptance run must exercise `load-and-publish` itself.
