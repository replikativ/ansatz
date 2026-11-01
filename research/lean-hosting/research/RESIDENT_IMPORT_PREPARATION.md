# Optional resident import preparation

`prototype.resident-import/prepare-source-import` prepares one published
standalone source module for a later `resident/load-source` call. Together with
[`load-and-publish`](RESIDENT_SOURCE_PUBLICATION.md), it provides a public-API
composition for the experimental two-file case. It remains outside Ansatz's
normal source and AOT paths.

```clojure
(def prepared
  (imports/prepare-source-import published-context
    {:path "B.lean"
     :module-name b-name
     :roots [b-entry]
     :initialization :defer}
    {:profile :standalone
     :configuration independent-configuration
     :kernel-policy {:allow-compiler-markers? true}}))

(def loaded
  (resident/load-source (:context prepared) (:request prepared)))
```

`b-name` and `b-entry` are kernel `Name` values, as in the resident API. A must
already be published in the input Context's world. In this profile A has no
imports; B's actual classic header must request exactly one ordinary exported
import of A. A typical B begins with `prelude` followed by `import A`.

The request accepts exactly one of `:path` or `:text`, an explicit module Name,
roots and deferred initialization. A path is read once as UTF-8; its file name
is used unless `:file-name` is supplied. The returned request contains captured
`:text` and a file name, so a later disk edit cannot change the source between
header inspection and compilation. This operation prepares imports; it does not
compile B or execute inline calls.

## Checking and capabilities

The consumer validates the independently captured resident configuration and the
fixed header parser, guest Name encoder, source assembly/finalizer/header and
kernel projection helpers. It does not install missing code or replace bindings.
The header's structured module identity is preserved, including numeric-looking
string segments. Module names outside the existing lossless classic helper
profile are rejected by its module-name validator.

Assembly resolves the actual source registry entry in this branch and verifies
its admitted unit and executable identities. Genuine guest finalization then
reconstructs the Environment, and the existing whole-map checker freshly checks
its constants and exact source receipt. The returned scalar `:import-receipt`
contains module, unit digest and constant count; it grants no checking authority.

`:kernel-policy` is explicit. The supported keys are Boolean `:allow-axioms?`,
`:allow-unsafe?`, `:allow-compiler-markers?`, and positive `:fuel`. The default
checking fuel remains the existing checker's default when omitted. The example
above admits the three exact compiler markers used by the genuine prelude seed.
Projection certificates and unrecognized policy fields are rejected.

## Ownership and failure

The input Context is locked during preparation and remains open and unchanged.
The output is a new persistent branch with the finalizer-owned Environment and
inherited Options owner. Only the output branch releases the prior Environment
owner. Its prepared packet contains the new live roots and borrowed catalogue;
old certificate/association metadata is not copied onto the new Environment.

Registry region anchors, assembly owners, Context roots and the external Source
lease retain their separate lifetimes. The operation never closes that lease or
unregisters the publication. Guest Name temporaries are released only after
successful finalization. Failure retains the captured request/header, actual
assembly/finalization result, latest helper return/world/session and named owner
states. These are terminal diagnostic records, not permission to replay effects
or infer cleanup from another snapshot.

## Current boundary

The [validation receipt](../measurements/resident-import-validation.json) records
focused tests with modeled parser/finalizer helpers, real guest encoding/raw
execution and production finalization with fresh Java checking of a guest-constructed
closed identity CI, alongside the native mixed-witness fixture. It distinguishes successful checking from genuine ill-typed CI rejection,
receipt mismatch and post-check adoption failure. A separate actual frontend acceptance now passes both public consumers: publish A,
prepare its import with a fresh four-constant strict receipt, compile B, return
Nat42 and Unicode, and retain the earlier A Context. The input Context stays
unchanged. This mutable-backend workflow takes 16.802 seconds, excluding restore
and seed preparation. Five further unprofiled warm trials and one separately
CPU-profiled trial also pass. The shared process then exits successfully under its
original guard (3,590,819,840-byte peak RSS); its 1,362.85-second lifecycle includes
restore, preparation, profiling and idle REPL time. Process disposal does not prove
semantic cleanup of the borrowed Context or Source lease. Full-Init acceptance
through these consumers remains separate.

The API deliberately supports one standalone import. Over-Init preparation needs
a separately authenticated InitPrefix capability, created from the original
checked Init result and its exact verified Store while those are available.
An evolved Context or publication descriptor cannot reconstruct that authority.
Authenticated hybrid native bindings and the external prefix/Source lifetimes
also remain explicit. General dependency graphs, package visibility and prefix
capability packaging remain further work.

## Next: an explicit Init prefix

Extend preparation with a separate capability created while the original checked
Init import result and exact verified attached Source are available. The existing
`source-import/prepare-init-prefix` validates their protected association,
re-derives the complete dependency-first descriptors from that Source, assembles
the prefix and retains its registry owner. A public preparation wrapper should
return the new Context and this borrowed capability together, with explicit
lifetime rules; it must not infer authority from an evolved Context snapshot.

An over-Init import operation can then validate the actual header against that
prefix plus the published A module, call the existing hybrid assembly/finalizer
path with authenticated native bindings, freshly check the resulting Environment
and exact A receipt, and adopt a new branch. The initializer-completion guard and
Source lease remain explicit. Test rejected foreign/stale prefixes, source
shadowing, changed bindings, malformed headers and terminal failures before the
fresh full-Init acceptance. Only after that gate should dependency graphs and
package resolution broaden this profile.
