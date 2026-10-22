# Explicit source capture

`prototype.project-source` supplies host-only source selection and capture for a
future Project loader. It operates on a vector of string Name segments, such as
`["Package" "Module"]`; it rejects numeric, empty, dotted and path-like segments.
It does not read Lean syntax or resolve Lake dependencies or compiled modules.

```clojure
(require '[prototype.project-source :as source])
(def sources (source/provider ["src" "vendor/lean"] 1048576))
(def captured (source/capture-source sources ["Package" "Module"]))
;; Feed (:text captured) to BOTH header discovery and compilation.
;; Do not reopen (:path captured) for compilation.
```

Root selection follows `SearchPath.findWithExt` in `src/Lean/Util/Path.lean`
at Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The first root
containing a package directory or a package `.lean` path owns the package.
If that root lacks the requested leaf, capture fails; it does not fall through
to another root. Roots are canonicalized when the provider is created.

A capture opens the selected regular file once and reads at most the configured
per-file byte limit plus one byte. It rejects oversized or malformed UTF-8 input.
The returned immutable map contains module segments, root index and canonical
paths, text, byte count and a SHA-256 digest of those captured bytes. A later
filesystem edit does not change an earlier capture. These fields describe bytes;
they convey no checked-module, publication or completed-import authority.

The filesystem assumption is cooperative. Canonical containment is checked before
opening; hostile concurrent ancestor or symlink replacement is not prevented.
An in-place edit may produce bytes spanning versions. There is no I/O deadline,
aggregate project budget or multi-file snapshot. A Project coordinator must own
those policies, capture each module once per attempt, parse the captured text
with the actual Lean helper, and schedule dependencies using checked receipts.

This component alone does not load or execute Lean files. Native-only base
preparation, bounded header discovery and the Project coordinator remain separate
integration steps.

The [focused validation](../measurements/project-source-capture.json) passes
7 tests / 41 assertions on both the JVM and Babashka. It covers package shadowing,
exact immutable bytes and digests across edits, UTF-8 and size rejection, empty
files, and symlink policy. The complete optional runtime suite was not rerun for
this independent host-only component; both optional runners register its tests.
