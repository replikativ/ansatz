# Original Expr constructor roles for private machinery

`original-rows.json` contains nine authentic constructor functions and the
original ExprMVars extern as **negative capability evidence only**. The runtime
does not register that extern. These rows do not establish Expr metavariable
instantiation or a frontend capability.

The nine roles are bvar, sort, const, app, lam, forallE, letE, mdata and proj.
Lam/forallE/letE use their genuine owned `_override._boxed` wrappers so all
helper arguments travel in object slots, including canonical tagged flags.
The other six use their original raw `_override` functions. Constructors compute
their real cached words through unchanged original IR and existing primitives.

Every row was reread from the original CAS, SHA-checked and matched by exact typed
Name against the accepted index. `provenance.json` pins Lean commit, index, raw
per-row identities, normalized fixture and relevant source files. Only optional
top-level `pretty` was removed. Upstream source is Apache 2.0; see `LICENSE`.
The focused suite combines this selection with existing original Expr constructor
fixtures; it does not restore an image or export all frontend declarations.

The `model-setup-*` copies in tests have distinct Names and descriptive test
hashes. They use the constructor algorithms only to prepare inputs without
accidentally preparing a role whose CodeRequest is under test. Explicit helper
body replacements and forged cache/cycle models are protocol/storage tests,
not authentic source admission or native execution oracles.
