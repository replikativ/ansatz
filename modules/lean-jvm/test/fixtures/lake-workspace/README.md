# Authored Lake workspace fixture

`app` is a Lake package requiring the separate local `domain` package. Its
original build includes a domain record, a theorem, a noinline reference function
and an ordinary initializer. The application calls into the dependency and
returns its record through the typed boundary. `app/Oracle.lean` is the independent
native execution reference.

The optional `test/lake_acceptance.clj` runner copies these sources to a fresh
owned cache directory, explicitly builds them with the configured toolchain,
and exercises public source/artifact preparation, dependency changes, refusals
and host bindings. It never modifies a user's workspace. Default SDK checks use
an already prepared artifact and require no Lake or native Lean installation.
