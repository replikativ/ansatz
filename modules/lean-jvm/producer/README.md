# Explicit native producer bundle

Precompiled artifact execution needs only the optional SDK and its ordinary
Maven dependencies. Trusted source compilation additionally needs an explicit
official Lean installation, writable compiler cache, Linux `prlimit`, and an
independently supplied native producer bundle. Compilation can execute native
metaprograms and compile-time IO. It is not a sandbox.

The initial bundle profile is Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, target
`x86_64-unknown-linux-gnu`, 64-bit words. Its data-only
`producer-bundle.json` follows [the example](producer-bundle.example.json).
Each of the three helpers includes its original Lean source. The SDK pins the
six hashes independently and validates bounded regular files, path containment,
source bytes and executable bytes. A supplied hash or claimed version alone
cannot authorize another helper. Stripping or rebuilding a binary changes its
identity and requires a separately reviewed producer cohort.

The bundle is outside the runtime JAR. No helper binary, Lean sysroot, source
checkout, Python or Clojure CLI is a runtime dependency of precompiled artifact
loading. The source service invokes these three native helpers itself; Java
callers do not run a separate exporter command. The retired fixed tutorial
exporter is not required by the canonical source service.

Bundle hosting, installation, compressed distribution and automatic discovery
are unresolved. The example is an explicit installation contract, not a download
or an installation claim. The current reviewed helper binaries contain debug
information and are large; they must not become mandatory Maven dependencies.
