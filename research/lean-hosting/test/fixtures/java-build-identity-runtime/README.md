# Original build identity rows

Four authentic Lean 4.33.1 declarations: Lean.getGithash,
System.Platform.getTarget and their original boxed wrappers. Optional top-level
pretty text is removed; original record hashes remain distinct from the derived
fixture hash. Each wrapper's complete static FAP dependency is its extern root.

`provenance.edn` pins the accepted producer payload and checkpoint manifest.
`source-receipt.json` records bounded source extraction and a matching installed
native binary's version/hash outputs. That binary corroborates the accepted
profile strings; it is not asserted to be the executable that made the checkpoint.
Selecting the Java profile is an explicit trusted-host assertion, not proof of
manifest acceptance or of the JVM host's native build identity.

Upstream copyright Microsoft Corporation and contributors, Apache 2.0:
[license](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE),
[platform.cpp](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/platform.cpp),
[lean.h](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/include/lean/lean.h).
