# Original checked-disabled profiling fixture

`original-rows.json` contains 43 authentic accepted-CAS records with exact typed
Names and raw original SHA256 identities. Only top-level `pretty` is removed.
The bounded closure contains profileit/boxed wrapper, the actual private
get_profiler/boxed getter and its Options specialization, plus original
Options/Name construction helpers. The single initialized sentinel is
`Lean.profiler`; its initializer body is not replayed or expanded.

`captured-profiler-option.json` retains the actual two persistent source nodes:
the Option Bool record and its cached Name `profiler`, with default false. It
includes the original ready-global frame, original heap frames, frame hashes,
checkpoint/source-index pins and source offsets from the separately checked
45-global companion extraction. This is a bounded captured-state fixture, not
a map claiming production admission. No fallback option/default was fabricated.

`provenance.json` pins all fixture bytes and upstream Lean source/license at
commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` (4.33.1), from accepted index
`74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`.
Upstream rows/source are Apache 2.0, copyright Microsoft Corporation, Sebastian
Ullrich and Lean contributors. The pinned LICENSE digest is recorded.

The original profileit extern owns its callback and declaration and borrows
category/Options. Its original boxed wrapper supplies an owning facade. The
original boxed getter owns one Options argument and returns a tagged Bool. The
source pure fallback has no separate authenticated fdecl in this catalogue.
See [the runtime profile](../../../research/JAVA_PROFILE_RUNTIME.md).
