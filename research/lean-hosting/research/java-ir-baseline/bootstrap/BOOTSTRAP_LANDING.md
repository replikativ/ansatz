# Clean bootstrap landing

This package is based on merged source-module main
`ab9339effa347dbda1502fc72e5d863e8c98ad8d`. It adds the reviewed bootstrap package, exact policy metadata,
explicit bounded pack assembler and the two supporting runtime-cohort hooks.
The existing artifact frontend's historical, arithmetic, general-command and
source-module layers and canonical validation files are unchanged.

The optional companion-importer hook preflights the caller-pinned selected
capture and delegates to the existing production importer. The optional child
observer receives the actual local child before module/setup effects, letting
the bootstrap privately retain the real engine for disposal/closed checks.
Omitting either hook preserves the existing cohort behavior; no source or
checking capability is created by the callbacks themselves.

The parent actual smoke used profile
`3e1850867319b5220354a5ba307d1c3a303433070e4dfe5e41568dd96c22852b`
with 504 selected artifacts and all 47 tracked definitions in one fresh
512 MiB JVM. The pristine parent had zero guest instructions. Matched Prelude
preparation and a two-definition earlier-reference file reached real EOF;
the linked boxed entry returned 42 for 40. Child retirement disposed/closed
14 extra occurrences and 534 runtime roots; seed retirement disposed/closed
zero extra occurrences and 534 roots. Profile and jar classloader then closed.
No ignored implementation loader, original code warmup or native Lean invocation
was used. `assembly-validation.json` pins the actual report and basis descriptor.

This is bounded explicit Prelude bootstrap acceptance. It is not full Init,
Mathlib, an arbitrary project importer, native tutorial runner or public Java
project-loading API. The large selected pack and CAS remain external,
independently pinned artifacts rather than tracked repository payloads.

Source checks:

- `python3 verify-source.py`
- `python3 verify-policy-data.py --lean-repository PINNED_LEAN_REPOSITORY`
- `python3 policies-data-checks.py`
- `python3 assembly-checks.py`

These checks never start Java, Lean or an interpreter. The ten Clojure metadata
model families and actual fresh-process run are parent evidence, separately
scoped in the existing receipt. Ordinary dependency-basis/runtime provenance
must accompany each new actual invocation.
