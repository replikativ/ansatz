# Matched default Init evidence producer

Native research evidence for Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. This profile parses an empty ordinary
legacy source header with the original parser. Its two implicit requests are
ordinary Init and meta Init; private import loading selects 631 modules and
3,155 genuine ModuleData parts. It does not finalize an Environment, run extension
callbacks or initializers, replay imported proofs, open a store, or start a JVM.

From this worktree root:

```sh
python3 experiments/lean-ir/paired-init/census.py target/init-census
python3 experiments/lean-ir/paired-init/build.py \
  experiments/lean-ir/target/matched-prelude-producer-structural-v4 target/init-build
python3 experiments/lean-ir/paired-init/run.py \
  target/init-build target/init-census/census.json target/init-pair
python3 experiments/lean-ir/paired-init/audit.py target/init-pair
(cd experiments/lean-ir/paired-init && python3 -m unittest test_audit.py)
```

The build reuses authenticated unchanged structural `Export` and `Projection`
units from the accepted Prelude build; it verifies their sources and compiled
bytes against that build's cohort. The exporter uses `ExprStructEq` for both
expression caches, preserving binder names and binder information. Only upstream
MData erasure and `let.nonDep=false` normalization remain.

Selection copies pinned `Environment.subsumesInfo` and the original module-order
merge. It retains all 66,124 CI occurrences, their exact source module/part/index,
65,994 winning declarations, and independent first-import attribution. The 130
observed repetitions are theorem/theorem entries: later subsuming entries win
without requiring identical proof bodies. Every occurrence's full checking shape
is exported, including losing theorem bodies. The producer validates dependency,
family, name-order, display-collision and quotient closure before graph export.

The transport streams its 11.23 million nodes without retaining native snapshots
or constructing a second cloned graph. `nativeRoundtripVerified` is therefore
false. The separate audit verifies complete records, reference/immediate counts,
source occurrence inventories, winner shapes, dependencies and families. It uses
sqlite for declaration shapes and dense expression-index flags, rather than
retaining the entire kernel DAG as Python objects. These are evidence gates, not
a guest admission certificate.

Typed scalar claims follow actual Name, Literal, IR, LCNF, simp and Verso source
fields. Dynamic doc elements are inspected only through original `Dynamic.get?`
for named genuine types. `Std.Format.nest` is an **Int**: native payload
`4294967294` means `-2`, while `Std.Format.tag` contains a Nat. Consumers must bind
claims to the transport digest and exact node/field/payload and preserve the Int
versus Nat distinction. The audit rejects any uncovered large immediate; a
physical constructor shape is never sufficient evidence of its scalar domain.

Each part records ordered `regularInitAttr`/`builtinInitAttr` declaration and
initializer names via the original `ParametricAttribute Name` entry type. This
observes requirements, not native initialization status. In this closure,
`Init.Data.Random` carries `IO.stdGenRef` initialization, which obtains entropy.
Pinned `runInitAttrForMod` first probes native module initialization, then consults
`interpretedModInits`, and only then performs ordered interpreted fallback.
A runtime seed that already captured stdGenRef cannot simply skip every module
or rerun it without a faithful per-module initialization protocol. Guest
finalization and this protocol remain separate prerequisites for activation.

Commands enforce one native process group, 2 GiB RSS, 2 GiB MemAvailable and
finite CPU/wall/output limits. The first complete export took 117 seconds and
1.58 GiB RSS; its transport was 1.86 GB, kernel 370 MB, correspondence 35 MB.
Allow disk space for a temporary transport spool and final file simultaneously.
No standalone boot or full Init guest import is claimed here.
