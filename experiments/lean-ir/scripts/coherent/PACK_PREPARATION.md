# Coherent pack preparation

`materialize-pack.py` is a host-only pack builder. It reads authenticated data,
streams file hashes and copies or hardlinks immutable inputs. It never executes
Java, Lean, archived host scripts, a constructor, a restore or a campaign stage.
Its output is **REVIEW_REQUIRED**, including the proposed constructor command.
Generated digests are observations for independent review, not launch authority.

Supply a committed final source capture and its observed, coherently compiled
24-source/48-class build. The final runtime dependency basis is Clojure 1.12.0,
core.specs.alpha 0.4.74, spec.alpha 0.5.238 and data.json 2.5.1, in that order.
Javac uses only the Clojure jar. Earlier data.json 2.5.0 test captures stay intact.

The command requires these explicit arguments:

```
python3 scripts/coherent/materialize-pack.py \
  --capture CAPTURE --expected-capture-sha256 SHA \
  --observed-build OBSERVATION --expected-observed-sha256 SHA \
  --source-commit FULL_COMMIT --jdk JDK_ROOT \
  --inputs INPUT_SPEC --expected-inputs-sha256 SHA --output NEW_ABSOLUTE_PACK
```

The bounded JSON input specification has exactly these fields:

- `schema`: `coherent-pack-inputs/1`.
- `producer-payload`: `{path, sha256}` for the original constructor payload. Its
  resolver is read as inert JSON; its exact original recipe is read as bounded
  EDN data. None of its embedded old host controller source is executed.
- `producer-store`: `{root, index-sha256}` for the original immutable CAS store.
- `helpers`: the exact nine roles `graph`, `export`, `import`, `old-import`,
  `visibility`, `ordinary-publication`, `ordinary-encoding`, `eio-builders`, and
  `cases-on`. Each has `source` and `ir` file pins `{path, sha256}`. The tool checks
  actual typed entrypoint names. Import helpers must retain exactly their known
  pure helper-value action; other helpers must have no initialization actions.
- `old-import-provenance`: `export-driver` and `export-receipt` file pins for the
  historical 56-row export. The old 43-row helper is explicitly an unchanged
  subprogram of this source-backed export. The builder checks the manifest and
  all 42 unique declaration raw lines byte for byte, in the original order, and
  reconstructs the old artifact digest. It does not claim to recover the old
  standalone source. Both original provenance files and the new selection proof
  are direct pack inputs; the historical driver is never executed.
- `fixtures`: exact file pins for the eight reviewed coherent Lean fixture files.
- `bootstrap`: the separately reviewed bootstrap source file pin.
- `build-evidence`: `receipt` and `postcheck` file pins linking the actual passed,
  disposed coherent compiler run and unchanged inputs to the observed classes.
- `provenance`: at most 64 additional parent metadata file pins. These remain
  separate provenance; they are not recursively imported as launch inputs.
- `final-source-approved`: a boolean review marker. Even `true` confers no
  authority: the final contract, manifest, command and source still need
  independent review and finite guarded execution.

All pin paths are explicit absolute regular files, paired with expected SHA256.
The output pack preserves checkpoint manifest/data sibling relationships and
native Source descriptor/source/index sibling relationships. Large immutable
files can share inodes with their originals; treat pack inputs as read-only.
No archive is rewritten and no ancestor campaign capture is recursively copied.

Only the original declaration index may resolve outside the pack, through one
explicit `producer-declarations` external-store descriptor. Its canonical root,
`indexes/<SHA>.json` relative path and digest are bound by the externally reviewed
launch manifest. Every use rechecks that exact index. Existing declaration-store
reads independently check each requested blob hash and Name. This authenticates
content; it does not claim a filesystem sandbox for arbitrary external blob
symlinks. No generic external input or classpath fallback exists.

Bootstrap rejects existing output/provider paths and symbolic-link ancestors
before any project namespace loads. Its classpath is exactly the four declared
jars followed by the selected source and fresh class directories. Constructor
policy is fixed to mutable, RAW invocation fuel 500,000,000 and compile threshold 1.
The independent per-declaration Java imported checker limit is 20,000,000,
preserving the established baseline rather than conflating the two fuel ledgers. The pack
builder emits only the `construct!` entrypoint, never `run!`.

Run the small host-only metadata/path regressions with:

```
python3 scripts/coherent/test-materialize-pack.py
```

These tests establish data and path handling, not actual bootstrap, constructor,
restore, callback, checking, guest or frontend acceptance. Those remain separate
reviewed execution gates.

## Finite hosted-file/JVM application composition

The historical `/1` contracts and four-jar launch basis above remain unchanged.
`coherent-pack-inputs/2` selects a separate finite experiment, with two additional
file pins:

- `dependency-lock`: a `coherent-maven-basis/1` JSON lock with exact roots
  Clojure 1.12.4, data.json 2.5.1 and Pattern 1.0.452. Its thirteen ordered rows
  contain `lib`, `version`, `id`, `path`, `sha256`, `pom-path`, `pom-sha256`.
  Every path is a physical absolute regular file. The resolver disables root,
  user and project configuration. Resolution provenance is recorded separately;
  hashes authenticate artifact bytes, not a remote repository's identity.
- `application-policy`: bounded inert EDN matching the new controller's closed
  `:application` policy. It names finite A/B file inputs, original module and
  callable Names, expected results, callback ABI and selection limits. The first
  corpus row contains the callback. `fixtures` contains exactly the referenced
  distinct A/B files, each at most 16 KiB. These initial scalar fixtures exercise
  the combined loading/compiler path; broader real-program coverage is a
  separate corpus, not inferred from these fixtures.

Pass `--dependency-lock LOCK --expected-dependency-lock-sha256 SHA` to
`plan-java-build.py` as well as every `--dependency PATH=SHA` in the lock's order.
The plan and observed build use `/2` schemas and carry the exact lock digest.
The pack builder checks that linkage and every ordered jar identity/hash. It
rejects project providers in dependency jars, including multi-release entries;
Pattern's own authenticated AOT classes are permitted. The core and optional
Ansatz jars must not be appended to this source/fresh-Java cohort.

The resulting contract is `ansatz-coherent-jvm-application-contract/1`, profile
`ansatz-producer50f-coherent-jvm-application-consumer/1`, and launch manifest is
`ansatz-coherent-launch/2`. The bootstrap requires that exact schema pairing.
The frontend retains the mutable/500M/threshold1 policy; application execution
uses a distinct JVM/500M/threshold1 branch. The controller reopens and adopts it
through public APIs under the independently retained original configuration.
Compiler selection conveys no checking authority.

The finite stages replace the historical Project campaign with Init prefix,
real A load/selection/calls/callback, real B load/selection, A/B/A calls and
managed disposal. Bootstrap acceptance checks the exact seventeen stages,
contract/profile/implementation identity, both execution roles, callback effect
counts and ordered phase summaries. It does not promote a successful constructor
or a data-model test into a successful hosted run. Preparation substage timing
may share one measured span; overlapping spans must not be added.
For this new profile, a failed controller prints only its exception class and a
bounded message before nonzero process exit. Exception data may contain entire
Worlds or owner checkpoints and is never serialized by this telemetry path.
Process termination does not prove managed disposal.

`test-bootstrap-result.clj` reads the reviewed bootstrap, evaluates only its
definitions in a scratch namespace, and tests terminal result validation. It
never evaluates the launch form. Run it in the existing small REPL after the
host-only Python tests; it is not a fresh Source/Init restore or actual bootstrap
acceptance. A genuine launch still needs the final committed cohort, fresh Java
classes, original pinned producer inputs, independent composition review and
resource preflight.

## Explicit artifact admission for the Init base

The `/2` input specification optionally accepts exactly:

```json
"kernel-base-admission": {
  "basis": "trusted-artifact",
  "profile": "full-init-lean-4.33.1-producer50f"
}
```

Omitting this field retains fresh strict Init checking. It is supported only by
the finite JVM application profile. It is authenticated contract data, rather
than a runtime flag or a caller-supplied digest. The builder selects the explicit
`admit-restored!` and `prepare-admitted!` controller entrypoints. Admission uses
the actual restored finalizer map and its already-open Store; it neither
reopens Source nor replays initialization or the finalizer.

The fixed profile pins the completed checkpoint and producer/Store cohort;
the current runtime source, classes, helpers and binding identities remain
independently authenticated. See [the full Init profile](../../research/FULL_INIT_ARTIFACT_PROFILE.md).
The admitted base carries an opaque token and artifact provenance, never a fresh
strict certificate. New checked declarations retain that base assumption.

The resident admitted prefix currently supports preparation, release and
retirement. Legacy prefix import/reconstruction/graph entrypoints reject it;
the application campaign uses `resident/load-source` directly. Bounded model
tests establish this wiring, not acceptance of the full Init image. A new
committed source/class cohort and genuine guarded campaign run are required
before claiming the artifact-mode provider works end to end.
