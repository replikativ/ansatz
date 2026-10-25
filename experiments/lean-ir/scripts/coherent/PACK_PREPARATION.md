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
policy is fixed to mutable, fuel 500,000,000 and compile threshold 1. The pack
builder emits only the `construct!` entrypoint, never `run!`.

Run the small host-only metadata/path regressions with:

```
python3 scripts/coherent/test-materialize-pack.py
```

These tests establish data and path handling, not actual bootstrap, constructor,
restore, callback, checking, guest or frontend acceptance. Those remain separate
reviewed execution gates.
