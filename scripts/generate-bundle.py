#!/usr/bin/env python3
"""Build a pinned six-artifact candidate in staging; never install it.

Example: python3 scripts/generate-bundle.py --exporter-source ../lean4export
  --lean-root /path/to/lean/toolchain --output target/bundle-candidate
The exporter is rebuilt from a captured tracked source tree inside staging.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

LEAN_VERSION = "4.33.1"
LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
EXPORTER_COMMIT = "15f6055e299ad5b89345e533cc2192f4cc00f659"
ROOT_FILES = {"init": "scripts/bundle-init-roots.txt",
              "lex": "scripts/bundle-lex-roots.txt",
              "sizeof": "scripts/bundle-sizeof-roots.txt"}
RESOURCES = {"init": "init-medium.ndjson.gz", "lex": "lex-prelude.ndjson.gz",
             "sizeof": "sizeof-prelude.ndjson.gz", "attrs": "init-attrs.ndjson.gz",
             "matchers": "init-matchers.ndjson.gz", "instances": "init-instances.tsv.gz"}
DUMPERS = {role: f"scripts/dump_{role}.lean" for role in ("attrs", "matchers", "instances")}


def digest(payload):
    return hashlib.sha256(payload).hexdigest()


def run(args, *, cwd, env, output=None):
    preview = " ".join(map(str, args[:5]))
    if len(args) > 5:
        preview += f" ... ({len(args)} arguments)"
    print("Running:", preview, flush=True)
    if output is None:
        subprocess.run(list(map(str, args)), cwd=cwd, env=env, check=True)
    else:
        with output.open("wb") as stream:
            subprocess.run(list(map(str, args)), cwd=cwd, env=env, stdout=stream, check=True)


def read_roots(payload):
    rows = [line.strip() for line in payload.decode("utf-8").splitlines()
            if line.strip() and not line.lstrip().startswith("#")]
    if any(row.startswith("_private.") for row in rows):
        raise ValueError("Requested roots must be public; private names are reached through dependencies")
    if not rows or len(rows) != len(set(rows)):
        raise ValueError("Root lists must be nonempty and contain no duplicates")
    return rows


def validate_root_migration(captured, roots):
    receipt = json.loads(captured["scripts/bundle-root-migrations.json"])
    base = captured["scripts/init-store-roots.txt"]
    rows = [line.strip() for line in base.decode("utf-8").splitlines()
            if line.strip() and not line.lstrip().startswith("#")]
    if receipt.get("profile") != "ansatz-bundle-root-migration/1" or receipt.get("to-lean") != LEAN_VERSION:
        raise ValueError("Wrong root migration profile/target")
    if receipt.get("base") != {"path": "scripts/init-store-roots.txt", "sha256": digest(base), "count": len(rows)}:
        raise ValueError("Root migration baseline differs")
    public = [name for name in rows if not name.startswith("_private.")]
    if len(rows) - len(public) != receipt["private-requested-roots-removed"]:
        raise ValueError("Private root migration count differs")
    if digest(("\n".join(public) + "\n").encode()) != receipt["legacy-public-roots-sha256"]:
        raise ValueError("Legacy public root inventory differs")
    changes = {row["from"]: row for row in receipt["changes"]}
    if len(changes) != len(receipt["changes"]) or not set(changes).issubset(public):
        raise ValueError("Ambiguous or absent root migration source")
    for row in changes.values():
        if row["action"] not in ("rename", "retire") or (row["action"] == "retire" and row["to"] not in public):
            raise ValueError("Invalid root migration action/retirement coverage")
    migrated = [changes.get(name, {}).get("to", name) for name in public
                if changes.get(name, {}).get("action") != "retire"]
    expected = migrated + receipt.get("added-roots", [])
    if len(set(expected)) != len(expected) or sorted(expected) != sorted(roots["init"]):
        raise ValueError("Tracked Init roots differ from the explicit migration")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter-source", type=Path, required=True)
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    options = parser.parse_args()
    project = Path(__file__).resolve().parent.parent
    output = options.output.resolve()
    for protected in [project / p for p in ("resources", "test-data", "src", "src-java", "scripts")]:
        if output == protected or protected in output.parents or output in protected.parents:
            raise ValueError("Generation output must be a separate staging directory")
    if output.exists() and any(output.iterdir()):
        raise ValueError("Generation requires an empty or nonexistent staging directory")
    source = options.exporter_source.resolve()
    lean_root = options.lean_root.resolve()
    env = dict(os.environ, LEAN_SYSROOT=str(lean_root), LEAN_PATH=str(lean_root / "lib/lean"),
               PATH=str(lean_root / "bin") + os.pathsep + os.environ.get("PATH", ""))
    lean = lean_root / "bin/lean"
    githash = subprocess.check_output([str(lean), "--githash"], env=env, text=True).strip()
    if githash != LEAN_COMMIT:
        raise ValueError(f"Wrong Lean producer: expected {LEAN_COMMIT}, found {githash}")
    commit = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
    if commit != EXPORTER_COMMIT:
        raise ValueError(f"Wrong exporter source commit: {commit}")
    toolchain = (source / "lean-toolchain").read_text().strip()
    if toolchain != f"leanprover/lean4:v{LEAN_VERSION}":
        raise ValueError(f"Wrong exporter toolchain: {toolchain}")
    output.mkdir(parents=True, exist_ok=True)
    inputs = output / "inputs"
    inputs.mkdir()
    input_rows = []
    captured = {}
    source_inputs = [str(p.relative_to(project)) for folder, suffix in [("src", ".clj"), ("src-java", ".java")]
                     for p in sorted((project / folder).rglob("*" + suffix))]
    for relative in [*ROOT_FILES.values(), "scripts/init-store-roots.txt", "scripts/bundle-root-migrations.json",
                     "scripts/lean4export-structural-exprs.patch", *DUMPERS.values(), "scripts/generate-bundle.py",
                     "scripts/validate-bundle.clj", "scripts/validate_bundle_roots.lean",
                     "scripts/export_bundle_equations.lean", "deps.edn", *source_inputs]:
        payload = (project / relative).read_bytes()
        destination = inputs / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(payload)
        captured[relative] = payload
        input_rows.append({"path": relative, "sha256": digest(payload)})
    roots = {role: read_roots(captured[path]) for role, path in ROOT_FILES.items()}
    validate_root_migration(captured, roots)
    run([lean, "--run", inputs / "scripts/validate_bundle_roots.lean",
         *[inputs / path for path in ROOT_FILES.values()]], cwd=output, env=env,
        output=output / "root-validation.json")
    # Run the second phase from the captured project, not live source/classes.
    classpath = subprocess.check_output(["clojure", "-J-Xmx256m", "-Srepro", "-Spath"],
                                       cwd=inputs, env=env, text=True).strip()
    jars = [Path(path) for path in classpath.split(os.pathsep) if path.endswith(".jar")]
    dependencies = [{"artifact": path.name, "sha256": digest(path.read_bytes())} for path in jars]
    versions = {tool: subprocess.run([tool, "-Xmx256m" if tool == "java" else "-J-Xmx256m", "-version"],
                                     env=env, text=True, check=True,
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout.strip()
                for tool in ("java", "javac")}
    build_record = json.dumps({"dependencies": sorted(dependencies, key=lambda row: (row["artifact"], row["sha256"])),
                               "versions": versions}, sort_keys=True, indent=2).encode()
    (inputs / "checker-build.json").write_bytes(build_record)
    input_rows.append({"path": "checker-build.json", "sha256": digest(build_record)})
    classes = inputs / "classes"
    classes.mkdir()
    run(["javac", "-J-Xmx1g", "-source", "11", "-target", "11", "-cp", classpath, "-d", classes,
         *[inputs / path for path in source_inputs if path.endswith(".java")]], cwd=inputs, env=env)
    for path in sorted(classes.rglob("*.class")):
        input_rows.append({"path": str(path.relative_to(inputs)), "sha256": digest(path.read_bytes())})
    producer = output / "producer"
    producer.mkdir()
    tracked = subprocess.check_output(["git", "-C", str(source), "ls-files", "-z"]).split(b"\0")
    source_rows = []
    for raw in sorted(p for p in tracked if p):
        relative = raw.decode("utf-8")
        origin = source / relative
        if origin.is_symlink() or not origin.is_file():
            raise ValueError(f"Unsupported exporter source entry: {relative}")
        payload = origin.read_bytes()
        destination = producer / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(payload)
        source_rows.append({"path": relative, "sha256": digest(payload)})
    (output / "exporter-base-source-inventory.json").write_text(json.dumps(source_rows, indent=2) + "\n")
    # The upstream Expr cache uses alpha equivalence, which can discard binder
    # annotations depending on traversal order. Preserve structural fields in
    # this explicitly patched, captured producer; never modify the source checkout.
    run(["patch", "--batch", "--fuzz=0", "--forward", "--no-backup-if-mismatch", "-p1", "-i",
         inputs / "scripts/lean4export-structural-exprs.patch"], cwd=producer, env=env)
    # Compile the captured equation-aware entry point against the pinned exporter.
    # Its name inventory is derived from roots, never maintained by hand.
    (producer / "Main.lean").write_bytes(captured["scripts/export_bundle_equations.lean"])
    source_rows = [{"path": row["path"], "sha256": digest((producer / row["path"]).read_bytes())}
                   for row in source_rows]
    source_hash = digest(json.dumps(source_rows, sort_keys=True, separators=(",", ":")).encode())
    (output / "exporter-source-inventory.json").write_text(json.dumps(source_rows, indent=2) + "\n")
    run([lean_root / "bin/lake", "--no-cache", "build"], cwd=producer, env=env)
    binary = producer / ".lake/build/bin/lean4export"
    recipe = {"profile": "ansatz-bundle-generator/1",
              "lean": {"version": LEAN_VERSION, "githash": LEAN_COMMIT},
              "exporter": {"commit": commit, "binary-sha256": digest(binary.read_bytes()),
                           "source-sha256": source_hash, "toolchain": toolchain},
              "inputs": sorted(input_rows, key=lambda r: r["path"]), "roots": roots,
              "metadata-profile": "ansatz-global-companions/1"}
    (output / "generation.json").write_text(json.dumps(recipe, indent=2, ensure_ascii=False) + "\n")
    raw = output / "raw"
    raw.mkdir()
    for role in ("init", "lex", "sizeof"):
        destination = raw / f"{role}.ndjson"
        run([binary, *roots[role]], cwd=output, env=env, output=destination)
        with destination.open(encoding="utf-8") as stream:
            header = json.loads(next(stream))
        if header.get("meta", {}).get("lean") != recipe["lean"]:
            raise ValueError(f"Exporter binary produced a different Lean header for {role}")
    for role, relative in DUMPERS.items():
        run([lean, "--run", inputs / relative, "Init"], cwd=output, env=env,
            output=raw / (f"{role}.tsv" if role == "instances" else f"{role}.ndjson"))
    # Clojure performs strict CI replay, exact overlap and companion selection,
    # then writes deterministic gzip resources and the manifest LAST.
    run(["clojure", "-J-Xmx512m", "-J-Xss16m", "-Srepro", "-M", inputs / "scripts/validate-bundle.clj", output],
        cwd=inputs, env=env)
    print(f"Validated candidate: {output / 'resources/ansatz/bundle.edn'}")
    print("No shipped resources or development fixtures were replaced.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Bundle generation failed: {error}", file=sys.stderr)
        sys.exit(1)
