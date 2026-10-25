#!/usr/bin/env python3
"""Prepare a REVIEW_REQUIRED coherent pack; never execute project/native code.

All source paths and expected hashes are explicit. Candidate hashes printed here
are observations for independent review, never self-issued launch authority.
Large immutable files may be hardlinked; no existing inputs are changed. The
original CAS store is explicit and index-authenticated; blobs stay hash-checked
on demand by declaration_store rather than copied or admitted by this tool.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys

SHA = re.compile(r"[0-9a-f]{64}\Z")
ID = re.compile(r"[A-Za-z0-9_./$-]{1,512}\Z")
COMMIT = re.compile(r"[0-9a-f]{40}\Z")
PRODUCER = "50f0b30693b1d696dd60790a0bb09aeeeba58baf2b2fdabe13e17f0103bf2849"
RECIPE = "9a1d53dce65909c15330ee4fa7289804e727927b30f504ed010680a0c1971e70"
LEAN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
ORIGINAL = "d7a54765268331ebe9afdfa4695a7702b8d53c95cd1a8c51da8ef41d1468e43d"
STAGES = "fresh-init graph-helpers panic ordinary-helpers typed-eio cases-on seal helper-value project typed-io ordinary-module chain diamond reload".split()
HELPER_COMPONENTS = {
    "graph": [("SourceModuleGraphImport", "assembleClassicGraphOverInit")],
    "export": [("SourceModuleExport", "exportClassic", "_boxed")],
    "import": [("SourceModuleImport", n) for n in ["mkOwnedPart", "assembleClassic", "finalizeClassic", "finalizerHeader", "appendClassicOverInit"]]
              + [("SourceModuleImport", "finalizeClassic", "_boxed_const_1")],
    "old-import": [("SourceModuleImport", n) for n in ["mkOwnedPart", "assembleClassic", "finalizeClassic", "finalizerHeader"]]
                  + [("SourceModuleImport", "finalizeClassic", "_boxed_const_1")],
    "visibility": [("SourceReconstructionWitness", "isExporting"), ("SourceReconstructionWitness", "isExporting", "_boxed")],
    "ordinary-publication": [("KernelSourceInductivePublication", "postCheckGeneratedFamily")],
    "ordinary-encoding": [("KernelEncoding", "decodeFamily", "_boxed"), ("KernelEncoding", "decodeNames", "_boxed")],
    "eio-builders": [("EIOResultBuilders", "success"), ("EIOResultBuilders", "failure")],
    "cases-on": [("KernelCasesOnRaw", "construct")],
}
# Dotted labels are contract presentation only, never typed Name identity.
HELPERS = {role: [".".join(parts) for parts in roots] for role, roots in HELPER_COMPONENTS.items()}

CONTROLLERS = {
    "prototype/coherent_source_preparation.clj": ["prototype.coherent-source-preparation/" + n for n in ["prepare-bootstrap-support", "check-restored!", "prepare!", "validate-approved-composition!", "assert-initialization-preserved!", "validate-prefix-native-bindings!"]],
    "prototype/coherent_campaign.clj": ["prototype.coherent-campaign/construct!", "prototype.coherent-campaign/run!"],
    "prototype/coherent_helper_value.clj": ["prototype.coherent-helper-value/initialize!"],
    "prototype/coherent_execution.clj": ["prototype.coherent-execution/run!"],
    "prototype/coherent_typed_eio.clj": ["prototype.coherent-typed-eio/" + n for n in ["prepare-prefix!", "assert-no-compilation-effects!", "invoke!", "dispose-call-failure!", "close-contexts!"]],
}


class Reject(ValueError):
    pass


def check(ok, label):
    if not ok:
        raise Reject(label)


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def relative(value):
    check(isinstance(value, str) and ID.fullmatch(value) and not value.startswith("/")
          and all(p not in ("", ".", "..") for p in value.split("/")), "invalid relative identity")
    return value


def file_pin(row, maximum=None):
    check(isinstance(row, dict) and set(row) == {"path", "sha256"}, "file pin schema")
    check(isinstance(row["sha256"], str) and SHA.fullmatch(row["sha256"]), "file pin digest shape")
    p = Path(row["path"])
    check(p.is_absolute() and p.is_file() and not p.is_symlink(), "explicit regular file required")
    check(maximum is None or p.stat().st_size <= maximum, "bounded metadata file too large")
    check(digest(p) == row["sha256"], "file digest mismatch")
    return p.resolve(strict=True)


def read_json(path, maximum=4 * 1024 * 1024):
    check(path.stat().st_size <= maximum, "JSON metadata bound")
    def unique(pairs):
        out = {}
        for key, value in pairs:
            check(key not in out, "duplicate JSON key")
            out[key] = value
        return out
    return json.loads(path.read_text(), object_pairs_hook=unique)


class Keyword(str):
    pass


class Tagged:
    def __init__(self, name, value):
        self.name, self.value = name, value


def key(name):
    return Keyword(name)


class EDN:
    """Finite inert data reader for producer manifest/recipe; never eval/read tags."""
    def __init__(self, text):
        check(len(text.encode()) <= 4 * 1024 * 1024, "EDN byte bound")
        self.text, self.pos, self.work = text, 0, 0

    def space(self):
        while self.pos < len(self.text):
            c = self.text[self.pos]
            if c.isspace() or c == ",":
                self.pos += 1
            elif c == ";":
                n = self.text.find("\n", self.pos)
                self.pos = len(self.text) if n < 0 else n + 1
            else:
                break

    def value(self, depth=0):
        self.space()
        self.work += 1
        check(depth <= 128 and self.work <= 100000, "EDN depth/work bound")
        check(self.pos < len(self.text), "EDN unexpected EOF")
        c = self.text[self.pos]
        if c == '"':
            result, end = json.JSONDecoder().raw_decode(self.text[self.pos:])
            check(isinstance(result, str), "EDN string")
            self.pos += end
            return result
        if c in "{[":
            self.pos += 1
            close = "}" if c == "{" else "]"
            values = []
            while True:
                self.space()
                check(self.pos < len(self.text), "EDN unclosed container")
                if self.text[self.pos] == close:
                    self.pos += 1
                    break
                values.append(self.value(depth + 1))
            if c == "[":
                return values
            check(len(values) % 2 == 0, "EDN map arity")
            result = {}
            for i in range(0, len(values), 2):
                check(isinstance(values[i], (str, int)) and values[i] not in result, "EDN map key/duplicate")
                result[values[i]] = values[i + 1]
            return result
        match = re.match(r"[^\s,\[\]{}\";]+", self.text[self.pos:])
        check(match is not None, "EDN token")
        token = match.group(0)
        self.pos += len(token)
        if token.startswith(":") and re.fullmatch(r":[A-Za-z0-9_./?!*+<>=$-]+", token):
            return Keyword(token[1:])
        if token in ("nil", "true", "false"):
            return {"nil": None, "true": True, "false": False}[token]
        if re.fullmatch(r"-?[0-9]{1,20}", token):
            return int(token)
        if re.fullmatch(r"#[A-Za-z][A-Za-z0-9_.-]+", token):
            # Only preserve opaque data tags; no callback, reader or code invoked.
            check(token == "#prototype.machine.Ref", "unsupported producer EDN tag")
            return Tagged(token[1:], self.value(depth + 1))
        raise Reject("unsupported EDN token")

    def read(self):
        result = self.value()
        self.space()
        check(self.pos == len(self.text), "multiple EDN forms")
        return result


def edn(value):
    if isinstance(value, Keyword):
        return ":" + value
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=False)
    if value is None:
        return "nil"
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, list):
        return "[" + " ".join(map(edn, value)) + "]"
    if isinstance(value, dict):
        return "{" + " ".join(edn(k) + " " + edn(v) for k, v in value.items()) + "}"
    raise Reject("unsupported output EDN value")


def kws(value):
    """Metadata maps have keyword keys; string values stay strings."""
    if isinstance(value, dict):
        return {key(k): kws(v) for k, v in value.items()}
    if isinstance(value, list):
        return [kws(v) for v in value]
    return value


def name_key(value):
    parts = []
    for _ in range(128):
        check(isinstance(value, list), "helper typed Name")
        if value == ["anonymous"]:
            result = ("anonymous",)
            for kind, payload in reversed(parts):
                result = (kind, result, payload)
            return result
        check(len(value) == 3 and value[0] in ("str", "num"), "helper typed Name constructor")
        if value[0] == "str":
            check(isinstance(value[2], str) and len(value[2]) <= 512, "helper Name string segment")
            parts.append(("str", value[2]))
        else:
            check(not isinstance(value[2], bool) and isinstance(value[2], (str, int))
                  and re.fullmatch(r"0|[1-9][0-9]{0,511}", str(value[2])), "helper Name canonical numeric segment")
            parts.append(("num", int(value[2])))
        value = value[1]
    raise Reject("helper Name depth")


def public_name_key(parts):
    result = ("anonymous",)
    for component in parts:
        result = ("str", result, component)
    return result


def expected_name(label):
    # Lookup only fixed, explicitly segmented constants; never split a display
    # string to decode an arbitrary structured Lean Name.
    found = [public_name_key(parts) for roots in HELPER_COMPONENTS.values()
             for parts in roots if ".".join(parts) == label]
    check(len(found) == 1 or (found and all(n == found[0] for n in found)), "unknown fixed helper label")
    return found[0]


def helper_roots(path, role):
    check(path.stat().st_size <= 8 * 1024 * 1024, "helper artifact bound")
    roots, actions = set(), None
    with path.open() as stream:
        for n, line in enumerate(stream):
            check(n < 10000 and len(line.encode()) <= 2 * 1024 * 1024, "helper row count/byte bound")
            row = json.loads(line)
            if n == 0:
                actions = row.get("initializationPlan", {}).get("actions")
            elif "name" in row:
                roots.add(name_key(row["name"]))
    if role in ("import", "old-import"):
        constant = ["str", ["str", ["str", ["anonymous"], "SourceModuleImport"], "finalizeClassic"], "_boxed_const_1"]
        check(actions == [{"action": {"kind": "value", "name": constant, "target": constant}, "meta": False}],
              "exact known pure helper-value action required")
    else:
        check(actions == [], "helper initializer actions frontier")
    return roots


class Pack:
    def __init__(self, root):
        check(root.is_absolute(), "absolute output required")
        for ancestor in [root] + list(root.parents):
            check(not ancestor.is_symlink(), "output symlink ancestor")
        check(not root.exists(), "output must be new")
        root.mkdir(parents=True)
        self.root, self.inputs, self.total = root, {}, 0

    def add(self, identity, source, expected, destination=None):
        identity = relative(identity)
        destination = relative(destination or "inputs/" + identity)
        check(identity not in self.inputs, "duplicate direct input ID")
        source = file_pin({"path": str(source), "sha256": expected})
        target = self.root / destination
        check(not target.exists(), "duplicate destination path")
        target.parent.mkdir(parents=True, exist_ok=True)
        self.total += source.stat().st_size
        check(self.total <= 8 * 1024 ** 3 and len(self.inputs) < 10000, "pack size/input bound")
        try:
            os.link(source, target)
        except OSError:
            shutil.copyfile(source, target)
        check(digest(target) == expected, "captured direct input drift")
        self.inputs[identity] = {"id": identity, "path": destination, "sha256": expected}
        return target

    def write(self, identity, data, destination=None):
        temp = self.root / ".generated-input"
        check(not temp.exists(), "generated input collision")
        temp.write_bytes(data)
        try:
            return self.add(identity, temp, digest(temp), destination)
        finally:
            temp.unlink()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--capture", type=Path, required=True)
    p.add_argument("--expected-capture-sha256", required=True)
    p.add_argument("--observed-build", type=Path, required=True)
    p.add_argument("--expected-observed-sha256", required=True)
    p.add_argument("--source-commit", required=True)
    p.add_argument("--jdk", type=Path, required=True)
    p.add_argument("--inputs", type=Path, required=True)
    p.add_argument("--expected-inputs-sha256", required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    check(COMMIT.fullmatch(args.source_commit), "full source commit required")
    check(args.output.is_absolute(), "explicit absolute output required")
    capture_path = file_pin({"path": str(args.capture.resolve() / "source-capture.json"), "sha256": args.expected_capture_sha256})
    observed_path = file_pin({"path": str(args.observed_build.resolve()), "sha256": args.expected_observed_sha256})
    spec_path = file_pin({"path": str(args.inputs.resolve()), "sha256": args.expected_inputs_sha256}, 4 * 1024 * 1024)
    capture, observed, spec = map(read_json, [capture_path, observed_path, spec_path])
    check(capture["commit"] == observed["commit"] == args.source_commit, "source/build commit mismatch")
    check(observed["capture-sha256"] == args.expected_capture_sha256, "observed build capture mismatch")
    check(spec["schema"] == "coherent-pack-inputs/1", "pack input schema")
    check(set(spec) == {"schema", "producer-payload", "producer-store", "helpers", "fixtures", "bootstrap", "provenance", "final-source-approved", "build-evidence", "old-import-provenance"}, "input specification keys")
    # This flag records the reviewer's intended source revision, not authority.
    check(isinstance(spec["final-source-approved"], bool), "source review marker")
    inv = observed["inventory"]
    check(len(inv) <= 1000 and len({r["id"] for r in inv}) == len(inv), "inventory size/duplicates")
    domain = "ansatz-restored-runtime-consumer/1\n" + "".join(r["id"] + "\t" + r["kind"] + "\t" + r["sha256"] + "\n" for r in sorted(inv, key=lambda r: r["id"]))
    check(hashlib.sha256(domain.encode()).hexdigest() == observed["implementation-sha256"], "inventory domain digest")
    check(len(observed["class-output-provenance"]) == 48, "expected complete 24-source/48-class cohort")
    pack = Pack(args.output)
    for row in inv:
        relative(row["id"])
        base = args.capture.resolve() / ("classes" if row["kind"] in ("kernel-class", "runtime-class") else "selected")
        dest = ("classes/" if row["kind"] in ("kernel-class", "runtime-class") else "selected/") + row["id"]
        source = file_pin({"path": str(base / row["id"]), "sha256": row["sha256"]})
        target = pack.root / dest
        target.parent.mkdir(parents=True, exist_ok=True)
        os.link(source, target) if source.stat().st_dev == pack.root.stat().st_dev else shutil.copyfile(source, target)
    for resource in CONTROLLERS:
        check(any(r["id"] == resource and r["kind"] == "host-source" for r in inv), "required controller absent")
    dependencies = []
    dependency_names = ["clojure-1.12.0.jar", "core.specs.alpha-0.4.74.jar", "spec.alpha-0.5.238.jar", "data.json-2.5.1.jar"]
    by_dependency = {Path(row["path"]).name: row for row in observed["dependencies"]}
    check(len(observed["dependencies"]) == 4 and set(by_dependency) == set(dependency_names), "explicit final current four-jar basis required")
    for dependency_name in dependency_names:
        row = by_dependency[dependency_name]
        target = pack.add("dependency/" + Path(row["path"]).name, args.capture.resolve() / row["path"], row["sha256"], row["path"])
        dependencies.append({"id": row["id"], "path": str(target.relative_to(pack.root)), "sha256": row["sha256"]})
    check(len(dependencies) == 4 and len({r["id"] for r in dependencies}) == 4, "four ordered dependency jars required")
    evidence = spec["build-evidence"]
    check(set(evidence) == {"receipt", "postcheck"}, "build evidence schema")
    compile_receipt = file_pin(evidence["receipt"], 1024 * 1024)
    compile_postcheck = file_pin(evidence["postcheck"], 1024 * 1024)
    cr, cp = read_json(compile_receipt), read_json(compile_postcheck)
    check(cr["status"] == "passed" and cr["exitCode"] == 0
          and observed["compile-receipt-sha256"] == digest(compile_receipt)
          and cp["receiptSha256"] == digest(compile_receipt) and cp["disposed"] is True
          and cp["allPinsMatch"] is True, "actual disposed coherent build evidence required")
    for identity, source in [("cohort/source-capture", capture_path),
                             ("cohort/observed-build", observed_path),
                             ("cohort/build-plan", args.capture.resolve() / "java-build-plan/plan.json"),
                             ("cohort/compile-receipt", compile_receipt),
                             ("cohort/compile-postcheck", compile_postcheck)]:
        if identity == "cohort/build-plan":
            check(digest(source) == observed["build-plan-sha256"], "actual observed build plan linkage")
        pack.add(identity, source, digest(source))
    payload_path = file_pin(spec["producer-payload"], 4 * 1024 * 1024)
    payload = read_json(payload_path)
    original = payload["constructor-input"]
    recipe_text = original["recipe-source"]
    check(hashlib.sha256(recipe_text.encode()).hexdigest() == RECIPE, "original producer recipe hash")
    recipe = EDN(recipe_text).read()
    resolver = json.loads(original["resolver-source"])
    check(len(resolver) <= 1000, "producer resolver bound")
    pack.write("producer/recipe", recipe_text.encode())
    for artifact, descriptor in recipe[key("artifacts")].items():
        identity = str(artifact)
        check(identity in resolver, "producer artifact missing explicit resolver")
        pack.add("producer/" + identity, Path(resolver[identity]), descriptor[key("sha256")])
    for row in recipe[key("build-inventory")]:
        identity = row[key("id")]
        check(identity in resolver, "original producer build input missing")
        pack.add("producer/" + identity, Path(resolver[identity]), row[key("sha256")])
    checkpoint = Path(original["manifest-path"])
    file_pin({"path": str(checkpoint), "sha256": original["manifest-sha256"]}, 4 * 1024 * 1024)
    manifest = EDN(checkpoint.read_text()).read()
    preparation = manifest[key("preparation")]
    check(preparation[key("implementation-sha256")] == PRODUCER and preparation[key("catalogue-recipe")] == recipe, "original producer preparation/recipe mismatch")
    pack.write("producer/preparation", (edn(preparation) + "\n").encode())
    pack.add("checkpoint/manifest", checkpoint, original["manifest-sha256"], "checkpoint/manifest.frames")
    data = manifest[key("data")]
    relative(data[key("file")])
    check("/" not in data[key("file")], "checkpoint data must be sibling basename")
    pack.add("checkpoint/data", checkpoint.parent / data[key("file")], data[key("sha256")], "checkpoint/" + data[key("file")])
    transport = read_json(Path(resolver["transport-descriptor"]), 8 * 1024 * 1024)
    for resource in manifest[key("resources")]:
        rid = resource[key("id")]
        check(resource[key("descriptor-sha256")] == digest(Path(resolver["transport-descriptor"])), "resource descriptor disagreement")
        descriptor = Path(resolver["transport-descriptor"])
        check(all("/" not in relative(transport[k]) for k in ["sourceFile", "indexFile"]), "native Source sidecars must be sibling basenames")
        source = descriptor.parent / transport["sourceFile"]
        index = descriptor.parent / transport["indexFile"]
        relative(source.name); relative(index.name)
        folder = "resources/" + relative(rid) + "/"
        pack.add("resource/" + rid + "/descriptor", descriptor, resource[key("descriptor-sha256")], folder + descriptor.name)
        pack.add("resource/" + rid + "/source", source, resource[key("source-sha256")], folder + source.name)
        pack.add("resource/" + rid + "/index", index, resource[key("index-sha256")], folder + index.name)
    store = spec["producer-store"]
    check(set(store) == {"root", "index-sha256"}, "explicit CAS store descriptor")
    check(store["index-sha256"] == recipe[key("declaration-index")], "CAS index recipe mismatch")
    store_root = Path(store["root"])
    check(store_root.is_absolute(), "absolute explicit CAS root required")
    for ancestor in [store_root] + list(store_root.parents):
        check(not ancestor.is_symlink(), "CAS root symlink ancestor")
    check(store_root == store_root.resolve(strict=True), "canonical captured CAS root required")
    check((store_root / "declarations").is_dir(), "CAS declarations root missing")
    index = file_pin({"path": str(store_root / "indexes" / (store["index-sha256"] + ".json")), "sha256": store["index-sha256"]})
    # Only the exact producer index may resolve outside the pack. Existing blob
    # reads verify SHA and Name; no generic external-file resolver is generated.
    external = {"schema": "coherent-external-cas-proposal/1", "id": "producer/declaration-index", "root": str(store_root), "index-relative-path": "indexes/" + index.name, "index-sha256": store["index-sha256"], "blob-policy": "Existing declaration_store verifies each requested declarations/<SHA>.json and exact Name; no index-only checkedness claim."}
    pack.write("external-cas-proposal", (json.dumps(external, indent=2) + "\n").encode())
    helper_specs = spec["helpers"]
    check(set(helper_specs) == set(HELPERS), "complete exact helper role set required")
    helpers = []
    for role, entries in HELPERS.items():
        item = helper_specs[role]
        check(set(item) == {"source", "ir"}, "helper input fields")
        source = file_pin(item["source"], 8 * 1024 * 1024)
        ir = file_pin(item["ir"], 8 * 1024 * 1024)
        check({expected_name(entry) for entry in entries} <= helper_roots(ir, role), "helper actual IR entrypoints missing")
        source_id, ir_id = "helpers/" + role + "/source.lean", "helpers/" + role + "/ir.jsonl"
        pack.add(source_id, source, item["source"]["sha256"])
        pack.add(ir_id, ir, item["ir"]["sha256"])
        helpers.append({"id": role, "source-id": source_id, "source-sha256": item["source"]["sha256"], "ir-id": ir_id, "ir-sha256": item["ir"]["sha256"], "entrypoints": entries})
    old_spec, full_spec = helper_specs["old-import"], helper_specs["import"]
    check(old_spec["source"]["sha256"] == full_spec["source"]["sha256"], "old/import unchanged-subprogram source disagreement")
    old_lines = file_pin(old_spec["ir"]).read_bytes().splitlines(keepends=True)
    full_lines = file_pin(full_spec["ir"]).read_bytes().splitlines(keepends=True)
    check(len(old_lines) == 43 and len(full_lines) == 56 and old_lines[0] == full_lines[0], "old/import exact manifest/row-count disagreement")
    by_name = {}
    for line in full_lines[1:]:
        n = json.dumps(json.loads(line)["name"], separators=(",", ":"))
        check(n not in by_name, "duplicate full import declaration")
        by_name[n] = line
    selected = [full_lines[0]]
    selected_names = set()
    for line in old_lines[1:]:
        n = json.dumps(json.loads(line)["name"], separators=(",", ":"))
        check(n not in selected_names and by_name.get(n) == line, "old import declaration duplicate/byte drift")
        selected_names.add(n)
        selected.append(by_name[n])
    check(len(selected_names) == 42, "exact42 unique old import declarations required")
    check(hashlib.sha256(b"".join(selected)).hexdigest() == old_spec["ir"]["sha256"], "old import exact selection digest mismatch")
    selection = {"schema": "coherent-old-import-subprogram-selection/1", "relation": "Old43 artifact is an unchanged selected subprogram of the source-backed56 export, not a full export of the current source or recovered original old source.", "source-sha256": full_spec["source"]["sha256"], "full-ir-sha256": full_spec["ir"]["sha256"], "selected-ir-sha256": old_spec["ir"]["sha256"], "manifest-byte-identical": True, "selected-declarations": 42, "all-selected-lines-byte-identical": True}
    legacy_proof = spec["old-import-provenance"]
    check(set(legacy_proof) == {"export-driver", "export-receipt"}, "old import native provenance schema")
    for role, row in legacy_proof.items():
        f = file_pin(row, 4 * 1024 * 1024)
        pack.add("provenance/old-import/" + role, f, row["sha256"])
    historical = read_json(file_pin(legacy_proof["export-receipt"]))
    check(historical["status"] == "passed" and historical["rows"] == 56
          and historical["old-rows-identical"] == 43
          and historical["source-sha256"] == full_spec["source"]["sha256"]
          and historical["sha256"] == full_spec["ir"]["sha256"], "historic native export provenance disagreement")
    selection["historic-export-driver-sha256"] = legacy_proof["export-driver"]["sha256"]
    selection["historic-export-receipt-sha256"] = legacy_proof["export-receipt"]["sha256"]
    pack.write("helpers/old-import/selection-proof", (json.dumps(selection, indent=2) + "\n").encode())
    fixture_names = {"CoherentA.lean", "CoherentA-reload.lean", "CoherentB.lean", "CoherentC.lean", "CoherentD.lean", "CoherentE.lean", "CoherentOrdinary.lean", "ProjectAppEIO.lean"}
    check(set(spec["fixtures"]) == fixture_names, "exact fixture set required")
    for name, row in spec["fixtures"].items():
        pack.add("fixtures/" + name, file_pin(row, 65536), row["sha256"])
    original_path = store_root / "declarations" / (ORIGINAL + ".json")
    pack.add("cas/" + ORIGINAL, original_path, ORIGINAL)
    bootstrap = file_pin(spec["bootstrap"], 1024 * 1024)
    pack.add("bootstrap", bootstrap, spec["bootstrap"]["sha256"], "bootstrap.clj")
    contract = kws({"schema": "ansatz-coherent-frontend-contract/1", "profile": "ansatz-producer50f-coherent-frontend-consumer/1", "producer": {"implementation-sha256": PRODUCER, "recipe-sha256": RECIPE}, "lean-commit": LEAN, "target": {"triple": "x86_64-unknown-linux-gnu", "word-bits": 64}, "inventory": inv, "implementation-sha256": observed["implementation-sha256"], "composition": {"controllers": [{"id": k, "entrypoints": v} for k, v in CONTROLLERS.items()], "helpers": helpers, "redirects": [{"symbol": "lean_mk_cases_on", "target": ["str", ["str", ["anonymous"], "KernelCasesOnRaw"], "construct"], "row-sha256": ORIGINAL}], "stages": [Keyword(x) for x in STAGES]}, "kernel-policy": {"allow-axioms?": True, "allow-unsafe?": True, "allow-compiler-markers?": True}, "limits": {"max-helper-bytes": 8 * 1024 * 1024, "max-helper-declarations": 10000, "checker-fuel": 500000000}})
    for row in contract[key("inventory")]:
        row[key("kind")] = Keyword(row[key("kind")])
    contract_path = pack.root / "contract.edn"
    contract_path.write_text(edn(contract) + "\n")
    jdk = {k: v for k, v in observed["jdk"].items() if k != "javac-sha256"}
    jdk_root = args.jdk.resolve(strict=True)
    for field, path in [("java-sha256", "bin/java"), ("release-sha256", "release"),
                        ("libjvm-sha256", "lib/server/libjvm.so"), ("modules-sha256", "lib/modules")]:
        check(digest(jdk_root / path) == jdk[field], "actual JDK path differs from observed build")
    launch = kws({"schema": "ansatz-coherent-launch/1", "commit": args.source_commit, "source-root": "selected", "class-root": "classes", "dependencies": dependencies, "inventory": inv, "direct-inputs": list(pack.inputs.values()), "external-stores": [{"role": Keyword("producer-declarations"), "root": str(store_root), "index-relative": "indexes/" + index.name, "index-sha256": store["index-sha256"]}], "contract-id": "contract.edn", "contract-sha256": digest(contract_path), "jdk": jdk, "entrypoint": "prototype.coherent-campaign/construct!", "execution": {"backend": Keyword("mutable"), "fuel": 500000000, "compile-threshold": 1}})
    for row in launch[key("inventory")]:
        row[key("kind")] = Keyword(row[key("kind")])
    (pack.root / "launch.edn").write_text(edn(launch) + "\n")
    proposed_command = [str(jdk_root / "bin/java"), "-Xmx384m", "-Xss8m", "--enable-native-access=ALL-UNNAMED", "-cp",
                        os.pathsep.join([str(pack.root / row["path"]) for row in dependencies] + [str(pack.root / "selected"), str(pack.root / "classes")]),
                        "clojure.main", str(pack.root / "bootstrap.clj"), str(pack.root), "launch.edn",
                        digest(pack.root / "launch.edn"), digest(contract_path)]
    (pack.root / "constructor-command-proposal.json").write_text(json.dumps({"status": "REVIEW_REQUIRED_NO_EXECUTION_AUTHORITY", "command": proposed_command, "note": "An independently reviewed guard must bind its own accepted external digests, resource caps, environment and these closed roots before executing. This tool never launches the command."}, indent=2) + "\n")
    provenance = []
    check(isinstance(spec["provenance"], list) and len(spec["provenance"]) <= 64, "parent provenance bound")
    for row in spec["provenance"]:
        f = file_pin(row, 4 * 1024 * 1024)
        provenance.append({"path": str(f), "sha256": row["sha256"]})
    review = {"schema": "coherent-candidate-pack-review/1", "status": "REVIEW_REQUIRED_NOT_EXECUTABLE", "source-commit": args.source_commit, "final-source-review-marker": spec["final-source-approved"], "capture-sha256": args.expected_capture_sha256, "observed-build-sha256": args.expected_observed_sha256, "input-spec-sha256": args.expected_inputs_sha256, "contract-sha256": digest(contract_path), "launch-sha256": digest(pack.root / "launch.edn"), "inventory-members": len(inv), "direct-inputs": len(pack.inputs), "captured-bytes": pack.total, "external-cas-proposal": external, "provenance-only-not-launch-inputs": provenance, "remaining-blocker": "Independent exact source/contract/launch review, bootstrap negative tests and actual constructor required. No run! manifest emitted; final approved V3 cohort required. Candidate digests do not confer authority."}
    (pack.root / "review-required.json").write_text(json.dumps(review, indent=2) + "\n")
    print(json.dumps({"status": review["status"], "contract-sha256": review["contract-sha256"], "launch-sha256": review["launch-sha256"], "members": len(inv), "direct-inputs": len(pack.inputs)}))


if __name__ == "__main__":
    try:
        main()
    except Exception as failure:
        # No arbitrary exception payload, input text, parser-state or rich dump.
        print(json.dumps({"status": "REJECTED", "class": type(failure).__name__, "reason": str(failure)[:256] if isinstance(failure, Reject) else "bounded preparation failure"}), file=sys.stderr)
        sys.exit(2)
