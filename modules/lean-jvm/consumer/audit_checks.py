#!/usr/bin/env python3
"""Static positive/negative jar inventory tests. Never starts javac or java."""
import argparse
import hashlib
import json
from pathlib import Path
import tempfile
import warnings
import zipfile

from sdk_audit import audit_jar


def changed_inventory(originals, change):
    """Model a candidate that updates its own manifest consistently after tampering."""
    files = dict(originals)
    inventory_path = "META-INF/ansatz-lean-jvm/java-classes.json"
    metadata_path = "META-INF/ansatz-lean-jvm/runtime.edn"
    inventory = json.loads(files[inventory_path])
    old_closure = inventory["engineClosureSHA256"]
    change(files, inventory)
    text = "".join(source["path"] + "\t" + source["class"] + "\t" + source["sha256"] + "\n"
                   for source in sorted(inventory["sources"], key=lambda source: source["path"])
                   if "/internal/" in source["path"])
    new_closure = hashlib.sha256(text.encode("utf-8")).hexdigest()
    inventory["engineClosureSHA256"] = new_closure
    files[inventory_path] = json.dumps(inventory).encode("utf-8")
    files[metadata_path] = files[metadata_path].replace(old_closure.encode(), new_closure.encode())
    return list(files.items())


CLOJURE_INVENTORY = "META-INF/ansatz-lean-jvm/clojure-classes.json"


def changed_clojure_inventory(originals, change):
    """Model a candidate that tampers with AOT output and re-pins its own Clojure inventory."""
    files = dict(originals)
    inventory = json.loads(files[CLOJURE_INVENTORY])
    change(files, inventory)
    files[CLOJURE_INVENTORY] = json.dumps(inventory).encode("utf-8")
    return list(files.items())


def add_aot_class(name, namespace, data):
    def change(files, inventory):
        files[name] = data
        inventory["classes"][name] = {"namespace": namespace, "sha256": hashlib.sha256(data).hexdigest()}
    return change


def add_self_inventoried_helper(files, inventory):
    name = "ansatz/lean/jvm/internal/exec/HiddenBits.class"
    # Same-length class rename preserves a valid compiled class structure;
    # the candidate claims a source hash without changing the reviewed manifest.
    files[name] = files["ansatz/lean/jvm/internal/exec/ScalarBits.class"].replace(b"ScalarBits", b"HiddenBits")
    inventory["sources"].append({"path": name[:-6] + ".java", "class": name[:-6].replace("/", "."), "sha256": "0" * 64})
    inventory["classes"][name] = hashlib.sha256(files[name]).hexdigest()


def relabel_primary_source(files, inventory):
    for source in inventory["sources"]:
        if source["class"] == "ansatz.lean.jvm.internal.exec.Interpreter":
            source["sha256"] = "1" * 64


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdk-jar", type=Path, required=True)
    args = parser.parse_args()
    baseline = audit_jar(args.sdk_jar)
    with zipfile.ZipFile(args.sdk_jar) as archive:
        originals = [(entry.filename, archive.read(entry)) for entry in archive.infolist()]
    primary_sha = baseline["engineSourceSHA256"]
    cases = {
        "self-inventoried-unreviewed-helper": changed_inventory(originals, add_self_inventoried_helper),
        "self-inventoried-primary-source-relabel": changed_inventory(originals, relabel_primary_source),
        "metadata-primary-source-relabel": [(name, data.replace(primary_sha.encode(), b"0" * 64))
                                             if name == "META-INF/ansatz-lean-jvm/runtime.edn" else (name, data)
                                             for name, data in originals],
        "missing-class-inventory": [(name, data) for name, data in originals if name != "META-INF/ansatz-lean-jvm/java-classes.json"],
        "changed-class-bytes": [(name, data + b"changed") if name == "ansatz/lean/jvm/internal/exec/Interpreter.class" else (name, data) for name, data in originals],
        "missing-adapter": [(name, data) for name, data in originals if name != "ansatz/lean/jvm/ir__init.class"],
        "aot-shadowing-source": originals + [("ansatz/lean/jvm/ir.clj", b"(ns ansatz.lean.jvm.ir)")],
        "changed-aot-class-bytes": [(name, data + b"changed") if name == "ansatz/lean/jvm/project__init.class" else (name, data) for name, data in originals],
        "uninventoried-aot-class": originals + [("ansatz/lean/jvm/ir$hidden.class", dict(originals)["ansatz/lean/jvm/ir__init.class"])],
        "missing-aot-init": changed_clojure_inventory(
            [(name, data) for name, data in originals if name != "ansatz/lean/jvm/startup__init.class"],
            lambda files, inventory: inventory["classes"].pop("ansatz/lean/jvm/startup__init.class")),
        "self-inventoried-dependency-class": changed_clojure_inventory(originals, add_aot_class(
            "clojure/data/json__init.class", "clojure.data.json", dict(originals)["ansatz/lean/jvm/ir__init.class"])),
        "self-inventoried-engine-linking-class": changed_clojure_inventory(originals, add_aot_class(
            "ansatz/lean/jvm/ir$linked.class", "ansatz.lean.jvm.ir",
            dict(originals)["ansatz/lean/jvm/ir__init.class"] + b"ansatz/lean/jvm/internal/exec/Interpreter")),
        "self-inventoried-direct-linking": changed_clojure_inventory(
            originals, lambda files, inventory: inventory.update(directLinking=True)),
        "changed-source-loaded-namespace": [(name, data + b"\n") if name == "ansatz/lean/jvm/compiler/transport.clj" else (name, data) for name, data in originals],
        "legacy-namespace": originals + [("prototype/machine.cljc", b"(ns prototype.machine)")],
        "duplicate-class": originals + [("ansatz/lean/jvm/internal/exec/Interpreter.class", b"duplicate")],
        "extra-java-source": originals + [("research/Interpreter.java", b"class Interpreter {}")],
        "dependency-drift": [(name, data.replace(b"<artifactId>clojure</artifactId>", b"<artifactId>pattern</artifactId>"))
                             if name.endswith("pom.xml") else (name, data) for name, data in originals],
    }
    target = Path(__file__).resolve().parent.parent / "target/consumer-audit-fixtures"
    target.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=target) as directory:
        for label, entries in cases.items():
            candidate = Path(directory) / (label + ".jar")
            with warnings.catch_warnings():
                warnings.simplefilter("ignore", UserWarning)
                with zipfile.ZipFile(candidate, "w") as archive:
                    for name, data in entries:
                        archive.writestr(name, data)
            try:
                audit_jar(candidate)
            except ValueError:
                continue
            raise AssertionError("Jar audit accepted " + label)
    try:
        audit_jar(args.sdk_jar, "0" * 64)
    except ValueError:
        pass
    else:
        raise AssertionError("Jar audit accepted wrong engine source pin")
    print("PASS 1 actual jar audit and " + str(len(cases) + 1) + " static rejection cases; no Java/native processes")


if __name__ == "__main__":
    main()
