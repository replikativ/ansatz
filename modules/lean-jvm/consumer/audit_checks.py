#!/usr/bin/env python3
"""Static positive/negative jar inventory tests. Never starts javac or java."""
import argparse
from pathlib import Path
import runpy
import tempfile
import warnings
import zipfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdk-jar", type=Path, required=True)
    args = parser.parse_args()
    audit = runpy.run_path(str(Path(__file__).with_name("check.py")), run_name="jar_audit")["audit_jar"]
    audit(args.sdk_jar)
    with zipfile.ZipFile(args.sdk_jar) as archive:
        originals = [(entry.filename, archive.read(entry)) for entry in archive.infolist()]
    cases = {
        "missing-adapter": [(name, data) for name, data in originals if name != "ansatz/lean/jvm/ir.clj"],
        "legacy-namespace": originals + [("prototype/machine.cljc", b"(ns prototype.machine)")],
        "duplicate-class": originals + [("ansatz/research/ir/Interpreter.class", b"duplicate")],
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
                audit(candidate)
            except ValueError:
                continue
            raise AssertionError("Jar audit accepted " + label)
    try:
        audit(args.sdk_jar, "0" * 64)
    except ValueError:
        pass
    else:
        raise AssertionError("Jar audit accepted wrong engine source pin")
    print("PASS 1 actual jar audit and 6 static rejection cases; no Java/native processes")


if __name__ == "__main__":
    main()
