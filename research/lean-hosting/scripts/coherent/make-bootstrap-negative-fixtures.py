#!/usr/bin/env python3
"""Create bounded JAR scan fixtures, without Java/JVM/compiler execution.

Each actual fresh-process negative needs a NEW reviewed derivative launch manifest
including the changed jar digest; otherwise it tests only digest mismatch. The
placeholder class is deliberately never loaded: pre-project scans must reject it.
"""
import argparse
import json
from pathlib import Path
import zipfile


def jar(path, entries):
    with zipfile.ZipFile(path, "x") as output:
        for name, content in entries.items():
            output.writestr(name, content)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    jar(args.output / "manifest-linked.jar", {
        "META-INF/MANIFEST.MF": "Manifest-Version: 1.0\r\nClass-Path: extra-provider.jar\r\n\r\n"})
    jar(args.output / "extra-provider.jar", {
        "prototype/unlisted.clj": '(ns prototype.unlisted) (throw (Exception. "must never execute"))'})
    jar(args.output / "multi-release-project.jar", {
        "META-INF/MANIFEST.MF": "Manifest-Version: 1.0\r\nMulti-Release: true\r\n\r\n",
        "META-INF/versions/17/prototype/unlisted.clj": '(ns prototype.unlisted)',
        "META-INF/versions/17/ansatz/kernel/Unlisted.class": b"SCAN-REJECT-BEFORE-CLASS-LOAD"})
    (args.output / "cases.json").write_text(json.dumps({
        "status": "FIXTURES_ONLY_NOT_EXECUTED",
        "cases": ["reverse two declared dependency entries while keeping actual JVM order",
                  "manifest-linked.jar declared, extra-provider.jar implicit ONLY",
                  "multi-release-project.jar declared with its genuine captured digest",
                  "extra-root .clj __init shadow", "extra-root .cljc __init shadow",
                  "jar .clj __init shadow", "jar .cljc __init shadow"],
        "required-verdict": "reject before any ansatz/prototype project namespace loads"
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
