#!/usr/bin/env python3
"""Observe actual post-javac classes; never builds/runs Java or accepts a contract.

Run only after the sole lane compiled the exact new empty class root under its
reviewed guard. The compile receipt hash is a provenance link, not an assertion
that this script has verified compiler execution or loaded class identity.
"""
import argparse
import hashlib
import json
from pathlib import Path


def digest(path):
    # Python 3.10 is used by component CI; keep bounded streaming portable.
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        while block := stream.read(1024 * 1024):
            result.update(block)
    return result.hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--capture", type=Path, required=True)
    p.add_argument("--expected-capture-sha256", required=True)
    p.add_argument("--expected-build-plan-sha256", required=True)
    p.add_argument("--compile-receipt", type=Path, required=True)
    p.add_argument("--expected-compile-receipt-sha256", required=True)
    args = p.parse_args()
    root = args.capture.resolve(strict=True)
    capture_path = root / "source-capture.json"
    plan_path = root / "java-build-plan/plan.json"
    for path, expected in [(capture_path, args.expected_capture_sha256),
                           (plan_path, args.expected_build_plan_sha256),
                           (args.compile_receipt, args.expected_compile_receipt_sha256)]:
        if digest(path) != expected:
            raise ValueError("external provenance input digest mismatch")
    capture = json.loads(capture_path.read_text())
    plan = json.loads(plan_path.read_text())
    if capture["commit"] != plan["commit"] or plan["capture-sha256"] != args.expected_capture_sha256:
        raise ValueError("source/build cohort mismatch")
    rows = []
    source_ids = {x["id"] for x in capture["inputs"]}
    for row in capture["inputs"]:
        path = root / "selected" / row["id"]
        if path.is_symlink() or digest(path) != row["sha256"]:
            raise ValueError("captured source changed")
        rows.append({k: row[k] for k in ["id", "kind", "sha256"]})
    outputs = []
    for path in sorted((root / "classes").rglob("*")):
        if path.is_symlink():
            raise ValueError("class tree symlink")
        if not path.is_file():
            continue
        identity = str(path.relative_to(root / "classes"))
        if not identity.endswith(".class") or identity.endswith("__init.class"):
            raise ValueError("unexpected non-Java/AOT class output")
        outer = identity.removesuffix(".class").split("$", 1)[0]
        source = "java/prototype/TypedLongMemo.java" if outer == "prototype/TypedLongMemo" else "src-java/" + outer + ".java"
        if source not in source_ids:
            raise ValueError("class output has no selected source/build provenance: " + identity)
        row = {"id": identity, "kind": "kernel-class" if identity.startswith("ansatz/kernel/") else "runtime-class",
               "sha256": digest(path)}
        rows.append(row)
        outputs.append({**row, "source-id": source, "bytes": path.stat().st_size})
    rows.sort(key=lambda x: x["id"])
    if not outputs or len(rows) > 1000 or len(rows) != len({x["id"] for x in rows}):
        raise ValueError("empty/duplicate/excessive complete member inventory")
    canonical = "ansatz-restored-runtime-consumer/1\n" + "".join(
        f'{row["id"]}\t{row["kind"]}\t{row["sha256"]}\n' for row in rows)
    result = {"schema": "coherent-observed-build/1", "status": "OBSERVED_NOT_ACCEPTED_OR_LOADED",
              "commit": capture["commit"], "implementation-sha256": hashlib.sha256(canonical.encode()).hexdigest(),
              "inventory": rows, "class-output-provenance": outputs, "dependencies": plan["dependencies"],
              "jdk": plan["jdk"], "compile-receipt-sha256": args.expected_compile_receipt_sha256,
              "capture-sha256": args.expected_capture_sha256, "build-plan-sha256": args.expected_build_plan_sha256}
    if plan["schema"] == "coherent-java-build-plan/2":
        result["schema"] = "coherent-observed-build/2"
        result["dependency-lock-sha256"] = plan["dependency-lock-sha256"]
    elif plan["schema"] != "coherent-java-build-plan/1":
        raise ValueError("unsupported build plan schema")
    output = root / "observed-build.json"
    if output.exists():
        raise ValueError("new observation must not overwrite prior evidence")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "members": len(rows), "classes": len(outputs)}))


if __name__ == "__main__":
    main()
