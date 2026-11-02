#!/usr/bin/env python3
"""Producer test: build an application JAR, then run the public JVM-only API."""
import argparse
import json
import os
from pathlib import Path
import zipfile

from sdk_audit import DEPENDENCIES, audit_jar, digest, require, run_stage


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdk-jar", type=Path, required=True)
    parser.add_argument("--dependency-jar", type=Path, action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--java", default="java")
    parser.add_argument("--javac", default="javac")
    parser.add_argument("--main-class", default="ProjectSmoke", choices=["ProjectSmoke", "GeneralInteropSmoke", "ScalarInteropSmoke", "JarSmoke"])
    args = parser.parse_args()
    consumer = Path(__file__).resolve().parent
    sdk = args.sdk_jar.resolve()
    audit = audit_jar(sdk)
    jars = [sdk, *(path.resolve() for path in args.dependency_jar)]
    require(len(jars) == len(set(jars)) == 5 and all(p.is_file() for p in jars), "SDK plus four unique runtime jars required")
    require({p.name for p in jars[1:]} == DEPENDENCIES, "Resolved runtime dependency closure differs")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    classes = output / "classes"
    empty = output / "empty-cwd"
    require(not empty.exists() or not any(empty.iterdir()), "Empty consumer working directory required")
    classes.mkdir(exist_ok=True)
    empty.mkdir(exist_ok=True)
    classpath = os.pathsep.join(map(str, jars))
    stages = [run_stage([args.javac, "-J-Xmx192m", "--release", "17", "-cp", classpath,
                                   "-d", str(classes), str(consumer / (args.main_class + ".java"))], empty, output / "javac", 60)]
    require(stages[0]["exit"] == 0, "Java consumer compilation failed")
    app = output / "interop-consumer.jar"
    with zipfile.ZipFile(app, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for root in [classes, consumer / "resources"]:
            for path in sorted(root.rglob("*")):
                if path.is_file(): archive.write(path, str(path.relative_to(root)))
    stages.append(run_stage([args.java, "-Xmx384m", "-cp", os.pathsep.join([str(app), classpath]),
                                       args.main_class], empty, output / "java", 120))
    report = {"jarAudit": audit, "stages": stages, "applicationJARSHA256": digest(app.read_bytes()),
              "sourceCheckoutOnClasspath": False, "runtimeNativeCompiler": False, "runtimeJavaCompilation": False}
    (output / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    require(stages[-1]["exit"] == 0, "Application-JAR consumer failed")
    print("PASS public API application-JAR consumer; see", output / "result.json")


if __name__ == "__main__":
    main()
