#!/usr/bin/env python3
"""Audit a built jar, optionally run its Java-only consumer. No dependency resolver.

The script is producer/test tooling and is not packaged in the runtime jar.
Dependencies are already-resolved jar files; no Clojure CLI/source roots are used.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import xml.etree.ElementTree as ET
import zipfile

POM = "META-INF/maven/org.replikativ/ansatz-lean-jvm/pom.xml"
ADAPTER = "ansatz/lean/jvm/ir.clj"
METADATA = "META-INF/ansatz-lean-jvm/runtime.edn"
SOURCES = {"ansatz/lean/jvm/" + name + ".clj" for name in
           ["ir", "artifact", "original", "capabilities", "startup", "publisher", "project",
            "compiler/encoding", "compiler/transport", "compiler/local", "compiler/evidence", "compiler/bundle"]}
SDK_RESOURCES = {METADATA, "META-INF/ansatz-lean-jvm/user-error.json", "META-INF/ansatz-lean-jvm/NOTICE"}
API_CLASSES = {"Bridge", "Lean", "LeanException", "LeanProject", "MainResult", "NativeCompilerOptions", "ProjectOptions"}
DEPENDENCIES = {"clojure-1.12.0.jar", "spec.alpha-0.5.238.jar", "core.specs.alpha-0.4.74.jar", "data.json-2.5.1.jar"}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def audit_jar(path, expected_engine_sha=None):
    path = Path(path)
    require(path.is_file() and path.stat().st_size <= 64 * 1024 * 1024, "Bounded SDK jar required")
    with zipfile.ZipFile(path) as archive:
        entries = archive.infolist()
        names = [entry.filename for entry in entries]
        require(len(names) <= 4096 and len(names) == len(set(names)), "Duplicate or excessive jar entries")
        require(sum(entry.file_size for entry in entries) <= 32 * 1024 * 1024, "Jar expansion exceeds bound")
        require(all(not name.startswith("/") and ".." not in name.split("/") for name in names), "Unsafe jar path")
        resources = sorted(name for name in names if name.endswith((".clj", ".cljc")))
        require(set(resources) == SOURCES, "Research/legacy or missing runtime namespace resource")
        require(POM in names and METADATA in names, "Missing POM/runtime metadata")
        classes = sorted(name for name in names if name.endswith(".class"))
        allowed_resources = SOURCES | SDK_RESOURCES | {POM, "META-INF/MANIFEST.MF",
                             "META-INF/maven/org.replikativ/ansatz-lean-jvm/pom.properties"}
        require(all(name.endswith("/") or name in allowed_resources or name in classes for name in names),
                "Uninventoried runtime file or research source in jar")
        require(classes and all(re.fullmatch(r"ansatz/research/ir/Interpreter(?:\$[^/]+)?\.class", name)
                               or (re.fullmatch(r"ansatz/lean/jvm/([A-Za-z]+)(?:\$[^/]+)?\.class", name)
                                   and re.fullmatch(r"ansatz/lean/jvm/([A-Za-z]+)(?:\$[^/]+)?\.class", name).group(1) in API_CLASSES)
                               for name in classes),
                "Unexpected or duplicate engine implementation classes")
        for api_class in API_CLASSES:
            require("ansatz/lean/jvm/" + api_class + ".class" in classes, "Missing Java facade class " + api_class)
        for nested in ["", "$Program", "$Node", "$Header", "$SourceBinding", "$HostExtern"]:
            require("ansatz/research/ir/Interpreter" + nested + ".class" in classes, "Missing engine class " + nested)
        for name in classes:
            data = archive.read(name)
            require(data[:4] == b"\xca\xfe\xba\xbe" and int.from_bytes(data[6:8], "big") == 61,
                    "Engine class is not Java release 17")
        pom = ET.fromstring(archive.read(POM))
        ns = {"m": "http://maven.apache.org/POM/4.0.0"}
        dependencies = [(item.findtext("m:groupId", namespaces=ns), item.findtext("m:artifactId", namespaces=ns),
                         item.findtext("m:version", namespaces=ns))
                        for item in pom.findall("m:dependencies/m:dependency", ns)]
        require(len(dependencies) == 2 and set(dependencies) == {("org.clojure", "clojure", "1.12.0"), ("org.clojure", "data.json", "2.5.1")}, "POM runtime dependencies differ")
        require(pom.findtext("m:groupId", namespaces=ns) == "org.replikativ"
                and pom.findtext("m:artifactId", namespaces=ns) == "ansatz-lean-jvm", "SDK coordinate differs")
        metadata = archive.read(METADATA)
        for key, value in [(b"precompiled-engine", b"true"), (b"runtime-java-compilation", b"false"),
                           (b"native-compiler-included", b"false")]:
            require(re.search(rb":" + key + rb"\s+" + value + rb"(?:[,\s}]|$)", metadata) is not None,
                    "Unsupported runtime metadata promise")
        public_match = re.search(rb":public-project-api\s+(true|false)(?:[,\s}]|$)", metadata)
        require(public_match is not None, "Missing public API acceptance flag")
        require(set(SDK_RESOURCES).issubset(names), "Missing SDK codec or attribution resource")
        require(digest(archive.read("META-INF/ansatz-lean-jvm/user-error.json")) ==
                "53b224c8fa037b144260872e3b14878aff86dbb61b598e1ea49f991dabc1fb6b", "Codec source pin differs")
        match = re.search(rb':engine-source-sha256\s+"([0-9a-f]{64})"', metadata)
        require(match is not None, "Missing engine source pin")
        engine_sha = match.group(1).decode("ascii")
        require(expected_engine_sha is None or engine_sha == expected_engine_sha, "Jar engine source pin differs")
        return {"jarBytes": path.stat().st_size, "jarSHA256": digest(path.read_bytes()),
                "entryCount": len(names), "engineClassCount": sum(name.startswith("ansatz/research/ir/") for name in classes),
                "javaAPIClassCount": sum(name.startswith("ansatz/lean/jvm/") for name in classes),
                "publicProjectAPIAccepted": public_match.group(1) == b"true", "javaRelease": 17,
                "engineSourceSHA256": engine_sha, "runtimeResources": resources,
                "pomDependencies": [list(item) for item in dependencies],
                "adapterSHA256": digest(archive.read(ADAPTER)), "metadataSHA256": digest(metadata),
                "pomSHA256": digest(archive.read(POM))}


def run_stage(command, cwd, prefix, timeout):
    with prefix.with_suffix(".stdout").open("wb") as stdout, prefix.with_suffix(".stderr").open("wb") as stderr:
        result = subprocess.run(command, cwd=cwd, stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr,
                                timeout=timeout, check=False)
    return {"stage": prefix.name, "exit": result.returncode,
            "stdoutSHA256": digest(prefix.with_suffix(".stdout").read_bytes()),
            "stderrSHA256": digest(prefix.with_suffix(".stderr").read_bytes())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdk-jar", type=Path, required=True)
    parser.add_argument("--dependency-jar", type=Path, action="append", default=[])
    parser.add_argument("--expected-engine-source-sha256")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit-only", action="store_true")
    parser.add_argument("--javac", default="javac")
    parser.add_argument("--java", default="java")
    args = parser.parse_args()
    report = {"jarAudit": audit_jar(args.sdk_jar, args.expected_engine_source_sha256), "publicProjectAPI": False}
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if not args.audit_only:
        jars = [args.sdk_jar.resolve(), *(path.resolve() for path in args.dependency_jar)]
        require(len(jars) == len(set(jars)) == 5 and all(path.is_file() and path.suffix == ".jar" for path in jars),
                "Exactly five unique SDK/runtime dependency jars required")
        require({path.name for path in jars[1:]} == DEPENDENCIES, "Unexpected resolved dependency closure")
        source = Path(__file__).resolve().with_name("JarSmoke.java")
        classes = output / "classes"
        empty = output / "empty-cwd"
        require(not empty.exists() or not any(empty.iterdir()), "Consumer working directory must be empty")
        empty.mkdir(exist_ok=True)
        classes.mkdir(exist_ok=True)
        classpath = os.pathsep.join(str(path) for path in jars)
        steps = [run_stage([args.javac, "-J-Xmx192m", "--release", "17", "-cp", classpath,
                            "-d", str(classes), str(source)], empty, output / "javac", 60)]
        if steps[0]["exit"] == 0:
            steps.append(run_stage([args.java, "-Xmx192m", "-cp", os.pathsep.join([str(classes), classpath]),
                                    "JarSmoke"], empty, output / "java", 60))
        report.update(steps=steps, classpathJarCount=4, sourceCheckoutOnConsumerClasspath=False,
                      resolvedJarNames=[path.name for path in jars])
    (output / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    require(args.audit_only or (len(report["steps"]) == 2 and all(step["exit"] == 0 for step in report["steps"])),
            "Consumer failed; inspect stage logs and result.json")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
