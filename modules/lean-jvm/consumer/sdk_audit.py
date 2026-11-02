#!/usr/bin/env python3
"""Audit a built SDK jar against the reviewed external source closure.

The script is producer/test tooling and is not packaged in the runtime jar.
Dependencies are already-resolved jar files; no Clojure CLI/source roots are used.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import xml.etree.ElementTree as ET
import zipfile

POM = "META-INF/maven/org.replikativ/ansatz-lean-jvm/pom.xml"
ADAPTER = "ansatz/lean/jvm/ir.clj"
METADATA = "META-INF/ansatz-lean-jvm/runtime.edn"
SOURCES = {"ansatz/lean/jvm/" + name + ".clj" for name in
           ["ir", "preparation", "argument", "construction", "producer", "scalar_buffer", "artifact", "original", "capabilities", "startup", "publisher", "project", "signature", "codec", "entry", "value",
            "compiler/encoding", "compiler/transport", "compiler/local", "compiler/evidence", "compiler/bundle"]}
SOURCES.add("ansatz/lean/jvm.clj")
CLASS_INVENTORY = "META-INF/ansatz-lean-jvm/java-classes.json"
SDK_RESOURCES = {CLASS_INVENTORY, METADATA, "META-INF/ansatz-lean-jvm/user-error.json", "META-INF/ansatz-lean-jvm/NOTICE"}
API_CLASSES = {"LeanPreparation", "PreparedArtifact", "Bridge", "Lean", "LeanException", "LeanProject", "LeanFunction", "LeanUnit", "LeanChoice", "IOResult", "MainResult", "NativeCompilerOptions", "ProjectOptions"}
DEPENDENCIES = {"clojure-1.12.0.jar", "spec.alpha-0.5.238.jar", "core.specs.alpha-0.4.74.jar", "data.json-2.5.1.jar"}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def reviewed_engine_sources():
    """Read the one reviewed source manifest, independently of the candidate JAR.

    This deliberately accepts only the manifest's explicit ordered java-engine
    records, not general EDN. A format expansion must update this producer gate
    explicitly; candidate archive metadata never chooses the expectation.
    """
    path = Path(__file__).resolve().parent.parent / "runtime-closure.edn"
    require(path.is_file() and path.stat().st_size <= 128 * 1024, "Bounded reviewed source closure required")
    text = path.read_text(encoding="utf-8")
    require(len(re.findall(r':schema\s+"ansatz-lean-jvm-source-closure/2"', text)) == 1,
            "Unknown reviewed source closure")
    blocks = re.findall(r":java-engine\s*\[([^\[\]]*)\]", text)
    require(len(blocks) == 1, "One explicit reviewed engine source block required")
    record = re.compile(r'\{\s*:path\s+"([^"\\]+)"\s+:class\s+"([^"\\]+)"\s+:sha256\s+"([0-9a-f]{64})"\s*\}')
    sources = []
    block = blocks[0]
    position = 0
    while position < len(block):
        whitespace = re.match(r"[\s,]*", block[position:])
        position += whitespace.end()
        if position == len(block):
            break
        match = record.match(block, position)
        require(match is not None, "Unexpected reviewed engine descriptor syntax")
        source_path, source_class, source_sha = match.groups()
        require(re.fullmatch(r"ansatz/lean/jvm/internal/(?:[a-z]+/)*[A-Z][A-Za-z0-9]*\.java", source_path)
                and source_class == source_path[:-5].replace("/", "."), "Malformed reviewed engine descriptor")
        sources.append({"path": source_path, "class": source_class, "sha256": source_sha})
        position = match.end()
    require(1 <= len(sources) <= 64 and len({s["path"] for s in sources}) == len(sources)
            and len({s["class"] for s in sources}) == len(sources), "Duplicate or excessive reviewed engine sources")
    primary = [source for source in sources if source["class"] == "ansatz.lean.jvm.internal.exec.Interpreter"]
    require(len(primary) == 1, "Reviewed primary engine source required")
    require(re.findall(r':engine-class\s+"([^"\\]+)"', text) == [primary[0]["class"]],
            "Reviewed engine class differs")
    closure_text = "".join(s["path"] + "\t" + s["class"] + "\t" + s["sha256"] + "\n"
                           for s in sorted(sources, key=lambda s: s["path"]))
    closure_sha = digest(closure_text.encode("utf-8"))
    require(re.findall(r':engine-closure-sha256\s+"([0-9a-f]{64})"', text) == [closure_sha],
            "Reviewed engine closure digest differs")
    return sources, closure_sha, primary[0]["sha256"]


def audit_jar(path, expected_engine_sha=None):
    expected_sources, expected_closure_sha, reviewed_primary_sha = reviewed_engine_sources()
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
        require(CLASS_INVENTORY in names, "Missing captured Java class inventory")
        inventory = json.loads(archive.read(CLASS_INVENTORY))
        require(inventory.get("schema") == "ansatz-java-class-inventory/1", "Unknown Java class inventory")
        sources = inventory.get("sources", [])
        require(isinstance(sources, list) and 1 <= len(sources) <= 128, "Bounded Java source inventory required")
        roots = set()
        engine_sources = []
        api_sources = set()
        for source in sources:
            require(set(source) == {"path", "class", "sha256"}, "Unknown Java source descriptor")
            source_path = source["path"]
            require(re.fullmatch(r"ansatz/lean/jvm/(?:internal/(?:[a-z]+/)+)?[A-Z][A-Za-z0-9]*\.java", source_path)
                    and source["class"] == source_path[:-5].replace("/", ".")
                    and re.fullmatch(r"[0-9a-f]{64}", source["sha256"]), "Malformed Java source descriptor")
            require(source_path[:-5] + ".class" not in roots, "Duplicate Java source")
            roots.add(source_path[:-5] + ".class")
            if "/internal/" in source_path: engine_sources.append(source)
            else: api_sources.add(source["class"].rsplit(".", 1)[-1])
        require(api_sources == API_CLASSES, "Java API source inventory differs")
        require(engine_sources == expected_sources, "Java engine sources differ from reviewed external closure")
        closure_text = "".join(s["path"] + "\t" + s["class"] + "\t" + s["sha256"] + "\n"
                               for s in sorted(engine_sources, key=lambda s: s["path"]))
        closure_sha = digest(closure_text.encode("utf-8"))
        require(closure_sha == inventory.get("engineClosureSHA256") == expected_closure_sha,
                "Java engine source closure differs")
        class_pins = inventory.get("classes", {})
        require(set(classes) == set(class_pins), "Uninventoried or missing compiled class")
        require(roots <= set(classes), "Captured source has no compiled top-level class")
        for name in classes:
            top_level = name.split("$", 1)[0].removesuffix(".class") + ".class"
            require(top_level in roots and digest(archive.read(name)) == class_pins[name],
                    "Compiled class source association or byte pin differs")
        for api_class in API_CLASSES:
            require("ansatz/lean/jvm/" + api_class + ".class" in classes, "Missing Java facade class " + api_class)
        for nested in ["", "$Program", "$Node", "$Header", "$SourceBinding", "$HostExtern"]:
            require("ansatz/lean/jvm/internal/exec/Interpreter" + nested + ".class" in classes, "Missing engine class " + nested)
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
        closure_match = re.search(rb':engine-closure-sha256\s+"([0-9a-f]{64})"', metadata)
        require(closure_match is not None and closure_match.group(1).decode() == closure_sha,
                "Runtime metadata/engine closure differs")
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
        require(engine_sha == reviewed_primary_sha, "Runtime metadata/primary reviewed source pin differs")
        require(expected_engine_sha is None or engine_sha == expected_engine_sha, "Jar engine source pin differs")
        return {"jarBytes": path.stat().st_size, "jarSHA256": digest(path.read_bytes()),
                "entryCount": len(names), "engineClassCount": sum(name.startswith("ansatz/lean/jvm/internal/exec/") for name in classes),
                "javaAPIClassCount": sum(name.startswith("ansatz/lean/jvm/") and "/" not in name[len("ansatz/lean/jvm/"):] for name in classes),
                "publicProjectAPIAccepted": public_match.group(1) == b"true", "javaRelease": 17,
                "engineSourceSHA256": engine_sha, "engineClosureSHA256": closure_sha, "runtimeResources": resources,
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

