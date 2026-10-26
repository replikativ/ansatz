"""Validate the isolated, explicitly pinned Pattern consumer dependency basis.

Metadata validation only: this module neither resolves dependencies nor starts a
JVM. A caller must independently pin the lock bytes before using its paths.
"""
import hashlib
import json
from pathlib import Path
import re
import zipfile

ROOTS = {"org.clojure/clojure": "1.12.4", "org.clojure/data.json": "2.5.1",
         "org.replikativ/pattern": "1.0.452"}
LIBS = {**ROOTS, "org.clojure/spec.alpha": "0.5.238",
        "org.clojure/core.specs.alpha": "0.4.74",
        "com.github.pangloss/pure-conditioning": "1.0.35",
        "com.github.pangloss/genera": "1.0.28", "uncomplicate/fluokitten": "0.10.0",
        "potemkin/potemkin": "0.4.7", "riddley/riddley": "0.1.12",
        "org.clojure/core.memoize": "1.1.266", "org.clojure/core.cache": "1.1.234",
        "org.clojure/data.priority-map": "1.2.0"}
SHA = re.compile(r"[0-9a-f]{64}\Z")


def digest(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        while block := stream.read(1024 * 1024):
            result.update(block)
    return result.hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate basis JSON key")
        result[key] = value
    return result


def physical(path):
    path = Path(path)
    if not path.is_absolute() or not path.is_file() or any(p.is_symlink() for p in [path, *path.parents]):
        raise ValueError("basis requires physical absolute regular paths")
    return path


def check_jar(path):
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        if len(names) != len(set(names)):
            raise ValueError("duplicate JAR resource")
        for name in names:
            # The same project provider under a multi-release prefix also shadows
            # authenticated source/classes. Pattern's own AOT is allowed.
            stripped = re.sub(r"^META-INF/versions/[0-9]+/", "", name)
            if (stripped.startswith(("ansatz/", "ansatz$", "prototype/", "prototype$"))
                    or stripped in {"ansatz.clj", "ansatz.cljc", "ansatz__init.class",
                                    "prototype.clj", "prototype.cljc", "prototype__init.class"}):
                raise ValueError("dependency JAR contains project provider")
            if stripped.startswith(("org/bytedeco/llvm/", "org/llvm/")):
                raise ValueError("LLVM providers are outside this dependency profile")
        if "META-INF/MANIFEST.MF" in names:
            manifest = archive.read("META-INF/MANIFEST.MF").decode("utf-8").replace("\r\n", "\n")
            if re.search(r"(?im)^Class-Path:", manifest):
                raise ValueError("dependency manifest Class-Path forbidden")


def load(path, expected_sha256):
    path = physical(path)
    if not isinstance(expected_sha256, str) or not SHA.fullmatch(expected_sha256) or digest(path) != expected_sha256:
        raise ValueError("independent Maven basis digest mismatch")
    if path.stat().st_size > 1024 * 1024:
        raise ValueError("Maven basis metadata bound")
    data = json.loads(path.read_text(), object_pairs_hook=unique)
    if set(data) != {"schema", "roots", "dependencies"} or data["schema"] != "coherent-maven-basis/1" or data["roots"] != ROOTS:
        raise ValueError("Maven basis schema/roots mismatch")
    rows = data["dependencies"]
    if not isinstance(rows, list) or len(rows) != len(LIBS):
        raise ValueError("exact isolated thirteen-JAR basis required")
    libs, ids, paths = {}, set(), set()
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"lib", "version", "id", "sha256", "path", "pom-sha256", "pom-path"}:
            raise ValueError("Maven dependency schema")
        lib, version = row["lib"], row["version"]
        if lib in libs or LIBS.get(lib) != version:
            raise ValueError("Maven dependency duplicate/unexpected version")
        libs[lib] = version
        jar, pom = physical(row["path"]), physical(row["pom-path"])
        if row["id"] != "dependencies/" + jar.name or jar.suffix != ".jar" or pom.suffix != ".pom" or row["id"] in ids or str(jar) in paths:
            raise ValueError("Maven dependency identity/duplicate path")
        ids.add(row["id"]); paths.add(str(jar))
        for source, field in [(jar, "sha256"), (pom, "pom-sha256")]:
            if not isinstance(row[field], str) or not SHA.fullmatch(row[field]) or digest(source) != row[field]:
                raise ValueError("Maven artifact pin mismatch")
        check_jar(jar)
    if libs != LIBS:
        raise ValueError("Maven basis library closure mismatch")
    return data
