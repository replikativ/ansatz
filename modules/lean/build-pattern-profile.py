#!/usr/bin/env python3
"""Build a local source-only Pattern jar from immutable pinned Git objects.

No checkout files, dependency resolution, compilation, installation or publishing.
The separate consumer gate requires an explicit audited Maven jar classpath.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile
import xml.etree.ElementTree as ET

PIN = "6d0242ee589d88b336f7dd6f820efa993d2b6f3b"
GROUP = "org.replikativ"
ARTIFACT = "pattern-source-profile"
VERSION = "0.0.0-" + PIN[:12]
DIRECT_DEPS = [("com.github.pangloss", "pure-conditioning", "1.0.35"),
               ("com.github.pangloss", "genera", "1.0.28"),
               ("uncomplicate", "fluokitten", "0.10.0"),
               ("potemkin", "potemkin", "0.4.7")]


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def pinned_entries(repo):
    if git(repo, "rev-parse", PIN + "^{commit}").decode().strip() != PIN:
        raise ValueError("Exact pinned Pattern commit unavailable")
    entries = {}
    for item in git(repo, "ls-tree", "-r", "-z", PIN).split(b"\0"):
        if not item:
            continue
        header, raw_path = item.split(b"\t", 1)
        mode, kind, blob = header.decode().split()
        path = raw_path.decode()
        if not (path.startswith(("src/", "resources/")) or path in {"LICENSE", "NOTICE", "README.md", "deps.edn"}):
            continue
        if mode not in {"100644", "100755"} or kind != "blob" or ".." in Path(path).parts:
            raise ValueError("Nonregular Pattern input: " + path)
        data = git(repo, "cat-file", "blob", blob)
        target = path.split("/", 1)[1] if path.startswith(("src/", "resources/")) else "META-INF/pattern-profile/" + path
        if target.endswith(".class") or target in entries:
            raise ValueError("Unexpected Pattern entry: " + target)
        entries[target] = data
    required = {"META-INF/pattern-profile/LICENSE", "META-INF/pattern-profile/README.md", "META-INF/pattern-profile/deps.edn"}
    if not required <= entries.keys():
        raise ValueError("Missing pinned licensing/dependency inputs")
    return entries


def pom():
    project = ET.Element("project", xmlns="http://maven.apache.org/POM/4.0.0")
    for tag, text in [("modelVersion", "4.0.0"), ("groupId", GROUP), ("artifactId", ARTIFACT),
                      ("version", VERSION), ("packaging", "jar"),
                      ("description", "Local source-only pinned Pattern validation profile; not a published release")]:
        ET.SubElement(project, tag).text = text
    deps = ET.SubElement(project, "dependencies")
    for group, artifact, version in DIRECT_DEPS:
        dep = ET.SubElement(deps, "dependency")
        for tag, text in [("groupId", group), ("artifactId", artifact), ("version", version)]:
            ET.SubElement(dep, tag).text = text
    return ET.tostring(project, encoding="utf-8", xml_declaration=True)


def build(repo, output):
    output = Path(output)
    if output.exists():
        raise ValueError("Refusing to replace existing artifact: " + str(output))
    entries = pinned_entries(repo)
    audit = {"schema": "pattern-source-profile/1", "git_url": "https://github.com/replikativ/pattern.git",
             "git_sha": PIN, "coordinate": f"{GROUP}/{ARTIFACT}:{VERSION}", "aot": False,
             "direct_dependencies": DIRECT_DEPS,
             "entries_sha256": {name: hashlib.sha256(data).hexdigest() for name, data in sorted(entries.items())}}
    prefix = f"META-INF/maven/{GROUP}/{ARTIFACT}/"
    entries[prefix + "pom.xml"] = pom()
    entries[prefix + "pom.properties"] = f"groupId={GROUP}\nartifactId={ARTIFACT}\nversion={VERSION}\n".encode()
    entries["META-INF/pattern-profile/audit.json"] = (json.dumps(audit, indent=2) + "\n").encode()
    output.parent.mkdir(parents=True, exist_ok=True)
    # Exclusive creation avoids replacing any immutable Maven/local artifact.
    with output.open("xb") as stream:
        with zipfile.ZipFile(stream, "w", compression=zipfile.ZIP_DEFLATED) as jar:
            for name, data in sorted(entries.items()):
                info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                jar.writestr(info, data)
    return {"jar_sha256": hashlib.sha256(output.read_bytes()).hexdigest(), **audit}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    print(json.dumps(build(args.repository, args.output), indent=2))
