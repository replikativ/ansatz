#!/usr/bin/env python3
"""Assemble explicit checked bytes; never starts Lean/Java or discovers artifacts."""
import argparse, hashlib, json, os, pathlib, re, stat, struct, subprocess, tempfile, zipfile
LEAN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
JAR = "ec44338dbe9e44fc2484c16d00addf46468a14919f66a5d55c01db431f43fbed"
JAVA = "617e8e63247289ce8a03b0afcc7794b5de17fcaa6f0faf7365c88238b34e1bc2"
LIMIT = 512 * 1024 * 1024
def need(value, message):
    if not value: raise ValueError(message)
def canonical(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
def sha(data): return hashlib.sha256(data).hexdigest()
def rel(value):
    need(isinstance(value, str) and value and "\\" not in value and "\0" not in value, "relative path")
    p = pathlib.PurePosixPath(value)
    need(not p.is_absolute() and all(x not in ("", ".", "..") for x in value.split("/")), "normalized relative path")
    return p
def regular(root, name):
    p = root
    for part in rel(name).parts:
        p = p / part
        need(not p.is_symlink(), "symlink input")
    need(p.is_file(), "missing regular input")
    return p
def stamp(p):
    s = p.stat()
    return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
def checked_bytes(p, expected, cap):
    before = stamp(p)
    need(before[2] <= cap, "input extent")
    data = p.read_bytes()
    need(stamp(p) == before and len(data) == before[2] and sha(data) == expected, "input hash/stamp")
    return data
def copy_checked(source, dest, expected, extent):
    before = stamp(source)
    need(before[2] == extent, "source extent")
    h = hashlib.sha256(); total = 0
    dest.parent.mkdir(parents=True, exist_ok=True)
    with source.open("rb") as inp, dest.open("xb") as out:
        while True:
            chunk = inp.read(65536)
            if not chunk: break
            total += len(chunk)
            need(total <= extent, "source grew")
            h.update(chunk); out.write(chunk)
    need(total == extent and h.hexdigest() == expected and stamp(source) == before, "copied input changed")
def assemble(plan_path, expected_sha, output, roots):
    need(re.fullmatch("[0-9a-f]{64}", expected_sha), "independent plan SHA")
    plan = json.loads(checked_bytes(plan_path, expected_sha, 2 * 1024 * 1024))
    need(plan.get("schema") == "source4-pack-assembly/1", "plan schema")
    need(set(plan) == {"schema", "profile", "inputs", "dependency-artifacts", "runtime-build-artifact", "definition-order-sha256"}, "plan fields")
    order_path = pathlib.Path(__file__).with_name("definition-order.json")
    order = json.loads(checked_bytes(order_path, plan["definition-order-sha256"], 65536))
    profile = plan["profile"]
    need(profile.get("schema") == "ansatz-source4-bootstrap/1" and "artifacts" not in profile, "profile template")
    inputs = plan["inputs"]
    build_id = plan["runtime-build-artifact"]
    need(isinstance(inputs, dict) and len(inputs) + 1 <= 512 and build_id not in inputs, "artifact count")
    need(set(plan["dependency-artifacts"]) <= set(inputs) and plan["dependency-artifacts"], "explicit dependency provenance")
    need(not output.exists(), "output must be absent")
    output.parent.mkdir(parents=True, exist_ok=True)
    stage = pathlib.Path(tempfile.mkdtemp(prefix=output.name + ".pending-", dir=output.parent))
    # Failed staging is preserved for diagnosis. It is never published as a pack.
    artifacts = {}; used = set(); total = 0
    try:
        for ident, item in inputs.items():
            need(set(item) in ({"root", "path", "output", "sha256", "bytes"}, {"root", "git-path", "commit", "output", "sha256", "bytes"}), "input fields")
            need(isinstance(item["bytes"], int) and 0 <= item["bytes"] <= LIMIT, "artifact extent")
            total += item["bytes"]; need(total <= LIMIT, "aggregate extent")
            name = str(rel(item["output"])); need(name not in used, "duplicate output")
            need(name not in {"profile.json", "assembly-receipt.json", "runtime-build.json"}, "reserved output")
            used.add(name); dest = stage / name
            root = roots[item["root"]]
            if "git-path" in item:
                need(item["commit"] == LEAN, "only pinned upstream source extraction")
                gitpath = str(rel(item["git-path"]))
                # The requested immutable Git object, never checkout contents.
                size = subprocess.check_output(["git", "-C", str(root), "cat-file", "-s", item["commit"] + ":" + gitpath], text=True).strip()
                need(int(size) == item["bytes"] and int(size) <= 4 * 1024 * 1024, "upstream blob extent")
                data = subprocess.check_output(["git", "-C", str(root), "show", item["commit"] + ":" + gitpath])
                need(sha(data) == item["sha256"], "upstream blob hash")
                dest.parent.mkdir(parents=True, exist_ok=True); dest.write_bytes(data)
            else:
                copy_checked(regular(root, item["path"]), dest, item["sha256"], item["bytes"])
            artifacts[ident] = {"root": "pack", "path": name, "sha256": item["sha256"], "bytes": item["bytes"]}
        runtime = profile["runtime"]
        need(artifacts[runtime["jar"]]["sha256"] == JAR and artifacts[runtime["source"]]["sha256"] == JAVA, "accepted runtime identity")
        need(runtime["build-receipt"] == build_id, "build receipt reference")
        with zipfile.ZipFile(stage / artifacts[runtime["jar"]]["path"]) as jar:
            info = jar.getinfo("ansatz/research/ir/Interpreter.class")
            need(info.file_size <= 4 * 1024 * 1024, "class extent")
            with jar.open(info) as inp: head = inp.read(8)
        need(len(head) == 8 and head[:4] == bytes.fromhex("cafebabe") and struct.unpack(">H", head[6:8])[0] == 55, "actual Java11 class major")
        build = canonical({"schema": "java-ir-runtime-build/1", "java-release": 11, "class-major": 55, "lean-commit": LEAN, "target": "x86_64-unknown-linux-gnu", "jar-sha256": JAR, "source-sha256": JAVA, "scope": "Supplemental identity/ZIP evidence for previously accepted artifacts; no compilation or running-classpath proof."})
        (stage / "runtime-build.json").write_bytes(build)
        artifacts[build_id] = {"root": "pack", "path": "runtime-build.json", "sha256": sha(build), "bytes": len(build)}
        total += len(build); need(total <= LIMIT, "aggregate extent")
        profile["artifacts"] = artifacts
        for group in profile["directories"].values():
            need(group["root"] == "pack", "pack directory root")
            prefix = str(rel(group["path"])) + "/"
            expected = {artifacts[i]["path"] for i in group["files"]}
            actual = {n for n in used if n.startswith(prefix)}
            need(expected == actual, "directory complete selected file set")
        entries = {n: ident for ident, value in artifacts.items() for n in [value["path"]]}
        definitions = []
        for file, namespace in order["entry-namespaces"] + order["definitions"]:
            need(file in entries, "missing explicit definition " + file)
            text = (stage / file).read_text()
            need(re.search(r"\(ns\s+" + re.escape(namespace) + r"(?:\s|\))", text), "definition namespace")
            if [file, namespace] in order["definitions"]:
                definitions.append([entries[file], namespace])
        need(profile.get("definitions") in (None, definitions), "definition order")
        profile["definitions"] = definitions
        data = canonical(profile); need(len(data) <= 1024 * 1024, "profile extent")
        (stage / "profile.json").write_bytes(data)
        receipt = {"schema": "source4-pack-assembly-receipt/1", "plan-sha256": expected_sha, "profile-sha256": sha(data), "artifact-count": len(artifacts), "artifact-bytes": total, "directory-count": len(profile["directories"]), "definitions": len(definitions), "dependency-provenance": {i: artifacts[i] for i in plan["dependency-artifacts"]}, "JVM-or-native-executed": False, "runtime-acceptance": False, "scope": "Exact selected byte distribution, not actual running Clojure/kernel dependency basis or capability issuance."}
        (stage / "assembly-receipt.json").write_bytes(canonical(receipt))
        need(not output.exists(), "output appeared")
        os.rename(stage, output)
        return receipt
    except Exception as error:
        raise RuntimeError("Assembly failed; unissued staging retained at " + str(stage)) from error
def main():
    a = argparse.ArgumentParser(description=__doc__)
    a.add_argument("--plan", type=pathlib.Path, required=True); a.add_argument("--plan-sha256", required=True)
    a.add_argument("--output", type=pathlib.Path, required=True); a.add_argument("--root", action="append", default=[], metavar="ID=PATH")
    args = a.parse_args(); roots = {}
    for value in args.root:
        ident, path = value.split("=", 1)
        need(ident not in roots, "duplicate root")
        root = pathlib.Path(path); need(root.is_absolute() and root.is_dir() and not root.is_symlink(), "explicit root")
        need(root == root.resolve(), "canonical root")
        roots[ident] = root
    print(json.dumps(assemble(args.plan, args.plan_sha256, args.output, roots), sort_keys=True))
if __name__ == "__main__": main()
