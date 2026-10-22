#!/usr/bin/env python3
"""Bounded native-only G1 prototype gate. Run only with an approved tool/input pin manifest.
No JVM, bootstrap export, runtime profile issuance, logical-region cleanup or retry.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

MIB = 1024 * 1024
PINNED_LEAN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"


def sha(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(MIB), b""):
            digest.update(block)
    return digest.hexdigest()


def available():
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    raise RuntimeError("MemAvailable unavailable")


def rss(pid):
    try:
        for line in Path(f"/proc/{pid}/status").read_text().splitlines():
            if line.startswith("VmRSS:"):
                return int(line.split()[1]) * 1024
    except (FileNotFoundError, ProcessLookupError):
        pass
    return 0


def group_rss(group):
    total = rss(os.getpid())
    for entry in Path("/proc").iterdir():
        if entry.name.isdecimal():
            try:
                if os.getpgid(int(entry.name)) == group:
                    total += rss(entry.name)
            except ProcessLookupError:
                pass
    return total


def extern_signature(row):
    ir = row.get("ir", {}).get("extern")
    # Keep the complete actual external declaration, excluding its Lean name:
    # external implementation symbol/ABI (parameters including borrowedness/result).
    if not isinstance(ir, dict):
        return None
    payload = {"ext": ir["ext"], "type": ir["type"],
               "xs": [{"borrow": x["borrow"], "ty": x["ty"]} for x in ir["xs"]]}
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


def name_key(name):
    return json.dumps(name, separators=(",", ":"))


def abi_shape(decl):
    return {"params": [{"ty": x["ty"], "borrow": x["borrow"]} for x in decl["xs"]],
            "return-type": decl["type"]}


def selected_symbol(ext):
    for entry in ext["ext"]["entries"]:
        payload = next(iter(entry.values()))
        if payload.get("backend") in (["str", ["anonymous"], "all"], ["str", ["anonymous"], "c"]):
            return entry.get("standard", {}).get("fn")
    return None


def hosted_support(externals, functions, exports, capabilities):
    counts = {"rawBindings": 0, "primitives": 0, "guestRedirects": 0}
    for row in externals:
        ext = row["ir"]["extern"]
        symbol, shape = selected_symbol(ext), abi_shape(ext)
        if symbol in capabilities["raw-bindings"]:
            if capabilities["raw-bindings"][symbol] != shape:
                raise RuntimeError("actual raw-binding ABI mismatch")
            counts["rawBindings"] += 1
            continue
        explicit = row.get("redirect")
        target = explicit["name"] if explicit else exports.get(symbol)
        if explicit and symbol in exports and explicit["name"] != exports[symbol]:
            raise RuntimeError("export redirect disagreement")
        if target is not None:
            actual = functions.get(name_key(target))
            if actual != shape:
                raise RuntimeError("redirect lacks exact actual guest function ABI")
            if explicit and abi_shape({"xs": explicit["params"], "type": explicit["type"]}) != actual:
                raise RuntimeError("stored redirect ABI mismatch")
            counts["guestRedirects"] += 1
            continue
        spec = capabilities["primitives"].get(symbol)
        if (not spec or len(shape["params"]) not in spec["arities"] or
                shape not in capabilities["signatures"].get(symbol, [])):
            raise RuntimeError("external lacks actual implemented hosted primitive/ABI: " + str(symbol))
        counts["primitives"] += 1
    return counts


def rows(path):
    with open(path) as stream:
        while True:
            line = stream.readline(16 * MIB + 1)
            if not line:
                return
            if len(line) > 16 * MIB:
                raise RuntimeError("JSONL row bound")
            yield json.loads(line)


def index_declarations(path):
    """Stream only the sorted index's first declarations array; no full index/DAG load."""
    decoder = json.JSONDecoder()
    with path.open() as stream:
        prefix = stream.read(len('{"declarations":['))
        if prefix != '{"declarations":[':
            raise RuntimeError("unexpected admitted index serialization")
        buffer = ""
        while True:
            if not buffer:
                buffer = stream.read(65536)
            buffer = buffer.lstrip()
            if buffer.startswith("]"):
                return
            if buffer.startswith(","):
                buffer = buffer[1:].lstrip()
            while True:
                try:
                    value, end = decoder.raw_decode(buffer)
                    buffer = buffer[end:]
                    break
                except json.JSONDecodeError:
                    extra = stream.read(65536)
                    if not extra or len(buffer) + len(extra) > 16 * MIB:
                        raise RuntimeError("admitted index row malformed/over bound")
                    buffer += extra
            if not isinstance(value, list) or len(value) != 2:
                raise RuntimeError("admitted index declaration shape")
            yield value


def main():
    start = time.monotonic()
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--pins", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    pins = json.loads(args.pins.read_text())
    for entry in pins["files"]:
        if sha(entry["path"]) != entry["sha256"]:
            raise RuntimeError("input pin mismatch: " + entry["path"])
    if available() < 5 * 1024 * MIB:
        raise RuntimeError("preflight MemAvailable below 5GiB")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    oleans = output / "oleans"
    oleans.mkdir()
    toolchain = Path(pins["toolchain"])
    lean = str(toolchain / "bin/lean")
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(oleans), str(toolchain / "lib/lean")]),
               LD_LIBRARY_PATH=str(toolchain / "lib/lean"), LEAN_NUM_THREADS="1", LANG="C.UTF-8")
    receipt = {"schema": "ansatz-source-graph-native-run/1", "status": "running",
               "pinManifestSha256": sha(args.pins), "commands": [], "peakGroupRSSBytes": 0,
               "minAvailableBytes": available(), "wallLimitSeconds": 300,
               "groupRSSLimitBytes": 2048 * MIB, "availableFloorBytes": 2048 * MIB}

    def run(label, command):
        stdout = output / (label + ".stdout")
        stderr = output / (label + ".stderr")
        item = {"label": label, "argv": command}
        receipt["commands"].append(item)
        if (time.monotonic() - start >= 300 or available() < 2048 * MIB or
                rss(os.getpid()) > 2048 * MIB):
            raise RuntimeError("pre-spawn deadline/memory guard")
        with stdout.open("wb") as out, stderr.open("wb") as err:
            proc = subprocess.Popen(command, stdout=out, stderr=err, env=env, start_new_session=True)
            item["ownedProcessGroup"] = proc.pid
            try:
                while True:
                    used, free = group_rss(proc.pid), available()
                    receipt["peakGroupRSSBytes"] = max(receipt["peakGroupRSSBytes"], used)
                    receipt["minAvailableBytes"] = min(receipt["minAvailableBytes"], free)
                    if time.monotonic() - start > 300:
                        raise RuntimeError("global 300-second deadline")
                    if used > 2048 * MIB or free < 2048 * MIB:
                        raise RuntimeError("memory guard")
                    if stdout.stat().st_size + stderr.stat().st_size > 128 * MIB:
                        raise RuntimeError("per-command output guard")
                    # Observe without reaping: the leader PID stays reserved
                    # until scoped group cleanup, preventing PID/group reuse.
                    status = os.waitid(os.P_PID, proc.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
                    if status is not None:
                        code = status.si_status if status.si_code == os.CLD_EXITED else -status.si_status
                        item["exitCode"] = code
                        if code != 0:
                            raise RuntimeError("command failed: " + label)
                        break
                    time.sleep(0.05)
            finally:
                # Only this driver's freshly issued child process group is targeted.
                # Group cleanup also covers any unexpectedly lingering child at exit.
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
                item["stdoutSha256"], item["stderrSha256"] = sha(stdout), sha(stderr)
        return stdout

    try:
        githash = run("lean-githash", [lean, "--githash"]).read_text().strip()
        if githash != PINNED_LEAN:
            raise RuntimeError("wrong Lean commit")
        run("bb-version", [pins["bb"], "--version"])
        for module in ("SourceModuleImport", "SourceModuleExport", "SourceModuleGraphImport",
                       "SourceModuleGraphImportOracle"):
            run("compile-" + module, [lean, "-R", "lean", "-o", str(oleans / (module + ".olean")), "lean/" + module + ".lean"])
        fixture_outputs = []
        for module in ("GraphOracleA", "GraphOracleB", "GraphOracleC"):
            run("fixture-" + module, [lean, "-R", "lean/source-graph-fixtures", "-o", str(oleans / (module + ".olean")),
                                      "lean/source-graph-fixtures/" + module + ".lean"])
            artifact = oleans / (module + ".olean")
            fixture_outputs.append({"module": module, "path": str(artifact),
                                    "bytes": artifact.stat().st_size, "sha256": sha(artifact)})
        receipt["fixtureOutputs"] = fixture_outputs

        def check_fixture_outputs(label):
            observed = [{"module": row["module"], "path": row["path"],
                         "bytes": Path(row["path"]).stat().st_size, "sha256": sha(row["path"])}
                        for row in fixture_outputs]
            receipt.setdefault("fixtureOutputChecks", {})[label] = observed
            if observed != fixture_outputs:
                raise RuntimeError("independent CLI fixture output changed: " + label)

        capabilities = json.loads(Path(pins["runtimeCapabilities"]).read_text())
        if (capabilities.get("schema") != "live-hosted-runtime-ABI-capabilities/1" or
                capabilities.get("consumer-id") != "742d8e49cd934083ba390b0be19a64192adf6a06e8eba4b255f147fb9e3b9326" or
                capabilities.get("checking-authority") is not False or
                len(capabilities["primitives"]) != 313 or len(capabilities["signatures"]) != 314 or
                len(capabilities["raw-bindings"]) != 6 or capabilities.get("guest-invocations") != 0):
            raise RuntimeError("actual frozen runtime capability inventory mismatch")
        wanted = {}
        audits = []
        def host_guard():
            used, free = rss(os.getpid()), available()
            receipt["peakGroupRSSBytes"] = max(receipt["peakGroupRSSBytes"], used)
            receipt["minAvailableBytes"] = min(receipt["minAvailableBytes"], free)
            if time.monotonic() - start > 300 or used > 2048 * MIB or free < 2048 * MIB:
                raise RuntimeError("host deadline/memory guard")
        for module, source in [("SourceModuleGraphImport", "lean/SourceModuleGraphImport.lean")] + [
                (m, "lean/source-graph-fixtures/" + m + ".lean") for m in ("GraphOracleA", "GraphOracleB", "GraphOracleC")]:
            path = run("export-" + module, [pins["exporter"], "--source", source, "--closure", "--local", module])
            manifests, local, count, externs = [], 0, 0, set()
            functions, external_rows = {}, []
            expected_module = ["str", ["anonymous"], module]
            for row in rows(path):
                host_guard()
                count += 1
                if row.get("kind") == "manifest":
                    manifests.append(row)
                elif row.get("kind") == "missing":
                    raise RuntimeError("missing closure row")
                elif row.get("kind") == "decl":
                    if row.get("sourceLocal") is True:
                        if row.get("sourceModule") != expected_module:
                            raise RuntimeError("local row source module mismatch")
                        local += 1
                    fdecl = row.get("ir", {}).get("fdecl")
                    if fdecl is not None:
                        if fdecl["f"] != row["name"]:
                            raise RuntimeError("function row name mismatch")
                        functions[name_key(row["name"])] = abi_shape(fdecl)
                else:
                    raise RuntimeError("unknown export record")
                signature = extern_signature(row)
                if signature is not None:
                    externs.add(signature)
                    external_rows.append({"name": row["name"], "ir": {"extern": row["ir"]["extern"]},
                                          "redirect": row.get("redirect")})
                    name = json.dumps(row["name"], separators=(",", ":"))
                    if name in wanted and wanted[name] != signature:
                        raise RuntimeError("exported external ABI conflict")
                    wanted[name] = signature
            if len(manifests) != 1 or not local:
                raise RuntimeError("missing/duplicate manifest or empty source inventory")
            manifest = manifests[0]
            if (manifest.get("schema") != "lean-ir-probe/1" or manifest.get("leanVersion") != "4.33.1" or
                    manifest.get("runtimeProfile") != {"wordBits": 64, "target": "x86_64-unknown-linux-gnu"}):
                raise RuntimeError("source exporter schema/version/ABI mismatch")
            # Legacy exact exporter has no commit field; its executable+source
            # are pinned, installed Lean and actual oracle independently check githash.
            exports = {}
            for entry in manifest["exports"]:
                if entry["symbol"] in exports and exports[entry["symbol"]] != entry["name"]:
                    raise RuntimeError("conflicting manifest export target")
                exports[entry["symbol"]] = entry["name"]
            support = hosted_support(external_rows, functions, exports, capabilities)
            plan = manifest.get("initializationPlan")
            if not isinstance(plan, dict) or plan.get("kind") != "initialization-plan" or plan.get("actions") != []:
                raise RuntimeError("source initializer actions absent/unsupported")
            if plan.get("module") != expected_module or plan.get("moduleSystem") is not False:
                raise RuntimeError("initialization plan module/profile mismatch")
            audits.append({"hostedSupport": support, "module": module, "localRows": local, "closureRows": count - 1,
                           "externalABIs": len(externs), "actions": []})
        if not wanted:
            raise RuntimeError("external audit unexpectedly empty")
        store = Path(pins["admittedStore"])
        index = store / "indexes" / (pins["admittedIndexSha256"] + ".json")
        if sha(index) != pins["admittedIndexSha256"]:
            raise RuntimeError("admitted catalogue index hash mismatch")
        found = set()
        for ordinal, (name, digest) in enumerate(index_declarations(index)):
            if ordinal % 256 == 0:
                host_guard()
            key = json.dumps(name, separators=(",", ":"))
            if key not in wanted:
                continue
            if not isinstance(digest, str) or len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
                raise RuntimeError("invalid admitted CAS row hash")
            blob = store / "declarations" / (digest + ".json")
            if blob.stat().st_size > 16 * MIB or sha(blob) != digest:
                raise RuntimeError("admitted CAS row bound/hash mismatch")
            row = json.loads(blob.read_text())
            if json.dumps(row["name"], separators=(",", ":")) != key or extern_signature(row) != wanted[key]:
                raise RuntimeError("external symbol/ABI differs from admitted row")
            found.add(key)
        if found != set(wanted):
            raise RuntimeError("new external declaration outside admitted producer catalogue")
        for audit in audits:
            audit["newExternalABIs"] = 0
        (output / "closure-audit.json").write_text(json.dumps(audits, indent=2) + "\n")
        check_fixture_outputs("beforeOracle")
        try:
            native = run("native-oracle", [lean, "-R", "lean", "--run", "lean/SourceModuleGraphImportOracle.lean",
                                           "lean/source-graph-fixtures", str(oleans)])
        finally:
            check_fixture_outputs("afterOracle")
        evidence = json.loads(native.read_text())
        if (evidence.get("sourceCount") != 3 or evidence.get("structuralDiamond") is not True or
                evidence.get("leanCommit") != PINNED_LEAN):
            raise RuntimeError("native oracle incomplete")
        run("g0-order-comparison", [pins["bb"], "scripts/check-source-graph-plan.bb", str(native)])
        receipt.update(status="passed", nativeAttributionEntries=evidence["attributionEntriesCompared"], audits=audits)
    except BaseException as exc:
        receipt.update(status="failed", failureType=type(exc).__name__, failure=str(exc))
        raise
    finally:
        receipt["elapsedSeconds"] = time.monotonic() - start
        (output / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
