#!/usr/bin/env python3
"""Export the authenticated observed frontend companion; never run its entry.

Caller explicitly supplies the already accepted pinned native exporter. Output
is a NEW bundle for source-setup/authenticate-overlay!, not authority to modify
an existing SourceBinding. The source and all local rows remain byte-exact.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import signal
import subprocess
import time

LEAN_PIN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
EXPORTER_PIN = "0b0344058631b8c3dc18a8a1a600f8100611eaf49c3b4ee5ad18a121651e736e"
BASE_INDEX = "74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e"
BASE = Path(__file__).resolve().parent.parent
MODULE = "ObservedFrontendCommand"
MiB = 1024 * 1024


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def mem_available():
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    raise RuntimeError("MemAvailable required")


def rss(pid):
    try:
        for line in Path(f"/proc/{pid}/status").read_text().splitlines():
            if line.startswith("VmRSS:"):
                return int(line.split()[1]) * 1024
    except FileNotFoundError:
        return 0
    return 0


def child_limits():
    # Lean reserves virtual runtime arenas/worker stacks; enforce resident
    # memory below instead of preventing runtime startup with an AS limit.
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_CPU, (60, 60))
    resource.setrlimit(resource.RLIMIT_FSIZE, (16 * MiB, 16 * MiB))


def typed_name(label):
    n = ["anonymous"]
    for part in label.split("."):
        n = ["str", n, part]
    return n



def verify_layout(rows, inventory, contract):
    by_label = {label(row["name"]): row for row in rows}
    main = by_label[MODULE + ".processCommandObserved"]["ir"]["fdecl"]
    parser_lambda = by_label[MODULE + ".processCommandObserved._lam_0"]["ir"]["fdecl"]
    gate = by_label[MODULE + ".beforeElaboration"]["ir"]["extern"]
    abi = contract["gate"]["rawABI"]
    if ([x["ty"] for x in gate["xs"]] != abi["parameters"] or
        [x["borrow"] for x in gate["xs"]] != abi["borrowed"] or gate["type"] != abi["result"]):
        raise RuntimeError("Actual borrowed gate ABI differs")
    for item in inventory:
        expected = contract["compiledRowPins"].get(label(item["name"]))
        if expected and item["sha256"] != expected:
            raise RuntimeError("Versioned companion compiled row differs")

    def nodes(root):
        todo = [(root, [])]
        visits = 0
        while todo:
            value, path = todo.pop()
            visits += 1
            if visits > 100000:
                raise RuntimeError("Companion structural audit bound")
            yield value, path
            if isinstance(value, dict):
                todo.extend((v, path + [k]) for k, v in value.items())
            elif isinstance(value, list):
                todo.extend((v, path + [i]) for i, v in enumerate(value))

    def calls(root, target):
        return [(v, path) for v, path in nodes(root)
                if isinstance(v, dict) and "fap" in v and label(v["fap"]["c"]) == target]

    gate_calls = calls(main, MODULE + ".beforeElaboration")
    elab_calls = calls(main, "Lean.Elab.Frontend.elabCommandAtFrontend")
    parser_calls = calls(parser_lambda, "Lean.Parser.parseCommand")
    if not (len(gate_calls) == len(elab_calls) == len(parser_calls) == 1):
        raise RuntimeError("Original parse/gate/elaboration static call inventory differs")
    ctors = [(v["ctor"], path) for v, path in nodes(main)
             if isinstance(v, dict) and "ctor" in v and
             label(v["ctor"]["i"]["name"]) == MODULE + ".Observation.mk"]
    expected = {"cidx": 0, "name": typed_name(MODULE + ".Observation.mk"), "size": 8, "usize": 0, "ssize": 4}
    if len(ctors) != 1 or ctors[0][0]["i"] != expected:
        raise RuntimeError("Actual Observation constructor layout differs")
    stores = [(v[:6], path) for v, path in nodes(main)
              if isinstance(v, list) and v and v[0] == "sset" and v[1] == {"idx": 59}]
    if sorted((v[2], v[3], v[5]) for v, _ in stores) != [(8, i, "uint8") for i in range(4)]:
        raise RuntimeError("Observation Boolean scalar slots differ")
    return {"schema": "observed-frontend-compiled-layout/1", "constructor": ctors[0][0],
            "constructor-path": ctors[0][1], "gate-fap": gate_calls[0],
            "original-elaboration-fap": elab_calls[0], "original-parser-fap": parser_calls[0],
            "bool-stores": stores, "observation-object-fields": contract["observation"]["objectFields"],
            "runtime-call-count-acceptance": False}


def label(name):
    if name == ["anonymous"]:
        return ""
    prefix = label(name[1])
    return (prefix + "." if prefix else "") + str(name[2])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--exporter", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    exporter = args.exporter.resolve()
    if sha(exporter) != EXPORTER_PIN:
        raise RuntimeError("Accepted exporter binary SHA differs")
    version = subprocess.check_output(["lean", "+leanprover/lean4:v4.33.1", "--version"], text=True).strip()
    if "version 4.33.1," not in version or LEAN_PIN not in version:
        raise RuntimeError("Pinned PATH/toolchain source identity differs")
    sysroot = Path(subprocess.check_output(["lean", "+leanprover/lean4:v4.33.1", "--print-prefix"], text=True).strip()).resolve()
    if mem_available() < 1536 * MiB:
        raise RuntimeError("System MemAvailable below 1.5GiB floor")
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = BASE / "lean" / (MODULE + ".lean")
    copied = out / source.name
    shutil.copyfile(source, copied)
    command = [str(exporter), "--source", str(copied), "--local", MODULE]
    environment = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_SYSROOT=str(sysroot),
                       LEAN_PATH=str(sysroot / "lib/lean"))
    environment["PATH"] = str(sysroot / "bin") + os.pathsep + environment.get("PATH", "")
    raw = out / "local-ir.jsonl"
    errors = out / "export.stderr"
    started = time.monotonic()
    peak = 0
    stop = None
    with raw.open("wb") as stdout, errors.open("wb") as stderr:
        proc = subprocess.Popen(command, stdout=stdout, stderr=stderr, env=environment,
                                start_new_session=True, preexec_fn=child_limits)
        while proc.poll() is None:
            peak = max(peak, rss(proc.pid))
            if time.monotonic() - started > 90:
                stop = "wall deadline"
            elif peak > 1228 * MiB:
                stop = "RSS cap"
            elif mem_available() < 1536 * MiB:
                stop = "MemAvailable floor"
            elif raw.stat().st_size > 16 * MiB or errors.stat().st_size > MiB:
                stop = "output cap"
            if stop:
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    proc.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                break
            time.sleep(0.02)
        exit_code = proc.wait()
    receipt = {"schema": "native-source-local-ir-export/1", "exit": exit_code,
               "stop": stop, "stderr-bytes": errors.stat().st_size,
               "no-source-main-execution": True, "no-checkpoint-restore": True,
               "no-imported-closure-export": True, "source-sha256": sha(copied),
               "exporter-binary-sha256": sha(exporter), "lean-commit": LEAN_PIN,
               "raw-output-sha256": sha(raw), "raw-output-bytes": raw.stat().st_size,
               "elapsed-seconds": time.monotonic() - started, "peak-rss-bytes": peak,
               "command": command, "toolchain": version, "threads": 1}
    write_json(out / "export-receipt.json", receipt)
    if exit_code != 0 or stop or errors.stat().st_size:
        raise RuntimeError(f"Export failed; diagnostic receipt preserved at {out}")
    lines = raw.read_bytes().splitlines()
    stream = [json.loads(line) for line in lines]
    manifest, rows = stream[0], stream[1:]
    if (manifest.get("kind"), manifest.get("schema"), manifest.get("leanVersion")) != ("manifest", "lean-ir-probe/1", "4.33.1"):
        raise RuntimeError("Unexpected export manifest")
    if manifest.get("runtimeProfile") != {"wordBits": 64, "target": "x86_64-unknown-linux-gnu"}:
        raise RuntimeError("Unsupported ABI profile")
    module = typed_name(MODULE)
    plan = manifest.get("initializationPlan")
    if not plan or plan.get("module") != module:
        raise RuntimeError("Missing actual module initialization plan")
    roles = set()
    inventory = []
    by_name = {}
    for line, row in zip(lines[1:], rows):
        ir = row.get("ir", {})
        if row.get("kind") != "decl" or row.get("sourceLocal") is not True or row.get("sourceModule") != module or len(ir) != 1:
            raise RuntimeError("Missing/nonlocal/invalid companion row")
        kind, decl = next(iter(ir.items()))
        name = row["name"]
        key = json.dumps(name, separators=(",", ":"))
        if kind not in ("fdecl", "extern") or decl["f"] != name or key in by_name:
            raise RuntimeError("Invalid or duplicate local typed declaration")
        by_name[key] = row
        role = row["runtime"]["role"]
        if role not in ("ordinary", "closed", "value") or row["runtime"].get("initializer") is not None:
            raise RuntimeError("Unsupported source-setup row role/initializer")
        roles.add(role)
        inventory.append({"name": name, "sha256": hashlib.sha256(line).hexdigest(), "kind": kind,
                          "parameters": decl["xs"], "result": decl["type"], "role": role})
    if not 1 <= len(rows) <= 10000:
        raise RuntimeError("Companion inventory outside source-setup bounds")
    gate = by_name[json.dumps(typed_name(MODULE + ".beforeElaboration"), separators=(",", ":"))]["ir"]["extern"]
    entries = gate["ext"]["entries"]
    if not any(e.get("standard", {}).get("fn") == "ansatz_observed_frontend_gate_v1" for e in entries):
        raise RuntimeError("Missing actual source gate extern")
    pins = {"source_sha256": sha(copied), "producer_sha256": sha(exporter),
            "local_ir_sha256": sha(raw), "export_receipt_sha256": sha(out / "export-receipt.json"),
            "base_index_sha256": BASE_INDEX}
    spec = {"module": module, "row-count": len(rows), "actions": plan["actions"], "pins": pins,
            "source-file": copied.name, "producer-file": "caller-supplied accepted exporter"}
    contract_path = BASE / "research/java-ir-baseline/observed-frontend/contract.json"
    audit = verify_layout(rows, inventory, json.loads(contract_path.read_text()))
    write_json(out / "compiled-layout.json", audit)
    write_json(out / "headers.json", inventory)
    write_json(out / "overlay-spec.json", spec)
    # Manifest LAST; failed exports never publish an admission candidate.
    write_json(out / "bundle-manifest.json", {"schema": "observed-frontend-source-bundle/1", "pins": pins,
               "source-contract-sha256": sha(contract_path),
               "compiled-layout-sha256": sha(out / "compiled-layout.json"),
               "runner-sha256": sha(Path(__file__)), "row-count": len(rows), "roles": sorted(roles),
               "gate": next(x for x in inventory if x["name"] == typed_name(MODULE + ".beforeElaboration")),
               "entry": next(x for x in inventory if x["name"] == typed_name(MODULE + ".processCommandObserved")),
               "runtimeAcceptance": False, "handlerAuthorityIncluded": False})
    print(json.dumps({"directory": str(out), "rows": len(rows), "pins": pins, "receipt": receipt}, indent=2))


if __name__ == "__main__":
    main()
