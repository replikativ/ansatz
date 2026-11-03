#!/usr/bin/env python3
"""Build an unpublished, source-closed native entry checkpoint.

This does not assemble a producer bundle or admit any executable. Default mode
supplies original interpreter-lookup wrappers as a probe shared module. Optional
standalone mode links the configured toolchain's existing static Lean libraries.
Neither mode is a claim of a portable published bundle.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import re
import signal
import shutil
import subprocess
import time

LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
MODULES = ("NativeEntryTransport", "NativeTypeGraph", "NativeNominalEntryEvidence")
FLOOR = 2 * 1024**3
RSS_LIMIT = 512 * 1024**2


def sha(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":")).encode()


def memory_available():
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    raise RuntimeError("MemAvailable unavailable; refusing native process")


def group_rss(root_pid):
    """Conservative sum of RSS for the root and observed owned descendants."""
    processes = {}
    for item in Path("/proc").iterdir():
        if not item.name.isdigit():
            continue
        try:
            fields = {}
            for line in (item / "status").read_text().splitlines():
                if line.startswith(("PPid:", "VmRSS:")):
                    key, value = line.split(":", 1)
                    fields[key] = int(value.split()[0])
            processes[int(item.name)] = (fields.get("PPid", -1), fields.get("VmRSS", 0) * 1024)
        except (OSError, ValueError):
            continue
    owned = {root_pid}
    while True:
        expanded = owned | {pid for pid, (parent, _) in processes.items() if parent in owned}
        if expanded == owned:
            return sum(processes.get(pid, (-1, 0))[1] for pid in owned)
        owned = expanded


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sysroot", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True,
                        help="New, nonexisting candidate directory")
    parser.add_argument("--compile-only", action="store_true",
                        help="Compile the source-closed modules only; no C or linker process")
    parser.add_argument("--standalone", action="store_true",
                        help="Build an unpublished entry executable using existing static Lean libraries")
    parser.add_argument("--compile-time-import-experiment", action="store_true",
                        help="Fresh source-closed deriving meta-import experiment; bounded link only")
    parser.add_argument("--resume-link", type=Path,
                        help="Reuse matching source-closed completed Lean/C products; refine link only")
    parser.add_argument("--link-rss-mib", type=int, default=512, choices=(512, 768, 1536),
                        help="Explicit link-only RSS budget; all other jobs remain capped at 512 MiB")
    parser.add_argument("--link-memory-floor-mib", type=int, default=2048, choices=(2048, 3072, 4096))
    args = parser.parse_args()
    if args.compile_only and (args.standalone or args.resume_link):
        parser.error("--compile-only excludes standalone/resume modes")
    if args.resume_link and not args.standalone:
        parser.error("--resume-link requires --standalone")
    if args.link_rss_mib == 1536 and args.link_memory_floor_mib < 4096:
        parser.error("A 1536 MiB one-time producer link requires at least a 4 GiB floor")
    if args.link_rss_mib > 512 and ((not args.resume_link and not args.compile_time_import_experiment) or args.link_memory_floor_mib < 3072):
        parser.error("A larger link-only budget requires explicit resume/structural experiment and a 3 GiB floor")
    sysroot = args.sysroot.resolve(strict=True)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source_dir = Path(__file__).resolve().parent / "src"
    closure = []
    for name in MODULES:
        source = source_dir / (name + ".lean")
        if source.is_symlink() or not source.is_file():
            raise RuntimeError("Expected regular maintained source: " + str(source))
        target = output / source.name
        target.write_bytes(source.read_bytes())
        closure.append({"module": ["str", ["anonymous"], name],
                        "source": target.name, "sha256": sha(target)})
    receipt = {"schema": "lean-native-entry-candidate/1",
               "scope": ("unpublished-compiler-only" if args.compile_only else
                         "unpublished-static-entry" if args.standalone else "unpublished-transport-shared-only"),
               "sourceClosure": closure,
               "builderSHA256": sha(Path(__file__).resolve()),
               "compileTimeImportExperiment": args.compile_time_import_experiment,
               "sourceClosureSHA256": hashlib.sha256(canonical(closure)).hexdigest(),
               "cpuSecondsPerProcess": 60, "wallSecondsPerProcess": 60,
               "sampledAggregateRSSLimitBytes": RSS_LIMIT, "processes": []}
    receipt["standaloneLinkConfig"] = {"supportInterpreter": True,
        "interpreterExportFlag": "-rdynamic", "linkerThreads": 1,
        "authority": "pinned Lake.Config.LeanExe.exeOnlyLinkArgs"} if args.standalone else None
    receipt["linkOnlyBudget"] = {"rssLimitBytes": args.link_rss_mib * 1024**2,
                                 "memoryFloorBytes": args.link_memory_floor_mib * 1024**2}
    receipt["toolSHA256"] = {name: sha(sysroot / "bin" / name)
                            for name in ("lean", "leanc", "clang", "ld.lld")}
    if args.resume_link:
        previous = args.resume_link.resolve(strict=True)
        previous_receipt = previous / "candidate-receipt.json"
        prior = json.loads(previous_receipt.read_text())
        if prior.get("sourceClosure") != closure or prior.get("leanCommit") != LEAN_COMMIT:
            raise RuntimeError("Resume source closure/toolchain identity mismatch")
        compile_prior = prior
        compile_directory = previous
        if "resume" in prior:
            predecessor = previous / "predecessor-receipt.json"
            if sha(predecessor) != prior["resume"]["receiptSHA256"]:
                raise RuntimeError("Predecessor receipt chain changed")
            compile_prior = json.loads(predecessor.read_text())
            compile_directory = Path(prior["resume"]["directory"])
            for item in prior["resume"]["capturedProductSnapshots"]:
                if sha(previous / item["path"]) != item["sha256"]:
                    raise RuntimeError("Previously captured source-closed product changed")
            if compile_prior.get("sourceClosure") != closure:
                raise RuntimeError("Compile receipt source closure differs")
        completed = {item["label"] for item in compile_prior["processes"] if item.get("exit") == 0}
        required = {prefix + name for prefix in ("lean-", "cc-") for name in MODULES}
        if not required <= completed:
            raise RuntimeError("Resume requires all successful Lean and C compile receipts")
        for item in compile_prior["processes"]:
            for key in ("stdout", "stderr"):
                info = item[key]
                if sha(compile_directory / info["path"]) != info["sha256"]:
                    raise RuntimeError("Predecessor process log changed")
        snapshots = []
        for name in MODULES:
            if sha(previous / (name + ".lean")) != sha(output / (name + ".lean")):
                raise RuntimeError("Predecessor staged source changed")
            for suffix in (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir", ".c", ".o"):
                source = previous / (name + suffix)
                if suffix not in (".olean", ".c", ".o") and not source.exists():
                    continue
                if source.is_symlink() or not source.is_file():
                    raise RuntimeError("Missing/irregular predecessor product")
                expected = sha(source)
                shutil.copyfile(source, output / source.name)
                if sha(source) != expected or sha(output / source.name) != expected:
                    raise RuntimeError("Predecessor product changed while capturing")
                snapshots.append({"path": source.name, "bytes": source.stat().st_size, "sha256": expected})
        receipt["resume"] = {"directory": str(previous), "receiptSHA256": sha(previous_receipt),
                             "capturedProductSnapshots": snapshots}
        shutil.copyfile(previous_receipt, output / "predecessor-receipt.json")
    environment = os.environ.copy()
    for key in ("LEAN_CC", "CFLAGS", "CPPFLAGS", "CXXFLAGS", "LDFLAGS"):
        environment.pop(key, None)
    environment.update(LEAN_SYSROOT=str(sysroot), LEAN_PATH=str(output),
                       LEAN_NUM_THREADS="1", MALLOC_ARENA_MAX="1",
                       PATH=str(sysroot / "bin") + ":" + environment.get("PATH", ""))
    receipt["environment"] = {key: environment[key] for key in
                              ("LEAN_SYSROOT", "LEAN_PATH", "LEAN_NUM_THREADS", "MALLOC_ARENA_MAX", "PATH")}

    def save():
        roles = (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir", ".c", ".o", ".so")
        receipt["moduleProductRoles"] = [
            {"module": name, "roles": [
                {"role": role, "present": (output / (name + role)).is_file(),
                 **({"bytes": (output / (name + role)).stat().st_size,
                     "sha256": sha(output / (name + role))}
                    if (output / (name + role)).is_file() else {})}
                for role in roles]} for name in MODULES]
        (output / "candidate-receipt.json").write_bytes(canonical(receipt) + b"\n")

    def verify_sources():
        for item in closure:
            if sha(output / item["source"]) != item["sha256"]:
                raise RuntimeError("Staged source changed: " + item["source"])
        for item in receipt.get("resume", {}).get("capturedProductSnapshots", []):
            if sha(output / item["path"]) != item["sha256"]:
                raise RuntimeError("Captured link input changed: " + item["path"])

    def limits():
        resource.setrlimit(resource.RLIMIT_CPU, (60, 60))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        resource.setrlimit(resource.RLIMIT_FSIZE, (256 * 1024**2, 256 * 1024**2))

    def run(label, command):
        verify_sources()
        available = memory_available()
        floor = args.link_memory_floor_mib * 1024**2 if label == "link-entry" else FLOOR
        rss_limit = args.link_rss_mib * 1024**2 if label == "link-entry" else RSS_LIMIT
        record = {"label": label, "command": [str(x) for x in command],
                  "cwd": str(output), "memAvailableBytes": available,
                  "memoryFloorBytes": floor, "rssLimitBytes": rss_limit,
                  "peakSampledAggregateRSSBytes": 0}
        receipt["processes"].append(record)
        save()
        if available < floor:
            record["blocked"] = "MemAvailable below required process floor"
            save()
            raise RuntimeError(record["blocked"])
        start = time.monotonic()
        with (output / (label + ".stdout")).open("wb") as out, (output / (label + ".stderr")).open("wb") as err:
            process = subprocess.Popen(record["command"], cwd=output, env=environment,
                                       stdout=out, stderr=err, preexec_fn=limits, start_new_session=True)
            while process.poll() is None:
                rss = group_rss(process.pid)
                record["peakSampledAggregateRSSBytes"] = max(record["peakSampledAggregateRSSBytes"], rss)
                if rss > rss_limit or time.monotonic() - start > 60:
                    record["terminated"] = "aggregate RSS limit" if rss > rss_limit else "wall timeout"
                    os.killpg(process.pid, signal.SIGKILL)
                    break
                time.sleep(0.05)
            record["exit"] = process.wait()
        record["elapsedSeconds"] = time.monotonic() - start
        for suffix in ("stdout", "stderr"):
            path = output / (label + "." + suffix)
            record[suffix] = {"path": path.name, "bytes": path.stat().st_size, "sha256": sha(path)}
        save()
        verify_sources()
        print(label, "exit", record["exit"], "peakRSSMiB",
              round(record["peakSampledAggregateRSSBytes"] / 1024**2, 1), flush=True)
        if record["exit"] != 0:
            raise RuntimeError(label + " failed; see bounded receipt logs")
        return (output / (label + ".stdout")).read_text().strip()

    try:
        lean = sysroot / "bin/lean"
        leanc = sysroot / "bin/leanc"
        if run("identity-commit", [lean, "--githash"]) != LEAN_COMMIT:
            raise RuntimeError("Official Lean commit mismatch")
        version = run("identity-version", [lean, "--version"])
        if "version 4.33.1" not in version:
            raise RuntimeError("Official Lean version mismatch")
        receipt["leanCommit"] = LEAN_COMMIT
        receipt["leanVersionOutput"] = version
        if not args.resume_link:
            for name in MODULES:
                command = [lean, "-M512", "-j1", "-o", name + ".olean"]
                if not args.compile_only and (args.standalone or name == "NativeEntryTransport"):
                    command += ["-c", name + ".c"]
                run("lean-" + name, command + [name + ".lean"])
            compiled = () if args.compile_only else MODULES if args.standalone else MODULES[:1]
            for name in compiled:
                run("cc-" + name, [leanc, "-v", "-c", "-fPIC", "-O0", "-g0", "-DLEAN_EXPORTING",
                                   name + ".c", "-o", name + ".o"])
        if args.standalone:
            # Compile-time deriving handlers must never initialize in the CLI.
            receipt["runtimeInitializerEdges"] = {}
            for name in MODULES:
                generated = (output / (name + ".c")).read_text()
                marker = "LEAN_EXPORT lean_object* runtime_initialize_" + name + "("
                body = generated.split(marker, 1)[1].split("\n}\n", 1)[0]
                edges = re.findall(r"res = (runtime_initialize_[A-Za-z0-9_]+)\(", body)
                receipt["runtimeInitializerEdges"][name] = edges
                if any("Lean_Elab_Deriving_" in edge for edge in edges):
                    raise RuntimeError("Deriving-handler runtime initializer edge remains")
                if name == "NativeNominalEntryEvidence" and not re.search(
                        r"res = runtime_initialize_NativeNominalEntryEvidence\(1 /\* builtin \*/\);", generated):
                    raise RuntimeError("Standalone main does not use runtime-only initialization")
            save()
            help_text = run("linker-help", [sysroot / "bin/ld.lld", "--help"])
            if "--threads=" not in help_text:
                raise RuntimeError("Bundled linker does not document --threads=")
            run("link-entry", [leanc, "-v", "-Wl,--threads=1", "-rdynamic",
                               *[name + ".o" for name in MODULES], "-o", "entry"])
        elif not args.compile_only:
            run("link-transport", [leanc, "-v", "-shared", "NativeEntryTransport.o", "-o", "NativeEntryTransport.so"])
        roles = (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir", ".c", ".o", ".so")
        receipt["products"] = [{"path": p.name, "bytes": p.stat().st_size, "sha256": sha(p)}
                               for p in sorted(output.iterdir())
                               if any(p.name == name + role for name in MODULES for role in roles) or p.name == "entry"]
        receipt["status"] = ("compiled-only-not-published" if args.compile_only else
                             "entry-built-not-published" if args.standalone else "transport-shared-built-not-published")
        save()
    except Exception as error:
        receipt["status"] = "blocked-or-failed"
        receipt["error"] = str(error)
        save()
        raise


if __name__ == "__main__":
    main()
