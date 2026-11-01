#!/usr/bin/env python3
"""Root-executed serial native gate. Author must not invoke it without the slot.
Run under the existing whole-process-group RSS/floor/CPU/wall supervisor.
No JVM, Java initialization, entropy Java provider or guest ownership occurs.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
HELPER = "2693f971452aa28190ca5c1033bf2b1030f9703b22f53181cd0591b1ab90399c"
EXPORTER = "0b0344058631b8c3dc18a8a1a600f8100611eaf49c3b4ee5ad18a121651e736e"
OLD_MANIFEST = "5221a039d9a7b4770dfe3fa4d691412978f228ba146c77c70090c0b594fbf45c"
OLD_ROWS = "a56c4b244afe6e5fc52de241d26841fca67c2edbdf386892efd679acbb84c27c"
RAW_CENSUS = "de02e7643eb3e79be09152fcb0a6c4a56412124a054c008c9574c352729b3ec2"
INIT_OUTPUT = "f644f89c61f672569743eb11ad6874cb35028b3e4097554f4b96145b54e32ea0"


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()


def equal(a, b):
    return canonical(a) == canonical(b)


def key(name):
    return canonical(name).decode()


def name(*parts):
    value = ["anonymous"]
    for part in parts:
        value = ["str", value, part]
    return value


def imp(module, meta=False, exported=True, all_=False):
    return {"module": module, "isMeta": meta, "isExported": exported, "importAll": all_}


def record(path, limit=512 * 1024 * 1024):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), "regular non-symlink file required: " + str(path))
    before = path.stat()
    require(before.st_size <= limit, "file extent: " + str(path))
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    after = path.stat()
    require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) ==
            (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns), "file changed: " + str(path))
    return {"bytes": before.st_size, "sha256": digest.hexdigest()}


def read_json(path, limit=16 * 1024 * 1024):
    record(path, limit)
    return json.loads(Path(path).read_bytes())


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def pin(path, expected, limit=512 * 1024 * 1024):
    value = record(path, limit)
    require(value["sha256"] == expected, "independent pin mismatch: " + str(path))
    return value


def available():
    with open("/proc/meminfo", encoding="ascii") as source:
        for line in source:
            if line.startswith("MemAvailable:"):
                return int(line.split()[1])
    raise AssertionError("MemAvailable unavailable")


class Batch:
    def __init__(self, directory, env):
        self.directory, self.env, self.cases = directory, env, []

    def command(self, label, argv, cwd, expected_zero=True, check=None):
        stdout, stderr = self.directory / (label + ".stdout"), self.directory / (label + ".stderr")
        receipt = {"label": label, "command": [str(x) for x in argv], "cwd": str(cwd),
                   "stdoutFile": stdout.name, "stderrFile": stderr.name,
                   "status": "starting", "pid": None, "expectedZero": expected_zero}
        # Journaling precedes the actual native start. Children intentionally
        # inherit the root supervisor's process group; never create another SID.
        write(self.directory / (label + ".receipt.json"), receipt)
        start, child = time.monotonic(), None
        try:
            require(available() >= 2097152, "2GiB memory floor before native start")
            with stdout.open("xb") as out, stderr.open("xb") as err:
                child = subprocess.Popen([str(x) for x in argv], cwd=cwd, env=self.env,
                                         stdin=subprocess.DEVNULL, stdout=out, stderr=err)
                receipt["pid"] = child.pid
                write(self.directory / (label + ".receipt.json"), receipt)
                try:
                    while child.poll() is None:
                        require(time.monotonic() - start <= 30, "native command wall30s limit")
                        require(stdout.stat().st_size <= 16 * 1024 * 1024 and
                                stderr.stat().st_size <= 1024 * 1024, "native command output limit")
                        time.sleep(0.01)
                    code = child.returncode
                except BaseException:
                    if child.poll() is None:
                        child.kill()
                        child.wait(timeout=5)
                    raise
            receipt.update(exit=code, stdout=record(stdout, 16 * 1024 * 1024),
                           stderr=record(stderr, 1024 * 1024))
            require((code == 0) if expected_zero else (code > 0), "unexpected native exit/signal")
            if expected_zero:
                require(stderr.stat().st_size == 0, "unexpected native stderr")
            result = check(stdout, stderr) if check else {}
            receipt.update(status="PASS", checks=result)
        except (KeyboardInterrupt, SystemExit) as error:
            receipt.update(status="INTERRUPTED", errorClass=type(error).__name__)
            raise
        except Exception as error:
            # Independent semantic/compile failures remain separate. Root's
            # outer resource/cancellation stop kills the entire batch group.
            receipt.update(status="FAIL", errorClass=type(error).__name__, error=str(error)[:4096])
            for label_, path, cap in [("stdout", stdout, 16 * 1024 * 1024), ("stderr", stderr, 1024 * 1024)]:
                if path.exists():
                    try:
                        receipt[label_] = record(path, cap)
                    except Exception as extent:
                        receipt[label_] = {"refused": str(extent)[:512]}
        finally:
            receipt["elapsedSeconds"] = time.monotonic() - start
            write(self.directory / (label + ".receipt.json"), receipt)
            self.cases.append(receipt)
        return receipt

    def metadata(self, label, check):
        try:
            result = {"label": label, "status": "PASS", "checks": check()}
        except Exception as error:
            result = {"label": label, "status": "FAIL", "errorClass": type(error).__name__, "error": str(error)[:4096]}
        write(self.directory / (label + ".receipt.json"), result)
        self.cases.append(result)


def header_check(path, expected_module, prelude, explicit, invalid=False):
    def check(stdout, _stderr):
        data, raw = read_json(stdout), path.read_bytes()
        require(data["schema"] == "lean-project-header/2" and data["leanCommit"] == COMMIT, "header producer")
        require(data["leanVersion"] == "4.33.1" and data["lineEndingNormalization"] == "disabled", "header version/normalization")
        require(data["sourceUTF8Bytes"] == len(raw), "exact UTF8 extent")
        end = data["parserEndByte"]
        require(type(end) is int and 0 <= end <= len(raw), "raw parser position")
        raw[:end].decode("utf-8")
        if invalid:
            require(data["parserHasErrors"] is True and data["header"] is None and data["diagnostics"], "original parser error custody")
            if path.name == "header-crlf-unicode.lean":
                require(any(x.get("data") == "isolated carriage returns are not allowed" for x in data["diagnostics"]),
                        "original raw-CR diagnostic missing")
            return {"source": record(path), "parserEndByte": end, "sourceUTF8Bytes": len(raw),
                    "originalDiagnosticCount": len(data["diagnostics"]),
                    "originalDiagnostics": [{k: x.get(k) for k in ["severity", "data", "pos", "endPos"]} for x in data["diagnostics"]]}
        require(data["parserHasErrors"] is False, "unexpected original parse error")
        h = data["header"]
        prefix = [] if prelude else [imp(name("Init")), imp(name("Init"), meta=True)]
        require(h["isModule"] is expected_module and h["hasPrelude"] is prelude, "actual mode/prelude")
        require(equal(h["explicitImports"], explicit), "actual explicit import tuples")
        require(equal(h["insertedImportPrefix"], prefix), "actual implicit prefix")
        require(equal(h["requestedImports"], prefix + explicit), "original includeInit interpretation")
        spans = h["explicitImportSpans"]
        require(len(spans) == len(explicit), "explicit span count")
        texts = []
        for span in spans:
            a, b = span["startByte"], span["endByte"]
            require(type(a) is int and type(b) is int and 0 <= a < b <= len(raw), "actual source span")
            raw[:a].decode("utf-8")
            texts.append(raw[a:b].decode("utf-8"))
        return {"source": record(path), "parserEndByte": end, "sourceUTF8Bytes": len(raw),
                "explicitImports": explicit, "insertedImports": prefix, "actualSpanText": texts}
    return check


def validate_startup(data, request, expected_module):
    require(data["schema"] == "lean-native-startup-evidence/1" and data["leanCommit"] == COMMIT, "startup schema/commit")
    require(data["leanVersion"] == "4.33.1" and equal(data["request"], request), "startup version/request")
    require(equal(data["requestedImports"], request["requestedImports"]), "ordinary requested imports unchanged")
    h = data["actualHeader"]
    require(h["isModule"] is False and h["inServer"] is False and h["globalLevel"] == "private", "actual legacy profile")
    require(equal(h["imports"], request["requestedImports"]), "actual header import identity")
    require(data["javaInitializationExecuted"] is False and data["nativeImportMayExecuteInitializers"] is True, "effect boundary")
    require(data["additionalNativeAvailabilityProbePerformed"] is False and data["nativeImportInitializationStatusReceipt"] is None, "no fake init status")
    modules, actions, selected = data["modules"], data["selectedActions"], []
    require(1 <= len(modules) <= 4096, "module bound")
    require(equal(data["moduleOrder"], [x["effectiveImport"]["import"]["module"] for x in modules]), "actual ordered module identities")
    require(expected_module in data["moduleOrder"], "requested actual module absent")
    for i, module in enumerate(modules):
        require(module["index"] == i, "module index")
        regular, ir = module["regularModuleEntries"], module["regularIREntries"]
        sequence = regular + [pair for pair in ir if not any(equal(pair, old) for old in regular)]
        require(equal(sequence, module["regularSequence"]), "first-list/IR filtering differs from source")
        init_runtime = module["effectiveImport"]["irPhases"] != "runtime"
        require(module["initRuntime"] is init_runtime, "actual initRuntime")
        require(len(sequence) == len(module["phaseDecisions"]), "phase decision count")
        for ordinal, (pair, decision) in enumerate(zip(sequence, module["phaseDecisions"])):
            require(decision["ordinal"] == ordinal and equal(decision["pair"], pair), "decision provenance")
            # Original getIRPhases returns all when actual header.isModule=false.
            require(decision["declarationIRPhases"] == "all", "actual legacy declaration phase")
            chosen = init_runtime or decision["declarationIRPhases"] != "runtime"
            require(decision["selected"] is chosen, "source phase selection")
            if chosen:
                selected.append((i, ordinal, pair))
    require(len(selected) == len(actions), "selected action extent")
    for (index, ordinal, pair), action in zip(selected, actions):
        require(action["moduleIndex"] == index and action["sequenceOrdinal"] == ordinal and equal(action["pair"], pair), "action tuple/order")
        e = action["evidence"]
        proof = e["ioPayloadTypeProof"]
        require(proof["algorithm"] == "Lean.Meta.isDefEq" and proof["transparency"] == "default", "actual native type proof identity")
        require(equal(proof["actualType"], e["actionCI"]["type"]), "type proof actual CI coupling")
        payload = ["const", name("Unit"), []] if equal(pair[1], ["anonymous"]) else e["targetCI"]["type"]
        require(equal(proof["expectedType"], ["app", ["const", name("IO"), []], payload]), "actual expected IO payload type")
        if equal(pair[1], ["anonymous"]):
            require(e["kind"] == "anonymous-io-unit" and equal(e["actionCI"]["name"], pair[0]), "actual anonymous action")
        else:
            require(e["kind"] == "named-global" and equal(e["targetCI"]["name"], pair[0]) and equal(e["actionCI"]["name"], pair[1]), "actual named CI pair")
            require(e["actionRaw"]["type"] == "object" and equal(e["actionRaw"]["xs"], [{"borrow": False, "ty": "void", "x": {"idx": 1}}]), "raw World action ABI")
            require(e["globalRaw"]["xs"] == [] and e["globalRaw"]["type"] in ["object", "tobject"], "boxed global ABI")
    rows = data["declarations"]
    index = {key(r["name"]): r for r in rows}
    require(len(index) == len(rows), "duplicate exact declaration Name")
    for row in rows:
        require(row["sourceLocal"] is False, "imported row relabelled source-local")
        for dependency in row["dependencies"]:
            require(key(dependency) in index, "missing actual static dependency")
    require(data["dynamicClosureProven"] is False, "unsupported dynamic proof")
    return {"moduleCount": len(modules), "actionCount": len(actions), "rowCount": len(rows),
            "unsupportedReasons": data["unsupportedActivationReasons"], "dynamicAPSites": data["dynamicAPSites"]}


def compare_reference(args, data):
    old_manifest = read_json(args.old_manifest)
    pin(args.old_manifest, OLD_MANIFEST)
    pin(args.old_rows, OLD_ROWS)
    raw = args.old_rows.read_bytes()
    require(record(args.old_rows) == {k: old_manifest["declarations"][k] for k in ["bytes", "sha256"]},
            "old manifest's actual declaration file binding")
    old = {}
    entries = {key(x["name"]): x for x in old_manifest["rows"]}
    require(len(entries) == len(old_manifest["rows"]) == 63, "old manifest exact Name uniqueness")
    for line in raw.splitlines():
        row = json.loads(line)
        k = key(row["name"])
        require(k not in old, "duplicate old Name")
        require(hashlib.sha256(line).hexdigest() == entries[k]["sha256"] and len(line) == entries[k]["bytes"], "old actual raw row digest")
        old[k] = row
    require(len(old) == old_manifest["rowCount"] == 63, "old63 reference extent")
    pin(args.raw_census, RAW_CENSUS)
    census = read_json(args.raw_census)
    require(len(census["rows"]) == 60, "original raw60 census")
    new = {key(x["name"]): x for x in data["declarations"]}
    require(len(new) == 62 and set(new) <= set(old), "new62 covered by actual old reference")
    for item in census["rows"]:
        k = key(item["name"])
        require(k in new and entries[k]["sha256"] == item["sha256"], "original raw60 coverage/source digest")
    differences, mismatches, imported_closed_observations = [], [], []
    for k, row in new.items():
        previous = old[k]
        for field in ["kind", "name", "ir", "dependencies", "redirect"]:
            if not equal(row[field], previous[field]):
                mismatches.append({"name": row["name"], "field": field,
                                   "oldValueDigest": hashlib.sha256(canonical(previous[field])).hexdigest(),
                                   "newValueDigest": hashlib.sha256(canonical(row[field])).hexdigest()})
        for field in ["role", "initializer"]:
            if not equal(row["runtime"][field], previous["runtime"][field]):
                # ClosedTermCache is a non-persistent EnvExtension. The old
                # source-compilation observation is closed; the imported env's
                # actual fallback is value. Never infer this from a Name suffix
                # or rewrite either original record/hash to hide the difference.
                imported_fallback = (field == "role" and previous["runtime"][field] == "closed"
                                     and row["runtime"][field] == "value"
                                     and row["runtime"]["initializer"] is None
                                     and previous["runtime"]["initializer"] is None
                                     and "fdecl" in row["ir"] and row["ir"]["fdecl"]["xs"] == []
                                     and equal(row["ir"], previous["ir"]))
                if imported_fallback:
                    imported_closed_observations.append(row["name"])
                else:
                    mismatches.append({"name": row["name"], "field": "runtime." + field})
        if not equal(row["runtime"].get("initializationAction"), previous["runtime"].get("initializationAction")):
            mismatches.append({"name": row["name"], "field": "runtime.initializationAction"})
        if previous["sourceLocal"] is not True:
            mismatches.append({"name": row["name"], "field": "old.sourceLocal"})
        if previous["sourceModule"] is not None and not equal(previous["sourceModule"], row["sourceModule"]):
            mismatches.append({"name": row["name"], "field": "sourceModule"})
        changed = [field for field in ["sourceLocal", "sourceModule", "runtime", "pretty"] if not equal(previous.get(field), row.get(field))]
        if changed:
            differences.append({"name": row["name"], "allowedMetadataDifferences": changed})
    write(args.out / "reference-row-comparison.json", {"sharedCount": len(new),
          "mismatches": mismatches, "allowedMetadataDifferences": differences,
          "sourceClosedMarksUnavailableAfterImport": imported_closed_observations})
    require(not mismatches, "common-name semantic mismatches; see reference-row-comparison.json")
    require(len(imported_closed_observations) == 15, "unexpected closed-cache observation frontier")
    remaining = [row for k, row in old.items() if k not in new]
    require(len(remaining) == 1 and any(equal(n, name("IO", "getRandomBytes")) for n in remaining[0]["dependencies"]), "unexpected old-only reference row")
    aux = next(x for x in data["auxiliaryRoots"] if equal(x["name"], name("IO", "userError")))
    user = new[key(aux["name"])]
    require(aux["typeProof"]["algorithm"] == "Lean.Meta.isDefEq", "auxiliary native proof")
    require(entries[key(aux["name"])]["sha256"] == "53b224c8fa037b144260872e3b14878aff86dbb61b598e1ea49f991dabc1fb6b", "independent old userError witness")
    return {"commonNames": len(new), "originalRaw60Covered": True,
            "exactIRABIAndOccurrenceDependenciesEqual": True,
            "sourceVsImportedRoleObservationsIdentical": False,
            "sourceClosedMarksUnavailableAfterImport": imported_closed_observations,
            "roleScope": "old source compilation versus actual imported nonpersistent caches; not native-C startup parity",
            "allowedMetadataDifferences": differences,
            "oldOnlyActualName": remaining[0]["name"],
            "oldUserErrorWitnessSHA256": entries[key(aux["name"])]["sha256"],
            "newUserErrorRowCanonicalComparisonDigest": hashlib.sha256(canonical(user)).hexdigest(),
            "canonicalComparisonDigestIsOriginalHeaderHash": False}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--sysroot", type=Path, required=True)
    parser.add_argument("--helper", type=Path, required=True)
    parser.add_argument("--exporter", type=Path, required=True)
    parser.add_argument("--old-manifest", type=Path, required=True)
    parser.add_argument("--old-rows", type=Path, required=True)
    parser.add_argument("--raw-census", type=Path, required=True)
    parser.add_argument("--init-output", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    for label, path in vars(args).items():
        setattr(args, label, path.resolve(strict=label != "out"))
    repo = args.repository
    fixtures = repo / "research/lean-hosting/test/fixtures/native-startup-evidence"
    args.out.mkdir(parents=False, exist_ok=False)
    capsule, build = args.out / "source", args.out / "build"
    capsule.mkdir(); build.mkdir()
    tools = {"helper": pin(args.helper, HELPER), "exporter": pin(args.exporter, EXPORTER),
             "lean": record(args.sysroot / "bin/lean"), "script": record(__file__)}
    for source in fixtures.glob("*"):
        if source.is_file():
            shutil.copyfile(source, capsule / source.name)
            require(record(source) == record(capsule / source.name), "immutable fixture capture")
    (capsule / "header-module-all.lean").write_bytes(b"module\nprelude\nimport all Init.Prelude\n")
    # A SEPARATE explicitly derived fixture, never normalization of the actual
    # CRLF input sent to the native raw-header mode.
    (capsule / "header-lf-unicode.lean").write_bytes((capsule / "header-crlf-unicode.lean").read_bytes().replace(b"\r\n", b"\n"))
    env = dict(os.environ, LEAN_NUM_THREADS="1", MALLOC_ARENA_MAX="1", LEAN_SYSROOT=str(args.sysroot),
               LEAN_PATH=str(build) + ":" + str(args.sysroot / "lib/lean"))
    batch = Batch(args.out, env)
    batch.command("identity-commit", [args.sysroot / "bin/lean", "--githash"], capsule,
                  check=lambda out, err: require(out.read_text().strip() == COMMIT, "installed compiler reports another commit"))
    cases = [
        ("ordinary", False, False, [imp(name("Init", "Data", "Nat", "Basic"))], False),
        ("prelude", False, True, [imp(name("Init", "Prelude"))], False),
        ("explicit-meta", True, True, [imp(name("Init", "Prelude"), meta=True, exported=False)], False),
        ("module", True, False, [imp(name("Init"))], False),
        ("invalid-meta", None, None, [], True),
        ("invalid-all-public", None, None, [], True),
        ("crlf-unicode", None, None, [], True),
        ("lf-unicode", False, False, [imp(name("Init", "Data", "Nat", "Basic"))], False),
        ("quoted-name", False, True, [imp(name("A.B"))], False),
        ("module-all", True, True, [imp(name("Init", "Prelude"), exported=False, all_=True)], False),
    ]
    for label, module, prelude, imports, invalid in cases:
        path = capsule / ("header-" + label + ".lean")
        batch.command("header-" + label, [args.helper, "--header", path], capsule,
                      check=header_check(path, module, prelude, imports, invalid))
    for module in ["StartupNamed", "StartupAnonymous", "StartupBuiltin", "StartupPhase"]:
        olean = build / (module + ".olean")
        def local_check(out, _err, module=module, olean=olean):
            lines = out.read_bytes().splitlines()
            manifest, rows = json.loads(lines[0]), [json.loads(x) for x in lines[1:]]
            require(manifest["leanVersion"] == "4.33.1", "local compiler version")
            require(equal(manifest["initializationPlan"]["module"], name(module)), "local actual module identity")
            require(all(r["sourceLocal"] is True and equal(r["sourceModule"], name(module)) for r in rows), "local provenance")
            return {"olean": record(olean), "actualLocalInitializationPlan": manifest["initializationPlan"], "rowCount": len(rows)}
        compile_result = batch.command("compile-" + module,
            [args.exporter, "--source", capsule / (module + ".lean"), "--olean", olean, "--local", module],
            capsule, check=local_check)
        if compile_result["status"] != "PASS":
            blocked = {"label": "startup-" + module, "status": "BLOCKED", "reason": "actual compile gate failed"}
            write(args.out / ("startup-" + module + ".receipt.json"), blocked)
            batch.cases.append(blocked)
            continue
        request_path = capsule / (module + "-request.json")
        def startup_check(out, _err, module=module, request_path=request_path):
            data = read_json(out)
            result = validate_startup(data, read_json(request_path), name(module))
            reasons = [x["reason"] for x in data["unsupportedActivationReasons"]]
            module_index = data["moduleOrder"].index(name(module))
            own = data["modules"][module_index]
            own_actions = [x for x in data["selectedActions"] if x["moduleIndex"] == module_index]
            if module == "StartupAnonymous":
                require("anonymous-regular-activation-not-supported-in-v1" in reasons, "anonymous activation not refused")
                require(len(own_actions) == 1 and own_actions[0]["evidence"]["kind"] == "anonymous-io-unit",
                        "missing genuine local anonymous action")
            elif module == "StartupBuiltin":
                require("builtin-initialization-obligations-not-supported-in-v1" in reasons, "builtin activation not refused")
                builtin = own["builtinModuleEntries"] + own["builtinIREntries"]
                require(any(equal(x[0], name("builtinRef")) for x in builtin), "missing genuine local builtin tuple")
                require(not own_actions, "builtin action was appended to regular loop")
            else:
                require(not reasons, "unexpected unsupported named/phase profile")
                expected = [name("numberRef")] if module == "StartupNamed" else [name("runtimeRef"), name("compileRef")]
                require(len(own_actions) == len(expected) and
                        {key(x["pair"][0]) for x in own_actions} == {key(x) for x in expected},
                        "missing actual local named/phase initializer")
            result["localSelectedActions"] = len(own_actions)
            result["localRawRegularOccurrences"] = len(own["regularModuleEntries"]) + len(own["regularIREntries"])
            result["localRawBuiltinOccurrences"] = len(own["builtinModuleEntries"]) + len(own["builtinIREntries"])
            return result
        batch.command("startup-" + module, [args.helper, "--startup", request_path], capsule, check=startup_check)
    for filename, message in [
        ("invalid-meta-request.json", "requires nonanonymous ordinary legacy"),
        ("invalid-profile-request.json", "unsupported startup request schema/profile"),
        ("invalid-numeric-module-request.json", "module Name cannot have a numeric component")]:
        def bad_check(out, err, message=message):
            text = out.read_text() + err.read_text()
            require(message in text, "did not observe actual pre-import request rejection")
            return {"actualPreImportDiagnostic": message}
        batch.command(filename[:-5], [args.helper, "--startup", capsule / filename], capsule,
                      expected_zero=False, check=bad_check)
    def init_metadata():
        pin(args.init_output, INIT_OUTPUT)
        data = read_json(args.init_output)
        result = validate_startup(data, read_json(capsule / "Init-request.json"), name("Init"))
        require(result["moduleCount"] == 631 and result["actionCount"] == 1 and result["rowCount"] == 62, "actual pinned Init inventory")
        require(not result["unsupportedReasons"] and result["dynamicAPSites"] == 0, "actual Init unsupported/dynamic frontier")
        require(equal(data["selectedActions"][0]["pair"][0], name("IO", "stdGenRef")), "actual Init global")
        return result | {"referenceComparison": compare_reference(args, data)}
    batch.metadata("init-existing-output-and-old-reference", init_metadata)
    batch.metadata("final-native-tool-pins", lambda: {
        "helper": pin(args.helper, HELPER), "exporter": pin(args.exporter, EXPORTER)})
    report = {"schema": "native-startup-fixture-gates/1", "tools": tools,
              "nativeImportMayExecuteInitializers": True, "JavaInitializationExecuted": False,
              "cases": batch.cases, "pass": sum(x["status"] == "PASS" for x in batch.cases),
              "fail": sum(x["status"] != "PASS" for x in batch.cases)}
    write(args.out / "report.json", report)
    print(json.dumps({"report": str(args.out / "report.json"), "pass": report["pass"], "fail": report["fail"]}))
    raise SystemExit(1 if report["fail"] else 0)


if __name__ == "__main__":
    main()
