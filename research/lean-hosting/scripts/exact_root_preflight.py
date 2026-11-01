"""DRAFT exact-root preflight harness. Runs only a captured Lean evidence helper.

No exporter, generator, kernel replay, artifact activation or promotion is invoked.
Expected hashes come from the caller's captured input inventory, not this program.
Run this entire process group under the campaign's external memory guards.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

REQUEST_PROFILE = "ansatz-exact-root-request/1"
EVIDENCE_PROFILE = "ansatz-exact-root-evidence/1"
LEAN = {"version": "4.33.1", "githash": "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"}
ROLES = ("init", "lex", "sizeof")
MAX_BYTES = 16777216
MAX_ROOTS = 100000
MAX_SEGMENTS = 1024
REASONS = {"option-like-root", "nul-root", "invalid-name-syntax", "decoded-name-mismatch", "missing-exact-root"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(payload):
    return hashlib.sha256(payload).hexdigest()


def strict_json(payload):
    def pairs(entries):
        result = {}
        for key, value in entries:
            require(key not in result, "Duplicate JSON key")
            result[key] = value
        return result
    return json.loads(payload.decode("utf-8", errors="strict"), object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError("Invalid JSON constant")))


def integer(value, bound):
    return type(value) is int and 0 <= value <= bound


def hex_text(value):
    require(isinstance(value, str), "Expected exact string")
    return value.encode("utf-8", errors="strict").hex()


def encode_request(requests):
    """Strict, deterministic framing; never reconstruct names from display text."""
    require(isinstance(requests, list) and 1 <= len(requests) <= 3, "Expected one to three roles")
    lines = [REQUEST_PROFILE, str(len(requests))]
    previous = -1
    total = 0
    for request in requests:
        require(isinstance(request, dict) and set(request) == {"role", "iteration", "roots"}, "Wrong role fields")
        role, iteration, roots = request["role"], request["iteration"], request["roots"]
        require(role in ROLES and ROLES.index(role) > previous, "Unknown, duplicate or unordered role")
        previous = ROLES.index(role)
        require(integer(iteration, 1000000), "Invalid iteration")
        require(isinstance(roots, list) and len(roots) > 0, "Empty root vector")
        total += len(roots)
        require(total <= MAX_ROOTS, "Too many requested roots")
        lines.append(f"{role}\t{iteration}\t{len(roots)}")
        texts, identities = set(), set()
        for root in roots:
            require(isinstance(root, dict) and set(root) == {"text", "name"}, "Wrong root fields")
            text, name = root["text"], root["name"]
            require(isinstance(text, str) and text != "", "Empty native text")
            # Reject before invoking any native process; native helper repeats this gate.
            require(not text.startswith("--") and "\0" not in text, "Option-like or NUL root text")
            require(isinstance(name, list) and 1 <= len(name) <= MAX_SEGMENTS, "Invalid segment count")
            encoded = [hex_text(text), str(len(name))]
            identity = []
            for segment in name:
                require(isinstance(segment, list) and len(segment) == 2, "Wrong Name segment shape")
                tag, value = segment
                if tag == "str":
                    encoded.append("s:" + hex_text(value))
                elif tag == "num":
                    require(isinstance(value, str) and value.isascii() and value.isdecimal()
                            and (value == "0" or not value.startswith("0")), "Noncanonical numeric Name")
                    require(len(value) <= 19 and int(value) <= 9223372036854775807, "Unsupported numeric Name")
                    encoded.append("n:" + value)
                else:
                    raise ValueError("Unknown Name segment tag")
                identity.append((tag, value))
            identity = tuple(identity)
            require(text not in texts and identity not in identities, "Duplicate root text/identity within role")
            texts.add(text)
            identities.add(identity)
            lines.append("\t".join(encoded))
    payload = ("\n".join(lines) + "\n").encode("ascii")
    require(len(payload) <= MAX_BYTES, "Request byte bound exceeded")
    return payload


def validate_response(payload, requests, request_bytes, exit_code):
    require(len(payload) <= 65536 and payload.endswith(b"\n") and payload.count(b"\n") == 1,
            "Unexpected native evidence framing/size")
    evidence = strict_json(payload)
    require(isinstance(evidence, dict) and set(evidence) ==
            {"profile", "lean", "requestBytes", "checked", "rejected", "roles", "failures"}, "Wrong evidence fields")
    require(evidence["profile"] == EVIDENCE_PROFILE and evidence["lean"] == LEAN, "Wrong native evidence producer")
    total = sum(len(request["roots"]) for request in requests)
    require(integer(evidence["requestBytes"], MAX_BYTES) and evidence["requestBytes"] == len(request_bytes),
            "Wrong request byte count")
    require(integer(evidence["checked"], MAX_ROOTS) and evidence["checked"] == total, "Wrong checked count")
    require(integer(evidence["rejected"], total), "Wrong rejected count")
    roles = evidence["roles"]
    require(isinstance(roles, list) and len(roles) == len(requests), "Wrong role evidence count")
    by_role = {}
    for request, row in zip(requests, roles):
        require(isinstance(row, dict) and set(row) == {"role", "iteration", "roots", "rejected"}, "Wrong role evidence fields")
        require(row["role"] == request["role"] and type(row["iteration"]) is int
                and row["iteration"] == request["iteration"] and type(row["roots"]) is int
                and row["roots"] == len(request["roots"]) and integer(row["rejected"], row["roots"]), "Role evidence mismatch")
        by_role[row["role"]] = row
    require(sum(row["rejected"] for row in roles) == evidence["rejected"], "Rejected role counts differ")
    failures = evidence["failures"]
    require(isinstance(failures, list) and len(failures) == min(64, evidence["rejected"]), "Wrong diagnostic count")
    previous = (-1, -1)
    sampled = {role: 0 for role in by_role}
    for failure in failures:
        require(isinstance(failure, dict) and set(failure) == {"role", "iteration", "root", "reason"}, "Wrong diagnostic fields")
        role = failure["role"]
        require(role in by_role and failure["reason"] in REASONS, "Unknown diagnostic role/reason")
        row = by_role[role]
        require(type(failure["iteration"]) is int and failure["iteration"] == row["iteration"]
                and integer(failure["root"], row["roots"] - 1), "Wrong diagnostic address")
        address = (ROLES.index(role), failure["root"])
        require(address > previous, "Duplicate or unordered diagnostic")
        previous = address
        sampled[role] += 1
    require(all(sampled[role] <= row["rejected"] for role, row in by_role.items()), "Diagnostic accounting mismatch")
    require(exit_code == (0 if evidence["rejected"] == 0 else 2), "Exit code/evidence mismatch")
    return evidence


def verify_file(path, expected):
    require(isinstance(expected, str) and len(expected) == 64 and all(c in "0123456789abcdef" for c in expected),
            "Invalid captured SHA256")
    require(path.is_file() and digest(path.read_bytes()) == expected, "Captured file hash mismatch: " + str(path))


def run_preflight(requests, *, lean_root, helper, lean_sha256, helper_sha256, output_dir, timeout_seconds=120):
    """One evidence helper, no shell/exporter. Output directory must not exist."""
    payload = encode_request(requests)
    lean_root, helper, output_dir = Path(lean_root).resolve(), Path(helper).resolve(), Path(output_dir).resolve()
    lean = lean_root / "bin/lean"
    verify_file(lean, lean_sha256)
    verify_file(helper, helper_sha256)
    require(integer(timeout_seconds, 3600) and timeout_seconds > 0, "Invalid timeout")
    output_dir.mkdir(parents=True, exist_ok=False)
    request_path = output_dir / "request.txt"
    request_path.write_bytes(payload)
    command = [str(lean), "--run", str(helper), str(request_path)]
    environment = dict(os.environ, LEAN_SYSROOT=str(lean_root), LEAN_PATH=str(lean_root / "lib/lean"),
                       PATH=str(lean_root / "bin") + os.pathsep + os.environ.get("PATH", ""))
    record = {"command": command, "request-sha256": digest(payload), "helper-sha256": helper_sha256,
              "lean-binary-sha256": lean_sha256, "sysroot": str(lean_root),
              "timeout-seconds": timeout_seconds, "exit-code": None, "accepted": False,
              "scope": "exact-native-root-preflight-only", "exporter-invoked": False}
    try:
        with (output_dir / "stdout.ndjson").open("wb") as stdout, (output_dir / "stderr.log").open("wb") as stderr:
            result = subprocess.run(command, cwd=output_dir, env=environment, stdout=stdout, stderr=stderr,
                                    timeout=timeout_seconds, check=False)
        record["exit-code"] = result.returncode
        verify_file(lean, lean_sha256)
        verify_file(helper, helper_sha256)
        require(request_path.read_bytes() == payload, "Request changed during native preflight")
        stdout_path = output_dir / "stdout.ndjson"
        require(stdout_path.stat().st_size <= 65536, "Native evidence exceeds output bound")
        evidence = validate_response(stdout_path.read_bytes(), requests, payload, result.returncode)
        record["evidence"] = evidence
        record["accepted"] = evidence["rejected"] == 0
        require(record["accepted"], "Exact native root preflight rejected requested roots")
        return record
    except Exception as error:
        record["failure"] = str(error)
        raise
    finally:
        (output_dir / "invocation.json").write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for argument in ["request-json", "lean-root", "helper", "lean-sha256", "helper-sha256", "output"]:
        parser.add_argument("--" + argument, required=True)
    parser.add_argument("--timeout-seconds", type=int, default=120)
    options = parser.parse_args()
    request_file = Path(options.request_json)
    require(request_file.stat().st_size <= MAX_BYTES, "JSON input exceeds bound")
    value = strict_json(request_file.read_bytes())
    require(isinstance(value, dict) and set(value) == {"requests"}, "Expected exact requests wrapper")
    run_preflight(value["requests"], lean_root=options.lean_root, helper=options.helper,
                  lean_sha256=options.lean_sha256, helper_sha256=options.helper_sha256,
                  output_dir=options.output, timeout_seconds=options.timeout_seconds)


if __name__ == "__main__":
    main()
