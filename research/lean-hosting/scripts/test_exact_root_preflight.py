"""Pure protocol/harness tests; no native process or exporter is invoked."""
import copy
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import exact_root_preflight as preflight


def requests():
    return [{"role": "init", "iteration": 0,
             "roots": [{"text": "Nat.add", "name": [["str", "Nat"], ["str", "add"]]}]}]


def response(value, rejected=0, failures=None):
    return {"profile": preflight.EVIDENCE_PROFILE, "lean": preflight.LEAN,
            "requestBytes": len(preflight.encode_request(value)),
            "checked": sum(len(row["roots"]) for row in value), "rejected": rejected,
            "roles": [{"role": row["role"], "iteration": row["iteration"],
                       "roots": len(row["roots"]), "rejected": rejected if index == 0 else 0}
                      for index, row in enumerate(value)], "failures": failures or []}


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False) + "\n").encode("utf-8")


class ExactRootProtocolTest(unittest.TestCase):
    def test_deterministic_framing_and_structural_tags(self):
        self.assertEqual(preflight.encode_request(requests()),
                         b"ansatz-exact-root-request/1\n1\ninit\t0\t1\n4e61742e616464\t2\ts:4e6174\ts:616464\n")
        value = requests()
        value[0]["roots"] = [{"text": "«A.B»", "name": [["str", "A.B"]]},
                              {"text": "A.B", "name": [["str", "A"], ["str", "B"]]},
                              {"text": "«7»", "name": [["str", "7"]]},
                              {"text": "7", "name": [["num", "7"]]},
                              {"text": "«λ\n\t»", "name": [["str", "λ\n\t"]]}]
        payload = preflight.encode_request(value)
        self.assertEqual(payload.count(b"\n"), 8)
        self.assertIn(b"\ts:37\n", payload)
        self.assertIn(b"\tn:7\n", payload)
        self.assertIn("λ\n\t".encode().hex().encode(), payload)

    def test_input_shape_collision_option_and_unicode_fail_closed(self):
        base = requests()
        invalid = []
        for text in ["--", "--export-unsafe", "x\0y", "\ud800"]:
            value = copy.deepcopy(base)
            value[0]["roots"][0]["text"] = text
            invalid.append(value)
        for name in [[], [["num", "01"]], [["num", "9223372036854775808"]], [["num", 1]], [["wrong", "a"]]]:
            value = copy.deepcopy(base)
            value[0]["roots"][0]["name"] = name
            invalid.append(value)
        invalid += [base + base, [{**base[0], "extra": True}], [{**base[0], "iteration": True}]]
        for second in [base[0]["roots"][0], {"text": "another", "name": base[0]["roots"][0]["name"]},
                       {"text": "Nat.add", "name": [["str", "other"]]}]:
            invalid.append([{**base[0], "roots": base[0]["roots"] + [second]}])
        for value in invalid:
            with self.subTest(value=value), self.assertRaises((ValueError, UnicodeError)):
                preflight.encode_request(value)
        with self.assertRaises(ValueError):
            preflight.strict_json(b'{"requests":[],"requests":[]}')

    def test_response_framing_counts_and_rejection_are_reconciled(self):
        value = requests()
        payload = preflight.encode_request(value)
        good = response(value)
        self.assertEqual(preflight.validate_response(json_bytes(good), value, payload, 0), good)
        rejection = response(value, 1, [{"role": "init", "iteration": 0, "root": 0, "reason": "decoded-name-mismatch"}])
        self.assertEqual(preflight.validate_response(json_bytes(rejection), value, payload, 2), rejection)
        bad = [json_bytes(good) + b"\n", json_bytes(good)[:-1], b"\xc3\x28\n",
               json_bytes(good).replace(b'"checked": 1', b'"checked": 1, "checked": 1')]
        for field, change in [("checked", 2), ("checked", True), ("requestBytes", 1), ("rejected", 1),
                              ("roles", []), ("failures", [{}]), ("extra", None)]:
            bad.append(json_bytes({**good, field: change}))
        for broken in bad:
            with self.subTest(payload=broken), self.assertRaises((ValueError, UnicodeError)):
                preflight.validate_response(broken, value, payload, 0)
        with self.assertRaises(ValueError):
            preflight.validate_response(json_bytes(rejection), value, payload, 0)

    def test_harness_reuses_captured_paths_and_keeps_evidence(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            lean = root / "toolchain/bin/lean"
            lean.parent.mkdir(parents=True)
            lean.write_bytes(b"synthetic captured executable; never run")
            helper = root / "helper.lean"
            helper.write_bytes(b"synthetic helper; never compiled")
            value = requests()
            def fake_run(command, **options):
                self.assertEqual(command[:3], [str(lean), "--run", str(helper)])
                self.assertEqual(options["env"]["LEAN_SYSROOT"], str(root / "toolchain"))
                self.assertEqual(options["env"]["LEAN_PATH"], str(root / "toolchain/lib/lean"))
                self.assertEqual(Path(command[3]).read_bytes(), preflight.encode_request(value))
                options["stdout"].write(json_bytes(response(value)))
                return SimpleNamespace(returncode=0)
            with patch.object(preflight.subprocess, "run", side_effect=fake_run) as runner:
                record = preflight.run_preflight(value, lean_root=root / "toolchain", helper=helper,
                    lean_sha256=preflight.digest(lean.read_bytes()), helper_sha256=preflight.digest(helper.read_bytes()),
                    output_dir=root / "observation")
                self.assertEqual(runner.call_count, 1)
            self.assertTrue(record["accepted"])
            self.assertFalse(record["exporter-invoked"])
            self.assertTrue((root / "observation/invocation.json").is_file())
            with self.assertRaises(FileExistsError):
                preflight.run_preflight(value, lean_root=root / "toolchain", helper=helper,
                    lean_sha256=preflight.digest(lean.read_bytes()), helper_sha256=preflight.digest(helper.read_bytes()),
                    output_dir=root / "observation")


if __name__ == "__main__":
    unittest.main()
