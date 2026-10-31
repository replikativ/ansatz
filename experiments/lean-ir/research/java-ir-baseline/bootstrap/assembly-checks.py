#!/usr/bin/env python3
"""Synthetic metadata tests only; no real runtime bootstrap or JVM execution."""
import importlib.util, json, pathlib, tempfile, unittest, zipfile
from unittest.mock import patch
P = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("pack_assembler", P / "assemble-pack.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
class AssemblyChecks(unittest.TestCase):
    def setUp(self):
        parent = P.parents[5] / ".tmp"
        parent.mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="bootstrap-pack-model-", dir=parent)
        self.root = pathlib.Path(self.temp.name)
        self.inputs = self.root / "inputs"; self.inputs.mkdir()
        self.jar = self.inputs / "runtime.jar"
        with zipfile.ZipFile(self.jar, "w") as jar:
            jar.writestr("ansatz/research/ir/Interpreter.class", bytes.fromhex("cafebabe00000037"))
        (self.inputs / "runtime.java").write_text("synthetic source")
        (self.inputs / "dependency.json").write_text('{"basis":"synthetic model"}')
        (self.inputs / "unit.clj").write_text("(ns example.unit)\n")
        self.order = {"entry-namespaces": [], "definitions": [["unit.clj", "example.unit"]]}
        self.orderbytes = m.canonical(self.order)
        self.items = {}
        for name in ["runtime.jar", "runtime.java", "dependency.json", "unit.clj"]:
            data = (self.inputs / name).read_bytes()
            self.items[name] = {"root":"input","path":name,"output":name,"sha256":m.sha(data),"bytes":len(data)}
        self.plan = {"schema":"source4-pack-assembly/1", "profile":{"schema":"ansatz-source4-bootstrap/1","runtime":{"jar":"runtime.jar","source":"runtime.java","build-receipt":"build"},"directories":{}}, "inputs":self.items, "runtime-build-artifact":"build","dependency-artifacts":["dependency.json"],"definition-order-sha256":m.sha(self.orderbytes)}
        self.planfile = self.root / "plan.json"
    def tearDown(self): self.temp.cleanup()
    def run_plan(self, digest=None):
        data = m.canonical(self.plan); self.planfile.write_bytes(data)
        real = m.checked_bytes
        def checked(path, expected, cap):
            if path.name == "definition-order.json":
                m.need(expected == m.sha(self.orderbytes), "order digest")
                return self.orderbytes
            return real(path, expected, cap)
        with patch.object(m, "JAR", self.items["runtime.jar"]["sha256"]), patch.object(m, "JAVA", self.items["runtime.java"]["sha256"]), patch.object(m, "checked_bytes", checked):
            return m.assemble(self.planfile, digest or m.sha(data), self.root/"pack", {"input": self.inputs})
    def test_complete_selected_metadata_pack(self):
        result = self.run_plan()
        self.assertEqual(5, result["artifact-count"])
        self.assertEqual(1, result["definitions"])
        self.assertFalse(result["runtime-acceptance"])
        profile = json.loads((self.root/"pack/profile.json").read_text())
        self.assertEqual([["unit.clj","example.unit"]], profile["definitions"])
        receipt = json.loads((self.root/"pack/runtime-build.json").read_text())
        self.assertEqual(55, receipt["class-major"])
    def test_independent_plan_digest(self):
        with self.assertRaises(ValueError): self.run_plan("0"*64)
        self.assertFalse((self.root/"pack").exists())
    def test_changed_bytes_do_not_publish(self):
        (self.inputs/"unit.clj").write_text("(ns changed.unit)\n")
        with self.assertRaises(RuntimeError): self.run_plan()
        self.assertFalse((self.root/"pack").exists())
    def test_symlink_rejected(self):
        (self.inputs/"unit.clj").unlink()
        (self.inputs/"unit.clj").symlink_to(self.inputs/"runtime.java")
        with self.assertRaises(RuntimeError): self.run_plan()
    def test_directory_requires_complete_file_set(self):
        self.plan["profile"]["directories"]={"bad":{"root":"pack","path":"missing","files":["unit.clj"]}}
        with self.assertRaises(RuntimeError): self.run_plan()
    def test_definition_namespace_checked(self):
        self.order["definitions"][0][1]="other.unit"; self.orderbytes=m.canonical(self.order)
        self.plan["definition-order-sha256"]=m.sha(self.orderbytes)
        with self.assertRaises(RuntimeError): self.run_plan()
    def test_no_overwrite_or_path_escape(self):
        (self.root/"pack").mkdir()
        with self.assertRaises(ValueError): self.run_plan()
        for path in ["../escape", "/escape", "a//b", "a/./b", "a\\b"]:
            with self.assertRaises(ValueError): m.rel(path)
if __name__ == "__main__": unittest.main()
