#!/usr/bin/env python3
"""Host-only metadata/path regressions. No JVM, native process or old code load."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("pack_materializer", Path(__file__).with_name("materialize-pack.py"))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class PackMetadataTests(unittest.TestCase):
    def test_producer_edn_roundtrip_preserves_keyword_and_string_roles(self):
        value = m.EDN('{:factory-id "source-bound" :kernel-policy {:allow-unsafe? true} :roots [["str" ["anonymous"] "I"]] :count 0}').read()
        self.assertEqual(value, m.EDN(m.edn(value)).read())
        self.assertIsInstance(next(iter(value)), m.Keyword)
        self.assertNotIsInstance(value[m.key("factory-id")], m.Keyword)

    def test_tag_is_opaque_and_code_reader_syntax_is_refused(self):
        value = m.EDN('{:root #prototype.machine.Ref {:id 9}}').read()
        self.assertIsInstance(value[m.key("root")], m.Tagged)
        self.assertEqual(9, value[m.key("root")].value[m.key("id")])
        for text in ['#=(System/exit 0)', '#other.Tag {}', '{:a 1 :a 2}', '[1] [2]']:
            with self.assertRaises(m.Reject):
                m.EDN(text).read()

    def test_depth_is_rejected_before_python_recursion_exhaustion(self):
        with self.assertRaisesRegex(m.Reject, "depth/work"):
            m.EDN('[' * 130 + '0' + ']' * 130).read()

    def test_duplicate_json_metadata_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / 'metadata.json'
            p.write_text('{"sha256":"original","sha256":"replacement"}')
            with self.assertRaisesRegex(m.Reject, "duplicate JSON"):
                m.read_json(p)

    def test_hash_mismatch_cannot_become_a_captured_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp); source = base / 'input'; source.write_bytes(b'actual')
            pack = m.Pack(base / 'pack')
            with self.assertRaisesRegex(m.Reject, "digest mismatch"):
                pack.add('producer/input', source, '0' * 64)
            self.assertEqual(b'actual', source.read_bytes())
            self.assertFalse((base / 'pack/inputs/producer/input').exists())

    def test_symlink_inputs_and_output_ancestors_are_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp); source = base / 'input'; source.write_bytes(b'input')
            alias = base / 'alias'; alias.symlink_to(source)
            with self.assertRaises(m.Reject):
                m.file_pin({'path': str(alias), 'sha256': m.digest(source)})
            parent = base / 'parent'; parent.mkdir()
            linked = base / 'linked'; linked.symlink_to(parent, target_is_directory=True)
            with self.assertRaisesRegex(m.Reject, "symlink ancestor"):
                m.Pack(linked / 'output')
            self.assertFalse((parent / 'output').exists())

    def test_destination_traversal_cannot_escape_pack(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp); source = base / 'input'; source.write_bytes(b'input')
            pack = m.Pack(base / 'pack')
            with self.assertRaisesRegex(m.Reject, "relative identity"):
                pack.add('producer/input', source, m.digest(source), '../escape')
            self.assertFalse((base / 'escape').exists())

    def test_typed_names_cannot_collide_through_dotted_display(self):
        normal = ['str', ['str', ['anonymous'], 'SourceModuleImport'], 'mkOwnedPart']
        flat = ['str', ['anonymous'], 'SourceModuleImport.mkOwnedPart']
        self.assertEqual(m.expected_name('SourceModuleImport.mkOwnedPart'), m.name_key(normal))
        self.assertNotEqual(m.name_key(normal), m.name_key(flat))
        numeric = ['num', ['str', ['anonymous'], 'Module'], '0']
        string = ['str', ['str', ['anonymous'], 'Module'], '0']
        self.assertNotEqual(m.name_key(numeric), m.name_key(string))
        self.assertEqual(m.name_key(numeric), m.name_key(['num', ['str', ['anonymous'], 'Module'], 0]))
        for invalid in ['00', '-1', True]:
            with self.assertRaises(m.Reject):
                m.name_key(['num', ['str', ['anonymous'], 'Module'], invalid])
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / 'helper.jsonl'
            p.write_text(json.dumps({'initializationPlan': {'actions': []}}) + '\n' + json.dumps({'name': flat}) + '\n')
            self.assertNotIn(m.expected_name('SourceModuleImport.mkOwnedPart'), m.helper_roots(p, 'graph'))

    def test_only_exact_known_pure_value_action_is_allowed(self):
        constant = ['str', ['str', ['str', ['anonymous'], 'SourceModuleImport'], 'finalizeClassic'], '_boxed_const_1']
        action = {'action': {'kind': 'value', 'name': constant, 'target': constant}, 'meta': False}
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / 'helper.jsonl'
            def write(actions):
                p.write_text(json.dumps({'initializationPlan': {'actions': actions}}) + '\n' + json.dumps({'name': constant}) + '\n')
            write([action])
            self.assertIn(m.expected_name('SourceModuleImport.finalizeClassic._boxed_const_1'), m.helper_roots(p, 'import'))
            with self.assertRaises(m.Reject):
                m.helper_roots(p, 'graph')
            write([dict(action, meta=True)])
            with self.assertRaises(m.Reject):
                m.helper_roots(p, 'old-import')
            write([])
            with self.assertRaises(m.Reject):
                m.helper_roots(p, 'import')


if __name__ == '__main__':
    unittest.main()
