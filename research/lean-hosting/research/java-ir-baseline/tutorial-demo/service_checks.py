"""Metadata/cache/process models only; no Lean, Java or upstream code executed."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).parent
spec = importlib.util.spec_from_file_location('tutorial_service', HERE / 'service.py')
service = importlib.util.module_from_spec(spec)
spec.loader.exec_module(service)


class ServiceChecks(unittest.TestCase):
    def directory(self):
        temporary = tempfile.TemporaryDirectory(prefix='tutorial-service-check-')
        self.addCleanup(temporary.cleanup)
        return Path(temporary.name)

    def cache_fixture(self):
        directory = self.directory()
        (directory / 'payload').write_bytes(b'owned synthetic metadata')
        inputs = {'test-profile': 'owner-free'}
        manifest = {'schema': 'native-compiled-project/1', 'cacheKey': 'key', 'inputs': inputs,
                    'files': service.file_inventory(directory)}
        (directory / 'manifest.json').write_bytes(service.canonical(manifest))
        return directory, inputs

    def test_source_constants_match_portable_corpus(self):
        corpus = json.loads((HERE / 'corpus.json').read_text())
        prefix = 'leanprover/fp-lean/examples/first-lake/expected/'
        expected = {r['path'][len(prefix):]: r['sha256'] for r in corpus['selected']['sourceReceipts']
                    if r['path'].startswith(prefix)}
        self.assertEqual(expected, service.SOURCES)

    def test_source_copy_digest_and_symlink_guards(self):
        directory = self.directory()
        (directory / 'A.lean').write_bytes(b'our synthetic input')
        expected = {'A.lean': service.digest(b'our synthetic input')}
        with mock.patch.object(service, 'SOURCES', expected):
            self.assertEqual({'A.lean'}, set(service.source_inputs(directory)))
            (directory / 'A.lean').write_bytes(b'changed synthetic input')
            with self.assertRaisesRegex(ValueError, 'Unsupported or modified'):
                service.source_inputs(directory)
            (directory / 'A.lean').unlink()
            (directory / 'actual').write_bytes(b'our synthetic input')
            (directory / 'A.lean').symlink_to(directory / 'actual')
            with self.assertRaisesRegex(ValueError, 'non-symlink'):
                service.source_inputs(directory)

    def test_valid_hit_binds_actual_key_inputs_and_manifest_bytes(self):
        directory, inputs = self.cache_fixture()
        manifest, pin = service.validate_hit(directory, 'key', inputs)
        self.assertEqual('key', manifest['cacheKey'])
        self.assertEqual(service.digest((directory / 'manifest.json').read_bytes()), pin)
        for key, supplied in [('other-key', inputs), ('key', {'other': 'profile'})]:
            with self.assertRaisesRegex(ValueError, 'another compile profile'):
                service.validate_hit(directory, key, supplied)

    def test_cache_payload_mutation_and_extra_files_rejected(self):
        directory, inputs = self.cache_fixture()
        (directory / 'payload').write_bytes(b'altered synthetic metadata')
        with self.assertRaisesRegex(ValueError, 'file set/bytes changed'):
            service.validate_hit(directory, 'key', inputs)
        directory, inputs = self.cache_fixture()
        (directory / 'extra').write_bytes(b'unlisted')
        with self.assertRaisesRegex(ValueError, 'file set/bytes changed'):
            service.validate_hit(directory, 'key', inputs)

    def test_cache_symlink_or_missing_payload_rejected(self):
        directory, inputs = self.cache_fixture()
        (directory / 'payload').unlink()
        with self.assertRaisesRegex(ValueError, 'file set/bytes changed'):
            service.validate_hit(directory, 'key', inputs)
        (directory / 'payload').symlink_to(directory / 'manifest.json')
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            service.validate_hit(directory, 'key', inputs)

    def test_process_floor_rejects_before_spawn(self):
        directory = self.directory()
        with mock.patch.object(service, 'available_kib', return_value=1), mock.patch.object(service.subprocess, 'Popen') as spawn:
            with self.assertRaisesRegex(ValueError, 'floor'):
                service.run_process('never-started', [sys.executable], {}, directory, directory)
            spawn.assert_not_called()

    def test_shell_free_small_process_receipt_and_failure(self):
        directory = self.directory()
        with mock.patch.object(service, 'available_kib', return_value=4 * 1024 * 1024):
            receipt = service.run_process('tiny', [sys.executable, '-c', 'print("model")'], {}, directory, directory, False)
            self.assertEqual(0, receipt['exit'])
            self.assertEqual(b'model\n', (directory / receipt['stdout']).read_bytes())
            with self.assertRaisesRegex(ValueError, 'Native command failed'):
                service.run_process('bad', [sys.executable, '-c', 'raise SystemExit(3)'], {}, directory, directory, False)
            self.assertEqual(3, json.loads((directory / 'bad.receipt.json').read_text())['exit'])


if __name__ == '__main__':
    unittest.main()
