#!/usr/bin/env python3
"""Fixture-authentication checks only; no guest/source capability is modeled."""
import importlib.util
import shutil
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).parent
spec = importlib.util.spec_from_file_location('policy_audit', HERE / 'verify-policy-data.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class PolicyDataChecks(unittest.TestCase):
    def fixture(self):
        temporary = tempfile.TemporaryDirectory(prefix='policy-data-')
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name) / 'policies'
        shutil.copytree(HERE / 'data/policies', root)
        return root

    def test_reviewed_inventory_preserves_complete_headers(self):
        result = audit.audit(HERE / 'data/policies')
        self.assertEqual((11, 28, 247, 225, 77), tuple(result[k] for k in
                         ['families', 'fixtureFiles', 'HeaderOccurrences', 'uniqueHeaderNames', 'upstreamSourceFiles']))
        self.assertFalse(result['JVMStarted'])
        self.assertFalse(result['runtimeOpened'])

    def test_changed_index_does_not_self_authorize(self):
        root = self.fixture()
        path = root / 'policy-index.json'
        path.write_bytes(path.read_bytes() + b' ')
        with self.assertRaisesRegex(ValueError, 'index pin'):
            audit.audit(root)

    def test_changed_abi_bytes_rejected(self):
        root = self.fixture()
        path = root / 'string/header-projections.json'
        original = path.read_bytes()
        changed = original.replace(b'"borrow": false', b'"borrow": true', 1)
        self.assertTrue(original != changed)
        path.write_bytes(changed)
        with self.assertRaisesRegex(ValueError, 'policy file'):
            audit.audit(root)

    def test_missing_fixture_rejected(self):
        root = self.fixture()
        (root / 'meta/header-projections.json').unlink()
        with self.assertRaisesRegex(ValueError, 'file set'):
            audit.audit(root)

    def test_undeclared_fixture_rejected(self):
        root = self.fixture()
        (root / 'finalizer/unreviewed.json').write_text('{}')
        with self.assertRaisesRegex(ValueError, 'file set'):
            audit.audit(root)

    def test_same_bytes_symlink_is_not_an_authenticated_leaf(self):
        root = self.fixture()
        path = root / 'level/manifest.json'
        saved = root / 'saved-manifest.json'
        path.rename(saved)
        path.symlink_to(saved)
        with self.assertRaisesRegex(ValueError, 'policy file'):
            audit.audit(root)


if __name__ == '__main__':
    unittest.main()
