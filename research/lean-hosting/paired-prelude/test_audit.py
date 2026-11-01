"""Mutation tests against a real native pair (no synthetic replacement artifacts).
Run: PAIRED_PRELUDE_FIXTURE=/absolute/final-pair python3 -m unittest discover \
  -s experiments/lean-ir/paired-prelude -p 'test_*.py'
"""
import json
import os
from pathlib import Path
import tempfile
import unittest
from audit import audit


@unittest.skipUnless(os.environ.get('PAIRED_PRELUDE_FIXTURE'), 'requires genuine native pair fixture')
class PairAuditTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.stage = Path(self.temporary.name)
        self.fixture = Path(os.environ['PAIRED_PRELUDE_FIXTURE']).resolve()
        for source in self.fixture.iterdir():
            if source.is_file() and source.name != 'pair-audit.json':
                (self.stage / source.name).symlink_to(source)

    def mutate(self, name, change):
        path = self.stage / name
        data = json.loads(path.read_text())
        path.unlink()
        change(data)
        path.write_text(json.dumps(data))

    def reject(self, message):
        with self.assertRaisesRegex(ValueError, message):
            audit(self.stage)
        self.assertFalse((self.stage / 'pair-audit.json').exists())

    def test_genuine_complete_pair(self):
        receipt = audit(self.stage)
        self.assertEqual(2314, receipt['declarations'])
        self.assertEqual(481, receipt['typedScalarClaims'])
        self.assertEqual(134363, receipt['moduleDataRecords'])

    def test_changed_body_reference_rejected(self):
        def change(data):
            item = next(i for i in data['constants'] if 'value' in i['shape']['payload'])
            item['shape']['payload']['value'] += 1
        self.mutate('correspondence.json', change)
        self.reject('checking shape mismatch')

    def test_typed_name_change_rejected(self):
        self.mutate('correspondence.json', lambda d: d['constants'][0].update(typedName=['anonymous']))
        self.reject('typed Name mismatch')

    def test_display_collision_rejected(self):
        def change(data):
            data['constants'][1]['displayName'] = data['constants'][0]['displayName']
        self.mutate('correspondence.json', change)
        self.reject('display-key collision')

    def test_missing_scalar_claim_rejected(self):
        self.mutate('typed-scalars.json', lambda d: d['claims'].pop())
        self.reject('incomplete source-typed immediate coverage')

    def test_signed_scalar_domain_rejected(self):
        self.mutate('typed-scalars.json', lambda d: d['claims'][0].update(domain='Int'))
        self.reject('unsupported scalar claim')

    def test_wrong_scalar_value_rejected(self):
        self.mutate('typed-scalars.json', lambda d: d['claims'][0].update(value='0'))
        self.reject('incomplete source-typed immediate coverage')

    def test_duplicate_source_index_rejected(self):
        self.mutate('correspondence.json', lambda d: d['constants'][1].update(sourceCIIndex=0))
        self.reject('duplicate source CI index')


if __name__ == '__main__':
    unittest.main()
