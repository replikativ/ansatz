#!/usr/bin/env python3
"""Small stdlib tests; does not read a live store or start a JVM."""
import hashlib
import importlib.util
import json
import pathlib
import sqlite3
import tempfile
import types
import unittest

SCRIPT = pathlib.Path(__file__).resolve().parents[3] / 'tools/lean-producer/build-code-catalogue.py'
SPEC = importlib.util.spec_from_file_location('builder', SCRIPT)
builder = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(builder)


class CatalogueTest(unittest.TestCase):
    def test_codec(self):
        vectors = [(['anonymous'], '00'),
                   (['str', ['anonymous'], ''], '000100000000'),
                   (['num', ['anonymous'], '0'], '00020000000130'),
                   (['str', ['num', ['anonymous'], '12'], 'λ'], '00020000000231320100000002cebb')]
        for name, expected in vectors:
            self.assertEqual(expected, builder.typed_name_bytes(name).hex())
        for name in [[], ['anonymous', 0], ['num', ['anonymous'], 0],
                     ['num', ['anonymous'], '01'], ['num', ['anonymous'], '-1'],
                     ['str', ['anonymous'], '\ud800']]:
            with self.assertRaises((ValueError, UnicodeError)):
                builder.typed_name_bytes(name)
        self.assertNotEqual(builder.typed_name_bytes(['str', ['anonymous'], '1']),
                            builder.typed_name_bytes(['num', ['anonymous'], '1']))

    def test_build_coverage_and_pins(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / 'indexes').mkdir()
            entries = [[['str', ['anonymous'], 'a'], '11' * 32],
                       [['num', ['anonymous'], '3'], '22' * 32]]
            raw = json.dumps({'declarations': entries, 'manifests': [], 'schema': 'lean-ir-store/1'},
                             separators=(',', ':')).encode()
            pin = hashlib.sha256(raw).hexdigest()
            (root / 'indexes' / (pin + '.json')).write_bytes(raw)
            db_path = root / 'names.sqlite3'
            with sqlite3.connect(db_path) as db:
                db.execute('CREATE TABLE names(name TEXT PRIMARY KEY, hash TEXT NOT NULL)')
                db.execute('CREATE TABLE metadata(json TEXT NOT NULL)')
                for name, sha in entries:
                    db.execute('INSERT INTO names VALUES (?,?)', (json.dumps(name, separators=(',', ':')), sha))
                db.execute('INSERT INTO metadata VALUES (?)', (json.dumps({'index_sha256': pin,
                    'declarations': 2, 'index_bytes': len(raw), 'manifests': 0}),))
            args = types.SimpleNamespace(store_root=str(root), source_index_sha256=pin,
                                         names_db=str(db_path), output=str(root / 'out'))
            builder.build(args)
            records = (root / 'out/catalogue.dat').read_bytes()
            expected = sorted(hashlib.sha256(builder.typed_name_bytes(n)).digest() + bytes.fromhex(h)
                              for n, h in entries)
            self.assertEqual(b''.join(expected), records)
            with sqlite3.connect(db_path) as db:
                db.execute('UPDATE names SET hash=?', ('33' * 32,))
            args.output = str(root / 'bad')
            with self.assertRaisesRegex(ValueError, 'declaration mismatch'):
                builder.build(args)
            self.assertFalse((root / 'bad/manifest.json').exists())


if __name__ == '__main__':
    unittest.main()
