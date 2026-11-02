#!/usr/bin/env python3
"""Build a bounded, authenticated base-CAS lookup companion. No bodies are copied.

The input SQLite is only an acceleration aid: every source-index row is checked
against it in the same pass that authenticates the original index bytes.
"""
import argparse
import codecs
import hashlib
import json
import pathlib
import re
import resource
import signal
import sqlite3
import struct
import tempfile
import time

SCHEMA = 'java-ir-code-catalogue/1'
CODEC = 'lean-typed-name-prefix/1'
HEX = re.compile(r'[0-9a-f]{64}\Z')
NUM = re.compile(r'(?:0|[1-9][0-9]*)\Z')


def typed_name_bytes(name):
    segments = []
    current = name
    total = 1
    for _ in range(257):
        if not isinstance(current, list) or not current:
            raise ValueError('invalid typed Name')
        if current[0] == 'anonymous':
            if len(current) != 1:
                raise ValueError('invalid anonymous Name')
            break
        if len(segments) == 256 or len(current) != 3 or current[0] not in ('str', 'num'):
            raise ValueError('invalid Name segment/depth')
        kind, prefix, leaf = current
        if not isinstance(leaf, str) or (kind == 'num' and not NUM.fullmatch(leaf)):
            raise ValueError('Name leaves must be strings; num must be canonical decimal')
        encoded = leaf.encode('utf-8', errors='strict')
        if len(encoded) > 1024 * 1024:
            raise ValueError('Name leaf exceeds bound')
        total += 5 + len(encoded)
        if total > 1024 * 1024:
            raise ValueError('encoded Name exceeds bound')
        segments.append(bytes([1 if kind == 'str' else 2]) + struct.pack('>I', len(encoded)) + encoded)
        current = prefix
    else:
        raise ValueError('Name depth exceeds bound')
    result = b'\0' + b''.join(reversed(segments))
    if len(result) > 1024 * 1024:
        raise ValueError('encoded Name exceeds bound')
    return result


class Stream:
    def __init__(self, source):
        self.source, self.buffer, self.pos, self.eof = source, '', 0, False
        self.digest, self.total = hashlib.sha256(), 0
        self.decoder, self.json = codecs.getincrementaldecoder('utf-8')('strict'), json.JSONDecoder()

    def fill(self):
        self.buffer, self.pos = self.buffer[self.pos:], 0
        data = self.source.read(65536)
        self.total += len(data)
        if self.total > 160 * 1024 * 1024:
            raise ValueError('source index exceeds 160MiB bound')
        self.digest.update(data)
        self.eof = not data
        self.buffer += self.decoder.decode(data, final=self.eof)
        if len(self.buffer) > 16 * 1024 * 1024:
            raise ValueError('index item/suffix exceeds 16MiB bound')

    def char(self):
        while self.pos == len(self.buffer) and not self.eof:
            self.fill()
        return self.buffer[self.pos:self.pos + 1]

    def consume(self, char):
        if self.char() != char:
            raise ValueError('unexpected source-index syntax')
        self.pos += 1

    def value(self):
        while True:
            try:
                value, self.pos = self.json.raw_decode(self.buffer, self.pos)
                return value
            except json.JSONDecodeError:
                if self.eof:
                    raise
                self.fill()


def build(args):
    started = time.monotonic()
    pin = args.source_index_sha256
    if not HEX.fullmatch(pin):
        raise ValueError('invalid source index pin')
    destination = pathlib.Path(args.output)
    destination.mkdir(parents=True, exist_ok=True)
    if any(destination.iterdir()):
        raise ValueError('output directory must be empty')
    database = sqlite3.connect(pathlib.Path(args.names_db).resolve().as_uri() + '?mode=ro', uri=True)
    database.execute('PRAGMA cache_size=-2048')
    metadata_rows = database.execute('SELECT json FROM metadata').fetchall()
    if len(metadata_rows) != 1:
        raise ValueError('expected one verified SQLite metadata row')
    metadata = json.loads(metadata_rows[0][0])
    if metadata['index_sha256'] != pin:
        raise ValueError('SQLite source index pin mismatch')
    count = 0
    with tempfile.TemporaryDirectory(prefix='.build-', dir=destination) as temporary:
        sorter = sqlite3.connect(str(pathlib.Path(temporary) / 'records.sqlite3'))
        sorter.execute('PRAGMA cache_size=-4096')
        sorter.execute('PRAGMA temp_store=FILE')
        sorter.execute('PRAGMA journal_mode=OFF')
        sorter.execute('CREATE TABLE records(name TEXT PRIMARY KEY, digest BLOB NOT NULL, rowhash BLOB NOT NULL) WITHOUT ROWID')
        with (pathlib.Path(args.store_root) / 'indexes' / (pin + '.json')).open('rb') as source:
            stream = Stream(source)
            stream.fill()
            prefix = '{"declarations":['
            if not stream.buffer.startswith(prefix):
                raise ValueError('unsupported source-index envelope')
            stream.pos = len(prefix)
            while stream.char() != ']':
                pair = stream.value()
                if not isinstance(pair, list) or len(pair) != 2:
                    raise ValueError('invalid declaration index pair')
                name, rowhash = pair
                encoded = typed_name_bytes(name)
                if not isinstance(rowhash, str) or not HEX.fullmatch(rowhash):
                    raise ValueError('invalid original row SHA')
                key = json.dumps(name, ensure_ascii=False, separators=(',', ':'))
                row = database.execute('SELECT hash FROM names WHERE name=?', (key,)).fetchone()
                if row != (rowhash,):
                    raise ValueError('SQLite/source-index declaration mismatch')
                sorter.execute('INSERT INTO records VALUES (?,?,?)', (key, hashlib.sha256(encoded).digest(), bytes.fromhex(rowhash)))
                count += 1
                if count > 500000:
                    raise ValueError('500000 declaration bound exceeded')
                if stream.char() == ',':
                    stream.consume(',')
                    if stream.char() == ']':
                        raise ValueError('trailing declaration comma')
                elif stream.char() != ']':
                    raise ValueError('unexpected declaration separator')
            stream.consume(']')
            while not stream.eof:
                stream.fill()
            suffix = stream.buffer[stream.pos:]
            if not suffix.startswith(','):
                raise ValueError('invalid index suffix')
            tail = json.loads('{' + suffix[1:])
            if tail['schema'] != 'lean-ir-store/1' or stream.digest.hexdigest() != pin:
                raise ValueError('source-index schema/hash mismatch')
            if (count != metadata['declarations'] or stream.total != metadata['index_bytes']
                    or len(tail['manifests']) != metadata['manifests']
                    or count != database.execute('SELECT count(*) FROM names').fetchone()[0]):
                raise ValueError('SQLite/source-index coverage mismatch')
        sorter.commit()
        sorter.execute('CREATE INDEX ordered_records ON records(digest,rowhash)')
        data_hash = hashlib.sha256()
        data_path = destination / 'catalogue.dat'
        with data_path.open('xb') as output:
            for digest, rowhash in sorter.execute('SELECT digest,rowhash FROM records ORDER BY digest,rowhash'):
                record = digest + rowhash
                output.write(record)
                data_hash.update(record)
        sorter.close()
    database.close()
    manifest = {'schema': SCHEMA, 'name-codec': CODEC, 'source-index-sha256': pin,
                'data-file': 'catalogue.dat', 'data-sha256': data_hash.hexdigest(),
                'count': count, 'record-bytes': 64, 'sort': 'unsigned-name-sha256-then-row-sha256'}
    manifest_bytes = (json.dumps(manifest, sort_keys=True, separators=(',', ':')) + '\n').encode()
    (destination / 'manifest.json').write_bytes(manifest_bytes)
    result = dict(manifest, **{'manifest-sha256': hashlib.sha256(manifest_bytes).hexdigest(),
                             'data-bytes': count * 64, 'elapsed-seconds': round(time.monotonic() - started, 3)})
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for argument in ('store-root', 'source-index-sha256', 'names-db', 'output'):
        parser.add_argument('--' + argument, required=True)
    arguments = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS, (384 * 1024 * 1024,) * 2)
    resource.setrlimit(resource.RLIMIT_CPU, (120, 125))
    resource.setrlimit(resource.RLIMIT_FSIZE, (320 * 1024 * 1024,) * 2)
    signal.alarm(180)
    build(arguments)
