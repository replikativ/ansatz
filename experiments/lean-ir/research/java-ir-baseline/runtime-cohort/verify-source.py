#!/usr/bin/env python3
"""Portable source/fixture audit only; no JVM, guest, store or source issuance."""
import hashlib, json, pathlib, re
P = pathlib.Path(__file__).resolve().parent
manifest = json.loads((P / 'manifest.json').read_text())
sources = json.loads((P / 'sources.json').read_text())
sha = lambda data: hashlib.sha256(data).hexdigest()
assert manifest['schema'] == 'runtime-cohort-package/1'
files = {str(p.relative_to(P)) for p in P.rglob('*') if p.is_file() and p.name != 'manifest.json'}
# The external audit fixture has its own historical manifest which IS payload.
files.add('data/externs/manifest.json')
assert set(manifest['files']) == files
for name, info in manifest['files'].items():
    p = P / name
    assert p.stat().st_size == info['bytes'], name
    assert sha(p.read_bytes()) == info['sha256'], name
    if p.name != 'verify-source.py' and p.suffix in {'.clj', '.md', '.json', '.jsonl', '.py'}:
        text = p.read_text()
        assert not re.search(r'/home/|/Users/|[A-Za-z]:\\Users\\', text), name
    if p.suffix == '.clj':
        stack, quoted, escaped, comment = [], False, False, False
        for c in p.read_text():
            if comment:
                if c == '\n': comment = False
            elif quoted:
                if escaped: escaped = False
                elif c == '\\': escaped = True
                elif c == '"': quoted = False
            elif c == ';': comment = True
            elif c == '"': quoted = True
            elif c in '([{': stack.append(c)
            elif c in ')]}': assert stack and stack.pop() == '([{'[')]}'.index(c)], name
        assert not stack and not quoted, name
for item in sources['files']:
    actual = manifest['files'][item['file']]['sha256']
    assert bool(item['changes']) == (actual != item['origin_sha256']), item['file']
# No silent addition/removal of code/model files outside explicit loader lists.
loader = (P / 'loader.clj').read_text()
units = re.findall(r'\["([^"]+\.clj)" ([^\]\s]+)\]', loader)
assert len(units) == 17
for path, namespace in units:
    assert re.search(r'\(ns\s+' + re.escape(namespace) + r'(?:\s|\))', (P/path).read_text()), path
assert {path for path, _ in units} | {'loader.clj', 'check-models.clj'} == {p for p in files if p.endswith('.clj')}
external = json.loads((P / 'data/externs/manifest.json').read_text())
assert sha((P/'data/externs/manifest.json').read_bytes()) == '225d3d9e506730ffa4f6a6319ca91e6d52b46145cd6058422748b93424b5fd11'
assert sha((P/'data/externs/extern-rows.jsonl').read_bytes()) == external['extern-rows-sha256']
rows = [json.loads(line) for line in (P/'data/externs/extern-rows.jsonl').read_text().splitlines()]
assert len(rows) == 961 == external['extern-row-count']
assert len({json.dumps(r['name'], separators=(',', ':')) for r in rows}) == 961
assert all(r['row']['kind'] == 'decl' and r['row']['name'] == r['name'] == r['row']['ir']['extern']['f'] for r in rows)
assert all(set(r['row']['ir']) == {'extern'} and re.fullmatch('[0-9a-f]{64}', r['sha256']) for r in rows)
origin_collector = next(x for x in sources['files'] if x['file'] == 'data/externs/collect.py')
assert external['collector-sha256'] == origin_collector['origin_sha256']
limits = json.loads((P/'data/limits/source-receipt.json').read_text())
for label, digest in limits['original-rows'].items():
    assert sha((P/'data/limits'/f'{label}.json').read_bytes()) == digest, label
runner = (P/'check-models.clj').read_text()
assert 'System/exit' in runner and 'run-tests' in runner and 'smoke!' not in runner
assert 'check-models.clj' not in loader
assert 'allocation-heartbeat-lab-v1' in loader and 'Namespace already loaded' in loader
print(json.dumps({'files': len(files), 'source-origins': len(sources['files']),
                  'ordered-definition-units': 9, 'model-units': 7, 'explicit-runtime-model-units': 1,
                  'extern-fixture-rows': 961, 'machine-paths': 0,
                  'JVM-or-guest-executed': False}))
