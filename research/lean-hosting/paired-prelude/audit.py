#!/usr/bin/env python3
"""Bounded independent metadata gate. Does not open a JVM or hydrate Java CIs."""
import hashlib
import json
from pathlib import Path
import sys
from patch_exporter import UPSTREAM_SHA256, PATCHED_SHA256

MAX_BYTES = 64 * 1024 * 1024
MAX_RECORDS = 200000
KINDS = {'axiom', 'def', 'thm', 'opaque', 'quot'}


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def records(path):
    require(path.stat().st_size <= MAX_BYTES, 'artifact byte bound')
    with path.open() as f:
        for i, line in enumerate(f):
            require(i < MAX_RECORDS, 'record bound')
            yield json.loads(line)


def audit(directory):
    directory = Path(directory)
    source = json.loads((directory / 'correspondence.json').read_text())
    cohort = json.loads((directory / 'build-cohort.json').read_text())
    require(cohort.get('exporterCacheEquality') == 'Lean.ExprStructEq/Expr.equal', 'structural expression cache profile required')
    require(cohort.get('exporterUpstreamSha256') == UPSTREAM_SHA256 and
            cohort.get('exporterPatchedSha256') == PATCHED_SHA256, 'structural exporter source pins')
    require(source['schema'] == 'matched-prelude-source-correspondence/1', 'correspondence schema')
    require(source['bodyPolicy'] == 'full', 'full body evidence required')
    prelude = ['str', ['str', ['anonymous'], 'Init'], 'Prelude']
    require(source['source']['globalLevel'] == 'private', 'legacy source profile requires private global level')
    require(source['source']['requestedImports'] == [dict(module=prelude, importAll=False,
            isExported=True, isMeta=False)], 'source-expressible legacy import request required')
    require(len(source['source']['modules']) == 1 and
            source['source']['modules'][0]['effectiveImport'] == dict(module=prelude,
            importAll=True, isExported=False, isMeta=False), 'effective private Prelude profile')
    require(source['source']['leanCommit'] == '819816b2e0a3bf405af45ae5c7af2491d8f5bee6', 'source pin')
    transport = next(records(directory / 'module-data.jsonl'))
    # Native transport metadata lives under input in its graph manifest.
    require(transport['input'] == source['source'], 'transport and exporter import metadata differ')
    names = {0: ['anonymous']}
    declarations = {}
    expressions = {}
    levels = {0: None}
    def put(target, key, value):
        require(key not in target, f'duplicate index {key}')
        target[key] = value
    def add(kind, payload):
        n = payload['name']
        require(n not in declarations, 'duplicate CI record')
        declarations[n] = {'kind': kind, 'payload': payload}
    for record in records(directory / 'kernel.ndjson'):
        if 'meta' in record:
            require(record['meta']['lean']['githash'] == source['source']['leanCommit'], 'NDJSON Lean pin')
        elif 'in' in record:
            if 'str' in record:
                v = record['str']; put(names, record['in'], ['str', names[v['pre']], v['str']])
            else:
                v = record['num']; put(names, record['in'], ['num', names[v['pre']], str(v['i'])])
        elif 'il' in record:
            put(levels, record['il'], record)
        elif 'ie' in record:
            put(expressions, record['ie'], record)
        elif 'inductive' in record:
            block = record['inductive']
            for key, kind in [('types', 'inductive'), ('ctors', 'ctor'), ('recs', 'rec')]:
                for payload in block[key]: add(kind, payload)
        else:
            require(len(record) == 1 and next(iter(record)) in KINDS, 'unknown record')
            kind, payload = next(iter(record.items())); add(kind, payload)
    require(len(declarations) == len(source['constants']) == 2314, 'complete private domain count')
    typed = set(); display = set(); indices = set()
    for item in source['constants']:
        shape = item['shape']; n = shape['payload']['name']
        require(item['sourcePartRoot'] == 2, 'source part must be private root 2')
        require(item['sourceCIIndex'] not in indices, 'duplicate source CI index')
        indices.add(item['sourceCIIndex'])
        require(names[n] == item['typedName'], 'typed Name mismatch')
        require(declarations.get(n) == shape, 'complete source checking shape mismatch')
        encoded = json.dumps(item['typedName'], separators=(',', ':'))
        require(encoded not in typed, 'typed Name duplicate'); typed.add(encoded)
        require(item['displayName'] not in display, 'display-key collision'); display.add(item['displayName'])
    require(indices == set(range(2314)), 'source CI inventory is not complete')
    # All expression constant dependencies, including proof and recursor-rule bodies.
    # DAG index closure is checked without recursively expanding shared expressions.
    expr_fields = {'app': ('fn', 'arg'), 'lam': ('type', 'body'),
                   'forallE': ('type', 'body'), 'letE': ('type', 'value', 'body'),
                   'mdata': ('expr',), 'proj': ('struct',)}
    for record in expressions.values():
        for kind, fields in expr_fields.items():
            if kind in record:
                for field in fields:
                    require(record[kind][field] in expressions, 'unresolved expression DAG index')
        if 'sort' in record: require(record['sort'] in levels, 'unresolved sort level')
        if 'const' in record:
            for level in record['const']['us']: require(level in levels, 'unresolved universe level')
        if 'const' in record:
            require(record['const']['name'] in declarations, 'unresolved constant dependency')
    for shape in declarations.values():
        p = shape['payload']; kind = shape['kind']
        require(p['type'] in expressions, 'missing declaration type')
        if 'value' in p: require(p['value'] in expressions, 'missing full declaration body')
        for level in p['levelParams']: require(level in names, 'missing universe parameter Name')
        for name in p.get('all', []): require(name in declarations, 'missing family member')
        if kind == 'inductive':
            for c in p['ctors']:
                require(declarations[c]['kind'] == 'ctor' and declarations[c]['payload']['induct'] == p['name'], 'incomplete constructor family')
        if kind == 'ctor':
            parent = declarations[p['induct']]
            require(parent['kind'] == 'inductive' and p['name'] in parent['payload']['ctors'], 'orphan constructor')
        if kind == 'rec':
            for ind in p['all']: require(declarations[ind]['kind'] == 'inductive', 'recursor family kind')
            for rule in p['rules']:
                require(rule['rhs'] in expressions, 'missing recursor rule body')
                require(declarations[rule['ctor']]['kind'] == 'ctor', 'recursor rule constructor kind')
    quot = [names[n] for n, s in declarations.items() if s['kind'] == 'quot']
    require(len(quot) == 4 and source['quotInit'], 'quotient inventory')
    scalar = json.loads((directory / 'typed-scalars.json').read_text())
    require(scalar['schema'] == 'matched-prelude-typed-scalars/1', 'typed scalar schema')
    require(scalar['graphNodes'] == transport['inventory']['nodes'], 'scalar census graph identity')
    claims = {}
    for c in scalar['claims']:
        key = (c['nodeId'], c['fieldIndex'])
        require(key not in claims and c['domain'] == 'Nat', 'duplicate or unsupported scalar claim')
        require(c['sourceType'] in {'Lean.Name.num', 'Lean.Literal.natVal', 'Lean.IR.LitVal.num'}, 'unsupported source scalar domain')
        claims[key] = c['value']
    actual = {}
    reference_count = immediate_count = node_count = 0
    for node in records(directory / 'module-data.jsonl'):
        if node.get('kind') == 'manifest': continue
        node_count += 1
        for i, edge in enumerate(node.get('fields', [])):
            if 'ref' in edge: reference_count += 1
            if 'immediate' in edge:
                immediate_count += 1
                if int(edge['immediate']) > 2147483647:
                    actual[(node['id'], i)] = edge['immediate']
    require(actual == claims and len(claims) == scalar['claimCount'], 'incomplete source-typed immediate coverage')
    root = transport['root']
    reference_count += int('ref' in root)
    immediate_count += int('immediate' in root)
    require(node_count == transport['inventory']['nodes'], 'transport record count')
    require(reference_count == transport['inventory']['referenceOccurrences'], 'transport reference census')
    require(immediate_count == transport['inventory']['immediateOccurrences'], 'transport immediate census')
    files = ['module-data.jsonl', 'kernel.ndjson', 'correspondence.json', 'transport-receipt.json', 'build-cohort.json', 'typed-scalars.json', 'module-file-cohort.json']
    receipt = {'schema': 'matched-prelude-pair-audit/1', 'declarations': len(declarations),
        'typedScalarClaims': len(claims), 'sourceReferenceOccurrences': reference_count,
        'sourceImmediateOccurrences': immediate_count,
        'names': len(names), 'levels': len(levels), 'expressions': len(expressions),
        'moduleDataRecords': transport['inventory']['nodes'],
        'sourceCIIndicesComplete': True, 'checkingShapesEqual': True, 'structuralExprKeys': True,
        'sourceHeaderProfile': 'legacy-prelude-explicit-Init.Prelude/1',
        'typedNameCollisionFree': True, 'displayKeyCollisionFree': True,
        'dependencyClosure': True, 'familyClosure': True, 'fullBodies': True,
        'quotInit': True, 'baseBasis': 'trusted-artifact', 'proofReplay': False,
        'guestFinalizationAccepted': False, 'generatedIRAuthorized': False,
        'files': {name: {'sha256': digest(directory / name), 'bytes': (directory / name).stat().st_size} for name in files}}
    (directory / 'pair-audit.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    return receipt

if __name__ == '__main__':
    print(json.dumps(audit(sys.argv[1]), sort_keys=True))
