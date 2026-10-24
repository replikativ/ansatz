"""Deterministic uniform reservoir per frame kind; sizes counted without EDN decode."""
import argparse, collections, hashlib, heapq, json, pathlib, random, re, struct, time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('source', type=pathlib.Path)
parser.add_argument('output', type=pathlib.Path)
parser.add_argument('--seed', type=int, default=20261024)
parser.add_argument('--functions', type=int, default=256)
parser.add_argument('--heap', type=int, default=1024)
parser.add_argument('--globals', type=int, default=256)
parser.add_argument('--declarations', type=int, default=64)
parser.add_argument('--expected-sha256', default='26282492007e48f6ba06466f0dea2c203c62d918da5ca283aee2db30449e773f')
args = parser.parse_args()
source, output = args.source, args.output
output.mkdir(exist_ok=False)
seed = args.seed
rng = random.Random(seed)
limits = {'function':args.functions, 'heap':args.heap, 'global':args.globals, 'imported-declaration':args.declarations}
assert all(1 <= n <= 16384 for n in limits.values()), 'bounded sample counts required'
samples = collections.defaultdict(list)
counts = collections.Counter()
sizes = collections.Counter()
largest = collections.defaultdict(list)
sha = hashlib.sha256()
start = time.monotonic()
with source.open('rb') as f:
    while True:
        length_bytes = f.read(4)
        if not length_bytes: break
        assert len(length_bytes) == 4
        length, = struct.unpack('>I', length_bytes)
        assert 1 <= length <= 64 * 1024 * 1024
        offset = f.tell()
        data = f.read(length)
        assert len(data) == length
        sha.update(length_bytes); sha.update(data)
        match = re.match(rb'\[:([a-z-]+)\s', data[:80])
        assert match, data[:80]
        kind = match.group(1).decode()
        counts[kind] += 1; sizes[kind] += length
        if kind in limits:
            row_digest = hashlib.sha256(data).hexdigest()
            row = {'kind':kind, 'offset':offset, 'bytes':length, 'ordinal':counts[kind], 'sha256':row_digest}
            chosen = rng.randrange(counts[kind])
            if len(samples[kind]) < limits[kind]: samples[kind].append(row)
            elif chosen < limits[kind]: samples[kind][chosen] = row
            entry = (length,offset,counts[kind],row_digest)
            heapq.heappush(largest[kind], entry)
            if len(largest[kind]) > 8: heapq.heappop(largest[kind])
        if time.monotonic()-start > 120: raise RuntimeError('sample wall bound')
digest = sha.hexdigest()
assert digest == args.expected_sha256
with source.open('rb') as f:
    for kind, rows in samples.items():
        for label, selected in [('uniform', rows), ('largest', [dict(kind=kind,bytes=n,offset=o,ordinal=i,sha256=h) for n,o,i,h in sorted(largest[kind], reverse=True)])]:
            with (output / (kind+'-'+label+'.frames')).open('wb') as out:
                for row in selected:
                    f.seek(row['offset']); data=f.read(row['bytes'])
                    assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256'], 'sample source changed between passes'
                    out.write(struct.pack('>I',len(data)));out.write(data)
manifest = {'schema':'stratified-checkpoint-frame-sample/1','seed':seed,'sourceSHA256':digest,
            'counts':dict(counts),'encodedBytesByKind':dict(sizes),'uniformSampleCount':{k:len(v) for k,v in samples.items()},
            'uniformRows':dict(samples),'largestRows':dict(largest),'elapsedSeconds':time.monotonic()-start,
            'note':'Sample only, not restoration/admission authority. Uniform rows and largest rows analyzed separately; source fully hashed.'}
(output/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:manifest[k] for k in ['counts','encodedBytesByKind','uniformSampleCount','elapsedSeconds']}))
