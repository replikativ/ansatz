import hashlib,json,struct
from pathlib import Path
import argparse
parser=argparse.ArgumentParser(description="Recreate only the fixed prior-native-CAS research gate")
for option in ["catalogue","cas-root","metadata","census","output"]:
    parser.add_argument("--"+option,type=Path,required=True)
args=parser.parse_args()
catalogue=args.catalogue
cas=args.cas_root/"declarations"
assert (catalogue/"manifest.json").stat().st_size<=65536
manifest=json.loads((catalogue/"manifest.json").read_text())
census_path=args.census
assert census_path.stat().st_size<=65536
assert hashlib.sha256(census_path.read_bytes()).hexdigest()=="cd66682aed6c1b15c784969524389354f681b1af9faa46e4307769c30440e31a"
census=json.loads(census_path.read_text())
metadata_path=args.metadata
assert metadata_path.stat().st_size<=16777216
metadata_digest=hashlib.sha256()
with metadata_path.open("rb") as metadata_file:
    while chunk:=metadata_file.read(65536):metadata_digest.update(chunk)
assert metadata_digest.hexdigest()==census["metadataSHA256"]
def encoded(name):
    parts=[]
    while name != ["anonymous"]:
        assert isinstance(name,list) and len(name)==3 and len(parts)<256
        kind,name,leaf=name
        assert kind in ("str","num") and isinstance(leaf,str)
        b=leaf.encode("utf8")
        assert len(b)<=1048576
        parts.append(bytes([1 if kind=="str" else 2])+struct.pack(">I",len(b))+b)
    result=b"\0"+b"".join(reversed(parts))
    assert len(result)<=1048576
    return result

with (catalogue/'catalogue.dat').open('rb') as file:
    digest=hashlib.sha256()
    while chunk:=file.read(65536):digest.update(chunk)
    assert digest.hexdigest()==manifest['data-sha256']
    def lookup(name):
        wanted=hashlib.sha256(encoded(name)).digest();lo=0;hi=manifest['count']
        while lo<hi:
            mid=(lo+hi)//2;file.seek(mid*64);key=file.read(32)
            if key<wanted:lo=mid+1
            else:hi=mid
        for i in range(lo,min(manifest['count'],lo+8)):
            file.seek(i*64);record=file.read(64)
            if record[:32]!=wanted:break
            pin=record[32:].hex();path=cas/(pin+'.json');assert path.stat().st_size<=8388608
            
            with path.open('rb') as blob:raw=blob.read(8388609)
            assert len(raw)<=8388608
            assert hashlib.sha256(raw).hexdigest()==pin
            row=json.loads(raw)
            if row['name']==name:return pin,row
        raise AssertionError(('missing',name))
    assert hashlib.sha256((catalogue/'manifest.json').read_bytes()).hexdigest()=='644323f598096865c3a86be050e092bad9cf52dbecf23804584c7cfef3ca1048'
    assert manifest['source-index-sha256']=='74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e'
    action=census['rawOccurrences'][0]['initializer'];global_name=census['rawOccurrences'][0]['decl']
    error=['str',['str',['anonymous'],'IO'],'userError']
    entropy_boxed=['str',['str',['str',['anonymous'],'IO'],'getRandomBytes'],'_boxed']
    # Actual pinned CompilerM.mkBoxedName typed construction. This is a verified
    # catalogue candidate, NOT a native observed findInterpreterDeclBoxed result.
    action_boxed=['str',action,'_boxed']
    pending=[action,global_name,error,entropy_boxed,action_boxed]
    seen={};records=[];raw_rows=[];total=0;dynamic=0
    while pending:
        assert len(pending)<=32768 and len(records)<2048
        name=pending.pop();key=json.dumps(name)
        if key in seen:continue
        pin,row=lookup(name);
        with (cas/(pin+'.json')).open('rb') as blob:raw=blob.read(8388609)
        assert len(raw)<=8388608
        assert hashlib.sha256(raw).hexdigest()==pin
        total+=len(raw)+1;assert total<=16777216
        seen[key]=pin;records.append({'name':name,'sha256':pin,'bytes':len(raw)})
        raw_rows.append(raw);pending+=row['dependencies']
        work=[row['ir']]
        while work:
            node=work.pop()
            if isinstance(node,dict):
                dynamic+=int('ap' in node);work+=list(node.values())
            elif isinstance(node,list):work+=node
    output=args.output;output.mkdir(parents=True,exist_ok=True)
    stream=b'\n'.join(raw_rows)+b'\n';(output/'declarations.jsonl').write_bytes(stream)
    declaration_sha=hashlib.sha256(stream).hexdigest()
    receipt={'schema':'trusted-original-cas-startup-gate/1','scope':'research prior-native-capture bridge gate; not public artifact issuance',
        'leanCommit':'819816b2e0a3bf405af45ae5c7af2491d8f5bee6','catalogueManifestSHA256':'644323f598096865c3a86be050e092bad9cf52dbecf23804584c7cfef3ca1048',
        'catalogueDataSHA256':manifest['data-sha256'],'sourceIndexSHA256':manifest['source-index-sha256'],
        'sourceMetadataSHA256':census['metadataSHA256'],
        'censusSHA256':hashlib.sha256(census_path.read_bytes()).hexdigest(),
        'global':global_name,'rawInitializer':action,
        'executionRoute':'genuine raw owned void -> object action; global result tobject',
        'boxedInitializerCandidate':{'name':action_boxed,'rowSHA256':seen[json.dumps(action_boxed)],
            'selectionEvidence':'pinned typed mkBoxedName construction plus exact catalogue row presence, not observed native interpreter selection',
            'usedByRawInitializerRoute':False},'rows':records,'rowCount':len(records),'dynamicAPSites':dynamic,
        'declarations':{'file':'declarations.jsonl','bytes':len(stream),'sha256':declaration_sha},
        'bounds':{'unionBytes':16777216,'rowBytes':8388608,'rows':2048,'queuedDependencies':32768},
        'verification':'catalogue data hash streamed; every typed Name positional lookup and raw row SHA verified',
        'nativeOrJVMExecuted':False}
    (output/'manifest.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'rows':len(records),'bytes':len(stream),'streamSHA256':declaration_sha,
        'manifestSHA256':hashlib.sha256((output/'manifest.json').read_bytes()).hexdigest()}))
