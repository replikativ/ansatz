#!/usr/bin/env python3
"""Independent metadata/source-pin audit; no JVM, catalogue or runtime opening."""
import argparse,hashlib,json,subprocess
from pathlib import Path

PIN='819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
INDEX='9a31d3ebfe00bd2ae7ad71cb78cc50db86d1817d8444b54b2edb9e7ac26112c8'
def digest(b):return hashlib.sha256(b).hexdigest()
def require(ok,message):
    if not ok:raise ValueError(message)
def audit(directory,repository=None):
    directory=Path(directory);raw=(directory/'policy-index.json').read_bytes()
    require(digest(raw)==INDEX,'reviewed policy index pin')
    index=json.loads(raw);require(index['leanCommit']==PIN,'Lean source pin')
    require(len(index['families'])==11 and len(index['sourceFiles'])==77,'complete policy family/source inventory')
    records={};record_count=files=0
    for family,spec in index['families'].items():
        root=directory/family
        require({p.name for p in root.iterdir()}==set(spec['files']),'exact policy file set '+family)
        parsed={}
        for name,evidence in spec['files'].items():
            p=root/name;data=p.read_bytes();files+=1
            require(not p.is_symlink() and len(data)==evidence['bytes'] and digest(data)==evidence['sha256'],'policy file '+str(p))
            parsed[name]=json.loads(data)
        headers=parsed.get('header-projections.json',[])
        if 'manifest.json'in parsed:
            manifest=parsed['manifest.json']
            require(manifest['schema']==spec['schema'] and manifest['lean-commit']==PIN,'policy schema/source')
            require(spec['headerCount']==len(headers)==manifest['header-record-count'],'header count')
        for record in headers:
            record_count+=1;row=record['header-row'];kind,decl=next(iter(row['ir'].items()))
            require(len(row['ir'])==1 and kind in ['fdecl','extern'] and 'body'not in decl,'complete bodyless Header')
            require(row['name']==decl['f'],'typed declaration Name')
            require(all(type(x['borrow'])is bool and type(x['ty'])is str for x in decl['xs']),'raw typed/borrow ABI')
            require(len(record['sha256'])==64,'original SHA')
            key=json.dumps(row['name'],separators=(',',':'))
            if key in records:require(records[key]==record['sha256'],'cross-family Name/SHA collision')
            records[key]=record['sha256']
    if repository:
        for path,expected in index['sourceFiles'].items():
            data=subprocess.check_output(['git','-C',str(repository),'show',f'{PIN}:{path}'])
            require(digest(data)==expected,'pinned source blob '+path)
    return {'scope':'policy-metadata-source-audit','families':len(index['families']),'fixtureFiles':files,
            'HeaderOccurrences':record_count,'uniqueHeaderNames':len(records),'upstreamSourceFiles':len(index['sourceFiles']),
            'sourceBlobsChecked':bool(repository),'indexSHA256':INDEX,'JVMStarted':False,'runtimeOpened':False}
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--directory',type=Path,default=Path(__file__).parent/'data/policies');p.add_argument('--lean-repository',type=Path)
    a=p.parse_args();print(json.dumps(audit(a.directory,a.lean_repository),indent=2))
