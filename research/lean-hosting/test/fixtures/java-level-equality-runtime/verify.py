#!/usr/bin/env python3
"""Verify frozen Level equality evidence without executing Lean or Java."""
import argparse,hashlib,json,pathlib,subprocess
P=pathlib.Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
a=argparse.ArgumentParser();a.add_argument('--lean-repository');a.add_argument('--store');args=a.parse_args();m=json.loads((P/'provenance.json').read_text());assert sha((P/'original-rows.json').read_bytes())==m['fixture-sha256'];rs=json.loads((P/'original-rows.json').read_text());assert len(rs)==m['original-row-count']==2
for f,h in m['shared-fixtures'].items():assert sha((P/f).read_bytes())==h
raw=rs[0]['row']['ir']['extern'];boxed=rs[1]['row']['ir']['fdecl'];assert [p['ty']for p in raw['xs']]==['tobject','tobject']and[p['borrow']for p in raw['xs']]==[True,True]and raw['type']=='uint8';assert raw['ext']['entries'][0]['standard']['fn']=='lean_level_eq';assert [p['ty']for p in boxed['xs']]==['tobject','tobject']and[p['borrow']for p in boxed['xs']]==[False,False]and boxed['type']=='tagged';assert boxed['body'][3]['fap']['c']==rs[0]['row']['name'];assert boxed['body'][4][0]=='dec'and boxed['body'][4][5][0]=='dec'
if args.lean_repository:
 for f,h in m['upstream-source-sha256'].items():assert sha(subprocess.check_output(['git','-C',args.lean_repository,'show',m['lean-commit']+':'+f]))==h
if args.store:
 for rec in rs:
  b=(pathlib.Path(args.store)/'declarations'/(rec['sha256']+'.json')).read_bytes();assert sha(b)==rec['sha256'];r=json.loads(b);r.pop('pretty',None);assert r==rec['row']
print(json.dumps({'status':'verified','records':2,'new-native-execution':False,'source-verified':bool(args.lean_repository),'raw-CAS-verified':bool(args.store)}))
