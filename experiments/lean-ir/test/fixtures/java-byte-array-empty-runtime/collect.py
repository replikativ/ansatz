#!/usr/bin/env python3
"""Read-only exact catalogue/CAS and pinned upstream source collection."""
import argparse,hashlib,json,pathlib,sqlite3,subprocess
A=argparse.ArgumentParser();A.add_argument('reviewed_root',type=pathlib.Path);A.add_argument('lean_repository',type=pathlib.Path);a=A.parse_args()
P=pathlib.Path(__file__).resolve().parent;R=a.reviewed_root
pin='819816b2e0a3bf405af45ae5c7af2491d8f5bee6';index='74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e'
conf=json.load(open(R/'target/full-init-artifact-cohort-v1/inputs-current-head.json'))['producer-store'];assert conf['index-sha256']==index
S=pathlib.Path(conf['root']);N=sqlite3.connect('file:'+str(R/'target/java-header-inventory-v1/names.sqlite3')+'?mode=ro',uri=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
key=lambda n:json.dumps(n,separators=(',',':'),ensure_ascii=False)
def label(n):return ''if n[0]=='anonymous'else(label(n[1])+'.'+str(n[2])).lstrip('.')
def raw(n,h):
 b=(S/'declarations'/(h+'.json')).read_bytes();assert len(b)<8*1024*1024 and sha(b)==h
 r=json.loads(b);assert key(r['name'])==n;return r
wanted={'ByteArray.emptyWithCapacity','ByteArray.emptyWithCapacity._boxed','ByteArray.empty._closed_0'};rows=[];inventory=[]
implemented={'lean_byte_array_mk','lean_byte_array_fget','lean_byte_array_size','lean_byte_array_push','lean_mk_empty_byte_array'}
for n,h in N.execute('select name,hash from names where name like ?',('%"ByteArray"%',)):
 name=json.loads(n);l=label(name)
 if l in wanted:
  r=raw(n,h);r.pop('pretty',None);rows.append({'label':l,'sha256':h,'row':r})
 # Catalogue data is authenticated individually; no cached coverage edge controls selection.
 r=raw(n,h)
 if'extern'in r['ir']:
  d=r['ir']['extern'];symbols=[e.get('standard',{}).get('fn')for e in d['ext']['entries']if'standard'in e]
  inventory.append({'label':l,'name':name,'sha256':h,'symbols':symbols,'params':d['xs'],'result':d['type'],'byte-runtime-symbol-implemented-after-this-patch':all(s in implemented for s in symbols)})
conversions=[]
for text in ['String.toByteArray','String.toUTF8','String.ofByteArray']:
 name=['anonymous']
 for part in text.split('.'):name=['str',name,part]
 n=key(name);hit=N.execute('select hash from names where name=?',(n,)).fetchone();assert hit
 r=raw(n,hit[0]);d=r['ir']['extern']
 conversions.append({'label':text,'name':name,'sha256':hit[0],'params':d['xs'],'result':d['type'],'extern':d['ext'],'implemented-by-this-patch':False})
(P/'string-conversion-frontier.json').write_text(json.dumps(conversions,ensure_ascii=False,indent=2)+'\n')
assert {r['label']for r in rows}==wanted
rows.sort(key=lambda r:r['label']);inventory.sort(key=lambda r:r['label'])
(P/'original-rows.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n');(P/'extern-inventory.json').write_text(json.dumps(inventory,ensure_ascii=False,indent=2)+'\n')
paths=['src/include/lean/lean.h','src/runtime/object.cpp','src/Init/Prelude.lean','src/Init/Data/ByteArray/Basic.lean','src/Init/Data/String/Basic.lean','src/Init/Data/String/Defs.lean']
sources={p:sha(subprocess.check_output(['git','-C',str(a.lean_repository),'show',pin+':'+p]))for p in paths}
def edn(v):
 if isinstance(v,str):return json.dumps(v)
 if isinstance(v,dict):return '{'+'\n '.join(edn(k)+' '+edn(x)for k,x in v.items())+'}'
 if isinstance(v,int):return str(v)
 raise TypeError(v)
# Conventional keyword keys used by the existing focused test harness.
text='{:schema 1\n :lean-commit '+edn(pin)+'\n :source-index-sha256 '+edn(index)+'\n :fixture-sha256 '+edn(sha((P/'original-rows.json').read_bytes()))+'\n :extern-inventory-sha256 '+edn(sha((P/'extern-inventory.json').read_bytes()))+'\n :string-conversion-frontier-sha256 '+edn(sha((P/'string-conversion-frontier.json').read_bytes()))+'\n :original-row-count 3\n :upstream-source-sha256 '+edn(sources)+'\n :transformation {:remove-top-level-pretty true :original-bodies-unchanged true}}\n'
(P/'provenance.edn').write_text(text)
print(json.dumps({'rows':3,'extern-inventory-rows':len(inventory),'upstream-source-files':len(sources),'fixture-sha256':sha((P/'original-rows.json').read_bytes())}))
