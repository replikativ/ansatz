#!/usr/bin/env python3
"""Read-only exact catalogue/CAS and pinned upstream source collection."""
import argparse,codecs,hashlib,json,pathlib,re,resource,sqlite3,subprocess,time
resource.setrlimit(resource.RLIMIT_AS,(256*1024*1024,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(90,95))
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
def typed_name(n):
 depth=0
 while True:
  assert isinstance(n,list)and n and depth<256
  if n[0]=='anonymous':assert len(n)==1;return
  assert len(n)==3 and n[0]in ['str','num']
  if n[0]=='str':assert isinstance(n[2],str)and len(n[2])<=4096
  else:assert (isinstance(n[2],str)or type(n[2])is int)and re.fullmatch('0|[1-9][0-9]*',str(n[2]))
  n=n[1];depth+=1
def byte_domain(n):
 while n[0]!='anonymous':
  if n[0]=='str'and n[2]=='ByteArray':return True
  n=n[1]
 return False
def named(text):
 n=['anonymous']
 for part in text.split('.'):n=['str',n,part]
 return key(n)
conversion_names={named(text)for text in ['String.toByteArray','String.toUTF8','String.ofByteArray']}
class Stream:
 def __init__(self,f):
  self.f=f;self.buffer='';self.pos=0;self.eof=False;self.hash=hashlib.sha256();self.bytes=0
  self.decoder=codecs.getincrementaldecoder('utf-8')();self.json=json.JSONDecoder()
 def fill(self):
  self.buffer=self.buffer[self.pos:];self.pos=0
  block=self.f.read(65536);self.bytes+=len(block);assert self.bytes<=160*1024*1024
  self.hash.update(block);self.eof=not block
  self.buffer+=self.decoder.decode(block,final=self.eof);assert len(self.buffer)<=16*1024*1024
 def char(self):
  while self.pos==len(self.buffer)and not self.eof:self.fill()
  return self.buffer[self.pos:self.pos+1]
 def take(self,c):assert self.char()==c;self.pos+=1
 def value(self):
  while True:
   try:value,end=self.json.raw_decode(self.buffer,self.pos);self.pos=end;return value
   except json.JSONDecodeError:
    if self.eof:raise
    self.fill()
# SQLite is only an accelerator/candidate cross-check. Authenticate the entire
# actual index byte stream, derive the complete typed ByteArray domain from it,
# and retain only that bounded domain plus the explicitly requested conversions.
accepted={};byte_pairs={};index_rows=0;started=time.monotonic()
index_path=S/'indexes'/(index+'.json')
with index_path.open('rb')as f:
 before=index_path.stat();stream=Stream(f);stream.fill();prefix='{"declarations":['
 assert stream.buffer.startswith(prefix);stream.pos=len(prefix)
 while stream.char()!=']':
  assert time.monotonic()-started<60
  n,h=stream.value();typed_name(n);assert isinstance(h,str)and re.fullmatch('[0-9a-f]{64}',h)
  index_rows+=1;assert index_rows<=500000
  if byte_domain(n)or key(n)in conversion_names:
   k=key(n);assert k not in accepted;accepted[k]=h;assert len(accepted)<=10000
   if byte_domain(n):byte_pairs[k]=h
  if stream.char()==',':stream.take(',')
  else:assert stream.char()==']'
 stream.take(']')
 while not stream.eof:stream.fill()
 suffix=stream.buffer[stream.pos:];assert suffix.startswith(',')
 tail=json.loads('{'+suffix[1:]);assert tail['schema']=='lean-ir-store/1'
 assert stream.hash.hexdigest()==index
 after=index_path.stat();assert (before.st_ino,before.st_size,before.st_mtime_ns)==(after.st_ino,after.st_size,after.st_mtime_ns)
assert conversion_names<=accepted.keys()
candidates={n:h for n,h in N.execute('select name,hash from names where name like ?',('%"ByteArray"%',))if byte_domain(json.loads(n))}
assert candidates==byte_pairs,'SQLite ByteArray candidate domain differs from actual authenticated index'
for n in conversion_names:assert N.execute('select hash from names where name=?',(n,)).fetchone()==(accepted[n],)
wanted={'ByteArray.emptyWithCapacity','ByteArray.emptyWithCapacity._boxed','ByteArray.empty._closed_0'};rows=[];inventory=[]
implemented={'lean_byte_array_mk','lean_byte_array_fget','lean_byte_array_size','lean_byte_array_push','lean_mk_empty_byte_array'}
for n,h in sorted(byte_pairs.items()):
 name=json.loads(n);l=label(name)
 if l in wanted:
  r=raw(n,h);r.pop('pretty',None);rows.append({'label':l,'sha256':h,'row':r})
 # Exact typed Name/hash pair came from the hashed original index; CAS is checked next.
 r=raw(n,h)
 if'extern'in r['ir']:
  d=r['ir']['extern'];symbols=[e.get('standard',{}).get('fn')for e in d['ext']['entries']if'standard'in e]
  inventory.append({'label':l,'name':name,'sha256':h,'symbols':symbols,'params':d['xs'],'result':d['type'],'byte-runtime-symbol-implemented-after-this-patch':all(s in implemented for s in symbols)})
conversions=[]
for text in ['String.toByteArray','String.toUTF8','String.ofByteArray']:
 name=['anonymous']
 for part in text.split('.'):name=['str',name,part]
 n=key(name);h=accepted[n]
 r=raw(n,h);d=r['ir']['extern']
 conversions.append({'label':text,'name':name,'sha256':h,'params':d['xs'],'result':d['type'],'extern':d['ext'],'implemented-by-this-patch':False})
(P/'string-conversion-frontier.json').write_text(json.dumps(conversions,ensure_ascii=False,indent=2)+'\n')
assert {r['label']for r in rows}==wanted
rows.sort(key=lambda r:r['label']);inventory.sort(key=lambda r:r['label'])
(P/'original-rows.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n');(P/'extern-inventory.json').write_text(json.dumps(inventory,ensure_ascii=False,indent=2)+'\n')
paths=['src/include/lean/lean.h','src/runtime/object.cpp','src/Init/Prelude.lean','src/Init/Data/ByteArray/Basic.lean','src/Init/Data/String/Basic.lean','src/Init/Data/String/Defs.lean']
sources={p:sha(subprocess.check_output(['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-C',str(a.lean_repository),'show',pin+':'+p]))for p in paths}
def edn(v):
 if isinstance(v,str):return json.dumps(v)
 if isinstance(v,dict):return '{'+'\n '.join(edn(k)+' '+edn(x)for k,x in v.items())+'}'
 if isinstance(v,int):return str(v)
 raise TypeError(v)
# Conventional keyword keys used by the existing focused test harness.
text='{:schema 1\n :lean-commit '+edn(pin)+'\n :source-index-sha256 '+edn(index)+'\n :source-index-bytes '+str(stream.bytes)+'\n :source-index-declarations '+str(index_rows)+'\n :byte-array-domain-index-entries '+str(len(byte_pairs))+'\n :source-index-authentication :same-stream-sha256-and-exact-typed-membership\n :sqlite-role :candidate-accelerator-only\n :fixture-sha256 '+edn(sha((P/'original-rows.json').read_bytes()))+'\n :extern-inventory-sha256 '+edn(sha((P/'extern-inventory.json').read_bytes()))+'\n :string-conversion-frontier-sha256 '+edn(sha((P/'string-conversion-frontier.json').read_bytes()))+'\n :original-row-count 3\n :upstream-source-sha256 '+edn(sources)+'\n :transformation {:remove-top-level-pretty true :original-bodies-unchanged true}}\n'
(P/'provenance.edn').write_text(text)
print(json.dumps({'index-bytes':stream.bytes,'index-declarations':index_rows,'index-derived-byte-domain':len(byte_pairs),'rows':3,'extern-inventory-rows':len(inventory),'upstream-source-files':len(sources),'fixture-sha256':sha((P/'original-rows.json').read_bytes())}))
