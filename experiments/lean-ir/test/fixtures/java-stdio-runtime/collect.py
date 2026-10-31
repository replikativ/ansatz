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
def named(text):
 n=['anonymous']
 for part in text.split('.'):n=['str',n,part]
 return key(n)
labels=[f'IO.{verb}Std{channel}{suffix}'for verb in ['get','set']for channel in ['in','out','err']for suffix in ['', '._boxed']]
labels+=['IO.FS.Stream.ofBuffer','IO.FS.Stream.ofBuffer._closed_0','IO.FS.instInhabitedStream.default._closed_5']
labels+=[f'IO.FS.Stream.ofBuffer._lam_{i}._boxed'for i in range(5)]
labels+=['IO.FS.instInhabitedStream.default._lam_5._boxed']
requested={named(text)for text in labels}
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
# actual index byte stream and retain only the bounded exact requested stdio
# and original Buffer-constructor/method Name/hash pairs.
accepted={};index_rows=0;started=time.monotonic()
index_path=S/'indexes'/(index+'.json')
with index_path.open('rb')as f:
 before=index_path.stat();stream=Stream(f);stream.fill();prefix='{"declarations":['
 assert stream.buffer.startswith(prefix);stream.pos=len(prefix)
 while stream.char()!=']':
  assert time.monotonic()-started<60
  n,h=stream.value();typed_name(n);assert isinstance(h,str)and re.fullmatch('[0-9a-f]{64}',h)
  index_rows+=1;assert index_rows<=500000
  if key(n)in requested:
   k=key(n);assert k not in accepted;accepted[k]=h;assert len(accepted)<=10000
  if stream.char()==',':stream.take(',')
  else:assert stream.char()==']'
 stream.take(']')
 while not stream.eof:stream.fill()
 suffix=stream.buffer[stream.pos:];assert suffix.startswith(',')
 tail=json.loads('{'+suffix[1:]);assert tail['schema']=='lean-ir-store/1'
 assert stream.hash.hexdigest()==index
 after=index_path.stat();assert (before.st_ino,before.st_size,before.st_mtime_ns)==(after.st_ino,after.st_size,after.st_mtime_ns)
assert set(accepted)==requested
# SQLite is checked only as an accelerator; actual membership came from hashed bytes.
for n,h in accepted.items():assert N.execute('select hash from names where name=?',(n,)).fetchone()==(h,)
rows=[]
for n,h in sorted(accepted.items()):
 r=raw(n,h);r.pop('pretty',None);rows.append({'label':label(r['name']),'sha256':h,'row':r})
rows.sort(key=lambda r:r['label'])
(P/'original-rows.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
paths=['src/runtime/io.cpp','src/runtime/thread.h','src/runtime/object.cpp','src/Init/System/IO.lean','src/Init/System/Promise.lean']
sources={p:sha(subprocess.check_output(['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-C',str(a.lean_repository),'show',pin+':'+p]))for p in paths}
receipt={'schema':'original-stdio-source-fixture/1','lean-commit':pin,'source-index-sha256':index,'source-index-bytes':stream.bytes,'source-index-declarations':index_rows,'selected-exact-typed-pairs':len(accepted),'index-authentication':'same-stream-sha256-and-membership','sqlite-role':'candidate-accelerator-only','fixture-sha256':sha((P/'original-rows.json').read_bytes()),'source-sha256':sources,'transformation':{'remove-top-level-pretty':True,'original-bodies-unchanged':True},'JVM-or-native-executed':False}
(P/'provenance.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
