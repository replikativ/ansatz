#!/usr/bin/env python3
"""Complete original-index/CAS extern metadata scan. No JVM/guest/handler authority."""
import argparse,codecs,hashlib,json,pathlib,re,resource,signal,sys,time
resource.setrlimit(resource.RLIMIT_AS,(256*1024*1024,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(300,305));signal.alarm(420)
P=pathlib.Path(__file__).resolve().parent
A=argparse.ArgumentParser();A.add_argument('cas_root',type=pathlib.Path);A.add_argument('--output',type=pathlib.Path,default=P);a=A.parse_args();P=a.output.resolve();P.mkdir(parents=True,exist_ok=True)
PIN='74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e'
S=a.cas_root.resolve();sha=lambda b:hashlib.sha256(b).hexdigest();key=lambda v:json.dumps(v,ensure_ascii=False,separators=(',',':'))
D=json.JSONDecoder()
def typed_name(n):
 depth=0
 while True:
  assert isinstance(n,list)and n and depth<256
  if n[0]=='anonymous':assert len(n)==1;return
  assert len(n)==3 and n[0]in ['str','num']
  if n[0]=='str':assert isinstance(n[2],str)and len(n[2])<=1048576
  else:assert (isinstance(n[2],str)or type(n[2])is int)and re.fullmatch('0|[1-9][0-9]*',str(n[2]))
  n=n[1];depth+=1
class Stream:
 def __init__(self,f):self.f=f;self.s='';self.p=0;self.eof=False;self.h=hashlib.sha256();self.bytes=0;self.decoder=codecs.getincrementaldecoder('utf8')()
 def fill(self):
  self.s=self.s[self.p:];self.p=0;b=self.f.read(65536);self.bytes+=len(b);assert self.bytes<=160*1024*1024
  self.h.update(b);self.eof=not b;self.s+=self.decoder.decode(b,final=self.eof);assert len(self.s)<=16*1024*1024
 def char(self):
  while self.p==len(self.s)and not self.eof:self.fill()
  return self.s[self.p:self.p+1]
 def take(self,c):assert self.char()==c;self.p+=1
 def value(self):
  while True:
   try:v,end=D.raw_decode(self.s,self.p);self.p=end;return v
   except json.JSONDecodeError:
    if self.eof:raise
    self.fill()
def ws(s,p):
 while p<len(s)and s[p].isspace():p+=1
 return p
def skip(s,p):
 p=ws(s,p)
 if s[p]=='"':return D.raw_decode(s,p)[1]
 if s[p]not in '{[':return D.raw_decode(s,p)[1]
 stack=[];quoted=False;escaped=False
 for i in range(p,len(s)):
  c=s[i]
  if quoted:
   if escaped:escaped=False
   elif c=='\\':escaped=True
   elif c=='"':quoted=False
  elif c=='"':quoted=True
  elif c in '{[':stack.append('}'if c=='{'else']')
  elif c in '}]':
   assert stack and stack.pop()==c
   if not stack:return i+1
 raise AssertionError('truncated source JSON container')
def fields(s,p=0):
 p=ws(s,p);assert s[p]=='{';p=ws(s,p+1);out={}
 while s[p]!='}':
  k,p=D.raw_decode(s,p);assert isinstance(k,str)and k not in out;p=ws(s,p);assert s[p]==':';p=ws(s,p+1)
  end=skip(s,p);out[k]=(p,end);p=ws(s,end)
  if s[p]==',':p=ws(s,p+1)
  else:assert s[p]=='}'
 return out,p+1
count=0;externs=0;rawbytes=0;largest=0;fallback=0;start=time.monotonic();coverage={};record_digest=hashlib.sha256()
outpath=P/'extern-rows.pending.jsonl'
with (S/'indexes'/(PIN+'.json')).open('rb')as f,outpath.open('w')as out:
 st=Stream(f);st.fill();prefix='{"declarations":[';assert st.s.startswith(prefix);st.p=len(prefix)
 while st.char()!=']':
  n,h=st.value();typed_name(n);assert re.fullmatch('[0-9a-f]{64}',h)
  path=S/'declarations'/(h+'.json');size=path.stat().st_size;assert size<=8*1024*1024,(h,size)
  b=path.read_bytes();assert len(b)==size and sha(b)==h
  rawbytes+=len(b);largest=max(largest,len(b));assert rawbytes<=24*1024*1024*1024
  try:r=json.loads(b)
  except RecursionError:
   # The accepted immutable producer can emit deeply nested fdecl bodies. The
   # fallback indexes root/ir fields iteratively, never accepts an extern without
   # full JSON decoding, and verifies exact indexed Name. SHA authenticates bytes.
   text=b.decode('utf8');top,end=fields(text);assert ws(text,end)==len(text)
   get=lambda k:json.loads(text[slice(*top[k])])
   ir,end=fields(text,top['ir'][0]);assert end==top['ir'][1]and set(ir)=={'fdecl'}
   r={'kind':get('kind'),'name':get('name'),'ir':{'fdecl':None}};fallback+=1
  assert r['kind']=='decl'and r['name']==n and len(r['ir'])==1
  kind=next(iter(r['ir']));assert kind in ['extern','fdecl']
  if kind=='extern':
   d=r['ir'][kind];assert d['f']==n and isinstance(d['xs'],list)and len(d['xs'])<=4096
   assert all(type(x['borrow'])is bool and type(x['x']['idx'])is int for x in d['xs'])
   assert len({x['x']['idx']for x in d['xs']})==len(d['xs'])
   assert isinstance(d['ext']['entries'],list)
   r.pop('pretty',None);record={'name':n,'sha256':h,'row':r};line=key(record)+'\n';out.write(line);record_digest.update(line.encode('utf8'));externs+=1
  count+=1;coverage[kind]=coverage.get(kind,0)+1;assert count<=500000
  if count%25000==0:print(json.dumps({'progress':count,'externs':externs,'raw-bytes':rawbytes,'seconds':round(time.monotonic()-start,2)}),flush=True)
  if st.char()==',':st.take(',')
  else:assert st.char()==']'
 st.take(']')
 while not st.eof:st.fill()
 suffix=st.s[st.p:];assert suffix.startswith(',');tail=json.loads('{'+suffix[1:]);assert tail['schema']=='lean-ir-store/1'
 assert st.h.hexdigest()==PIN and count==375258
outpath.replace(P/'extern-rows.jsonl')
manifest={'schema':'complete-original-extern-metadata/1','source-index-sha256':PIN,'source-index-bytes':st.bytes,'declarations':count,'kind-counts':coverage,'extern-row-count':externs,'extern-rows-sha256':record_digest.hexdigest(),'raw-CAS-bytes-checked':rawbytes,'largest-CAS-row':largest,'deep-fdecl-metadata-fallbacks':fallback,'collector-sha256':sha(pathlib.Path(__file__).read_bytes()),'limits':{'memory-MiB':256,'CPU-seconds':300,'wall-seconds':420,'index-MiB':160,'index-buffer-MiB':16,'row-MiB':8,'raw-total-GiB':24,'declarations':500000},'seconds':round(time.monotonic()-start,3),'peak-RSS-KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'JVM-or-guest-executed':False}
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(manifest),flush=True)
