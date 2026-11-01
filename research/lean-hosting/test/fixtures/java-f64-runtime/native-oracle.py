"""Bounded matching Lean4.33.1 native oracle, runtime-fed words/Nats, no JVM.
Run from this directory; LEAN_BINARY may select the exact matching pinned binary.
"""
import hashlib,json,os,pathlib,random,struct,subprocess,resource
D=pathlib.Path(__file__).resolve().parent
exe=pathlib.Path(os.environ.get('LEAN_BINARY',pathlib.Path.home()/'.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean')).resolve()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def word(x):return struct.unpack('>Q',struct.pack('>d',x))[0]
pin='819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
env=dict(os.environ,LC_ALL='C',LANG='C')
work=D.parents[4]/'target/java-f64-runtime-v1/native-oracle';work.mkdir(parents=True,exist_ok=True)
shim=work/'profile.so';flags=['-std=c++20','-O2','-fPIC','-shared']
def compiler_limit(): resource.setrlimit(resource.RLIMIT_AS,(256*1024*1024,256*1024*1024))
compiler=subprocess.check_output(['g++','--version'],text=True).splitlines()[0]
build=subprocess.run(['g++',*flags,str(D/'Profile.cpp'),'-o',str(shim)],capture_output=True,text=True,preexec_fn=compiler_limit,timeout=30)
assert build.returncode==0,(build.stdout,build.stderr)
version=subprocess.check_output([str(exe),'--version'],env=env,text=True);assert pin in version and 'x86_64-unknown-linux-gnu' in version
bits=[0,1,(1<<52)-1,1<<52,0x7fefffffffffffff,0x7ff0000000000000,0x7ff8000000000042,0x7ff0000000000001]
bits += [x|(1<<63) for x in list(bits)]
for x in [0.1,1/128,3/128,1/3,1.0,0.0000005,0.0000015]:
 u=word(x);bits += [u-1,u,u+1,(u-1)|(1<<63),u|(1<<63),(u+1)|(1<<63)]
rng=random.Random(4331);bits+= [rng.getrandbits(64) for _ in range(24)]
rows=[{'op':'bits','a':str(u),'b':'0'} for u in bits]
u64=[0,1,(1<<64)-1]
for e in [53,54,60,63]:u64 += [(1<<e)+delta for delta in [-1,0,1,3,1023,1024,1025]]
rows += [{'op':'u64','a':str(u),'b':'0'} for u in u64]
nats=u64+[(1<<64)+x for x in [0,2047,2048,2049,2051]]+[(1<<100)+x for x in [0,1,(1<<47)-1,1<<47,(1<<47)+1]]
threshold=(1<<1024)-(1<<970);nats += [threshold-1,threshold,threshold+1,1<<1100]
rows += [{'op':'nat','a':str(u),'b':'0'} for u in nats]
pairs=[(word(1.0),word(3.0)),(word(-0.0),word(0.0)),(word(0.0),word(-0.0)),(0x7fefffffffffffff,word(2.0)),(1,word(2.0)),(1<<52,word(0.5)),(0x7ff0000000000000,0x7ff0000000000000),(word(1.0),0),(word(1.0),1<<63),(0,0),(0x7ff8000000000042,word(1.0)),(word(1.0),0xfff8000000000042)]
pairs += [(rng.getrandbits(64),rng.getrandbits(64)) for _ in range(12)]
for op in ['sub','mul','div','eq','lt']:
 rows += [{'op':op,'a':str(a),'b':str(b)} for a,b in pairs]
data=''.join(f"{x['op']} {x['a']} {x['b']}\n" for x in rows)
p=subprocess.run([str(exe),'--load-dynlib='+str(shim),'--run',str(D/'Oracle.lean')],input=data,text=True,capture_output=True,env=env,timeout=30);assert p.returncode==0,(p.stdout,p.stderr)
lines=p.stdout.splitlines();profile=lines.pop(0);assert profile=='profile|1|1|1',profile
assert len(lines)==len(rows),(len(lines),len(rows))
for r,line in zip(rows,lines):
 b,t,c=line.split('|');r.update(bits=b,text=t,comparison=int(c))
out=(json.dumps(rows,indent=2)+'\n').encode();(D/'native-vectors.json').write_bytes(out)
ldd=subprocess.check_output(['ldd',str(exe)],text=True);deps={}
for line in ldd.splitlines():
 parts=line.split()
 if '=>' in parts and len(parts)>2 and parts[2].startswith('/'):
  f=pathlib.Path(parts[2]).resolve();deps[f.name]={'bytes':f.stat().st_size,'sha256':sha(f)}
receipt={'schema':'matching-native-f64-oracle/1','lean-commit':pin,'binary-sha256':sha(exe),'version':version.strip(),'library-hashes':deps,'script-sha256':sha(D/'Oracle.lean'),'input-sha256':hashlib.sha256(data.encode()).hexdigest(),'vectors-sha256':hashlib.sha256(out).hexdigest(),'rows':len(rows),'exit':p.returncode,'stderr':p.stderr,'environment':{'LC_ALL':'C','LANG':'C'},'same-process-profile':{'FE_TONEAREST':True,'LC_NUMERIC':'C','native-ofBits-quietNaN-word':'7ff8000000000000','query':profile,'shim-source-sha256':sha(D/'Profile.cpp'),'shim-binary-sha256':sha(shim),'compiler':compiler,'compiler-flags':flags,'compiler-exit':build.returncode,'compiler-stderr':build.stderr},'rounding-scope':'Read-only same-process fenv/locale queries before runtime vectors; observed nearest/even six-decimal output including exact ties and adjacent values. No dynamic fenv/locale mutation in oracle; not all libc/FENV configurations.','native-NaN-scope':'Float.toBits canonicalizes NaNs; arithmetic NaN payload parity is not asserted.','provenance-scope':'Installed matching binary/runtime, not proof it is the executable that produced the accepted checkpoint.'}
(D/'native-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
