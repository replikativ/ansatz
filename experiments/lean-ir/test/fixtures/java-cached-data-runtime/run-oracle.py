#!/usr/bin/env python3
"""Compiled pinned getter offset oracle, explicitly not complete native object ABI."""
import argparse,hashlib,json,pathlib,re,resource,subprocess
resource.setrlimit(resource.RLIMIT_AS,(256*1024*1024,256*1024*1024));resource.setrlimit(resource.RLIMIT_CPU,(25,30))
p=argparse.ArgumentParser();p.add_argument('--lean-repository',required=True);p.add_argument('--output',required=True);a=p.parse_args();f=pathlib.Path(__file__).resolve().parent;o=pathlib.Path(a.output);o.mkdir(parents=True,exist_ok=True);m=json.loads((f/'provenance.json').read_text());pin=m['lean-commit'];sraw=subprocess.check_output(['git','-c','core.packedGitWindowSize=1m','-c','core.packedGitLimit=8m','-C',a.lean_repository,'show',pin+':src/include/lean/lean.h'],timeout=15);assert hashlib.sha256(sraw).hexdigest()==m['upstream-source-sha256']['src/include/lean/lean.h'];s=sraw.decode();parts=[]
for name in ['lean_ctor_get_uint64','lean_expr_data']:
 match=re.search(r'static inline [^\n]+\b'+name+r'\([^\n]*\) \{',s);assert match,name;i=match.end();d=1
 while d:
  if s[i]=='{':d+=1
  elif s[i]=='}':d-=1
  i+=1
 parts.append(s[match.start():i])
assert (f/'pinned-inline.h').read_text()=='\n'.join(s.splitlines()[:6])+'\n#pragma once\n\n'+'\n'.join(parts)+'\n'
version=subprocess.check_output(['g++','--version'],timeout=10).decode().splitlines()[0];subprocess.run(['g++','-std=c++17','-O2',str(f/'oracle.cpp'),'-o',str(o/'oracle')],capture_output=True,check=True,timeout=25)
inputs=[(n,w,t) for n in range(1,5) for w,t in [(0,255),(1,255),(2**63,0xabcdef0123456789),(2**64-1,255)]];data=''.join(f'{n} {w} {t}\n' for n,w,t in inputs).encode();run=subprocess.run([str(o/'oracle')],input=data,capture_output=True,check=True,timeout=10);assert not run.stderr;rows=[]
for line,item in zip(run.stdout.decode().splitlines(),inputs,strict=True):
 cols=line.split();assert len(cols)==4 and tuple(map(int,cols[:3]))==item
 rows.append({'objects':int(cols[0]),'word':cols[1],'tail':cols[2],'result':cols[3]})
b=(json.dumps(rows,indent=2)+'\n').encode();(o/'native-vectors.json').write_bytes(b)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
r={'schema':'compiled-pinned-expression-cache-offset/1','scope':'verbatim getter bodies with modeled storage API scaffolding; not complete native Lean object ABI','lean-commit':pin,'compiler':version,'word-bits':64,'vectors':len(rows),'exit':run.returncode,'stderr-bytes':len(run.stderr),'storage-read-only-check':True,'inline-sha256':sha(f/'pinned-inline.h'),'driver-sha256':sha(f/'oracle.cpp'),'binary-sha256':sha(o/'oracle'),'vectors-sha256':hashlib.sha256(b).hexdigest(),'limits':{'address-space-mib':256,'compile-wall-seconds':25,'oracle-wall-seconds':10}};(o/'native-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
