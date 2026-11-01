#!/usr/bin/env python3
"""Bounded compiled pinned widening casts; not a full native Lean ABI oracle."""
import argparse,hashlib,json,pathlib,re,resource,subprocess
resource.setrlimit(resource.RLIMIT_AS,(256*1024*1024,256*1024*1024));resource.setrlimit(resource.RLIMIT_CPU,(25,30))
p=argparse.ArgumentParser();p.add_argument('--lean-repository',required=True);p.add_argument('--output',required=True);a=p.parse_args()
f=pathlib.Path(__file__).resolve().parent;o=pathlib.Path(a.output);o.mkdir(parents=True,exist_ok=True);m=json.loads((f/'provenance.json').read_text());pin=m['lean-commit']
src=subprocess.check_output(['git','-c','core.packedGitWindowSize=1m','-c','core.packedGitLimit=8m','-C',a.lean_repository,'show',pin+':src/include/lean/lean.h'],timeout=15);assert hashlib.sha256(src).hexdigest()==m['upstream-source-sha256']['src/include/lean/lean.h'];s=src.decode();parts=[]
for name in ['lean_uint8_to_uint64','lean_uint32_to_uint64','lean_usize_to_uint64']:
 match=re.search(r'static inline [^\n]+\b'+name+r'\([^\n]*\) \{[^\n]*\}',s);assert match,name;parts.append(match.group())
expected='\n'.join(s.splitlines()[:6])+'\n#pragma once\n#include <stdint.h>\n#include <stddef.h>\n\n'+'\n'.join(parts)+'\n';assert (f/'pinned-inline.h').read_text()==expected
version=subprocess.check_output(['g++','--version'],timeout=10).decode().splitlines()[0];subprocess.run(['g++','-std=c++17','-O2',str(f/'oracle.cpp'),'-o',str(o/'oracle')],check=True,capture_output=True,timeout=25)
inputs=[(8,x) for x in [0,1,127,128,255]]+[(32,x) for x in [0,1,2**31-1,2**31,2**32-1]]+[(64,x) for x in [0,1,2**63-1,2**63,2**64-1]];data=''.join(f'{lane} {value}\n' for lane,value in inputs).encode();run=subprocess.run([str(o/'oracle')],input=data,capture_output=True,check=True,timeout=10);assert not run.stderr
rows=[]
for line,item in zip(run.stdout.decode().splitlines(),inputs,strict=True):
 cols=line.split();assert len(cols)==3 and tuple(map(int,cols[:2]))==item
 rows.append({'lane':int(cols[0]),'input':cols[1],'result':cols[2]})
b=(json.dumps(rows,indent=2)+'\n').encode();(o/'native-vectors.json').write_bytes(b)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
receipt={'schema':'compiled-pinned-u64-widening-casts/1','scope':'exact inline casts with typed I/O scaffolding, not full Lean runtime ABI','lean-commit':pin,'word-bits':64,'compiler':version,'compile-flags':['-std=c++17','-O2'],'limits':{'address-space-mib':256,'compile-wall-seconds':25,'oracle-wall-seconds':10},'functions':3,'vectors':len(rows),'exit':run.returncode,'stderr-bytes':len(run.stderr),'inline-sha256':sha(f/'pinned-inline.h'),'driver-sha256':sha(f/'oracle.cpp'),'binary-sha256':sha(o/'oracle'),'vectors-sha256':hashlib.sha256(b).hexdigest(),'stdout-sha256':hashlib.sha256(run.stdout).hexdigest()};(o/'native-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
