#!/usr/bin/env python3
"""Reproduce arithmetic vectors with bounded g++; no JVM/Lean image/Init.
The copied algorithm bodies are verbatim pinned Lean inline functions; only the
include/type/driver scaffolding is local. Vectors are read by the executable.
"""
import argparse,hashlib,json,pathlib,re,resource,subprocess
resource.setrlimit(resource.RLIMIT_AS,(256*1024*1024,256*1024*1024))
resource.setrlimit(resource.RLIMIT_CPU,(25,30))
p=argparse.ArgumentParser();p.add_argument('--lean-repository',required=True);p.add_argument('--output',required=True);a=p.parse_args()
fixture=pathlib.Path(__file__).resolve().parent;out=pathlib.Path(a.output);out.mkdir(parents=True,exist_ok=True)
manifest=json.loads((fixture/'provenance.json').read_text());pin=manifest['lean-commit']
raw=subprocess.check_output(['git','-c','core.packedGitWindowSize=1m','-c','core.packedGitLimit=8m','-C',a.lean_repository,'show',pin+':src/include/lean/lean.h'],timeout=15)
assert hashlib.sha256(raw).hexdigest()==manifest['upstream-source-sha256']['src/include/lean/lean.h']
s=raw.decode();names=['lean_bool_to_uint64']+['lean_uint64_'+x for x in ['add','sub','mul','div','mod','land','lor','complement','neg','log2','shift_left','dec_le']];parts=[]
for name in names:
 m=re.search(r'static inline [^\n]+\b'+name+r'\([^\n]*\) \{',s);assert m,name
 i=m.end();depth=1
 while depth:
  if s[i]=='{':depth+=1
  elif s[i]=='}':depth-=1
  i+=1
 parts.append(s[m.start():i])
expected='\n'.join(s.splitlines()[:6])+'\n#pragma once\n#include <stdint.h>\n\n'+'\n'.join(parts)+'\n'
assert (fixture/'pinned-inline.h').read_text()==expected
compiler=subprocess.check_output(['g++','--version'],timeout=10).decode().splitlines()[0]
command=['g++','-std=c++17','-O2','-fno-fast-math',str(fixture/'oracle.cpp'),'-o',str(out/'oracle')]
subprocess.run(command,check=True,capture_output=True,timeout=25)
m=2**64-1;h=2**63
pairs=[(0,0),(0,64),(1,0),(m,0),(m,1),(m,2),(h,2),(h,h),(m,h),(1,63),(1,64),(1,65),(1,m),(2,63),(h,1),(m,m),(h-1,m),(2,64),(63,65),(65,63)]
vectors=[(b,a,c) for b in [0,1] for a,c in pairs];input_data=''.join(f'{b} {a} {c}\n' for b,a,c in vectors).encode()
run=subprocess.run([str(out/'oracle')],input=input_data,capture_output=True,check=True,timeout=10);assert not run.stderr
keys=['Bool.toUInt64']+['UInt64.'+x for x in ['add','sub','mul','div','mod','land','lor','complement','neg','log2','shiftLeft','decLe']]
results=[]
for line,inputs in zip(run.stdout.decode().splitlines(),vectors,strict=True):
 cols=line.split();assert len(cols)==16 and tuple(map(int,cols[:3]))==inputs
 results.append({'flag':cols[0],'a':cols[1],'b':cols[2],'results':dict(zip(keys,cols[3:],strict=True))})
blob=(json.dumps(results,indent=2)+'\n').encode();(out/'native-vectors.json').write_bytes(blob)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
receipt={'schema':'pinned-inline-u64-arithmetic-oracle/1','scope':'compiled pinned inline arithmetic, not full Lean runtime ABI','lean-commit':pin,'compiler':compiler,'compile-flags':['-std=c++17','-O2','-fno-fast-math'],'limits':{'address-space-mib':256,'cpu-soft-seconds':25,'compile-wall-seconds':25,'oracle-wall-seconds':10},'inline-sha256':sha(fixture/'pinned-inline.h'),'driver-sha256':sha(fixture/'oracle.cpp'),'binary-sha256':sha(out/'oracle'),'vectors-sha256':hashlib.sha256(blob).hexdigest(),'vectors':len(results),'functions':len(keys),'exit':run.returncode,'stderr-bytes':len(run.stderr),'input-sha256':hashlib.sha256(input_data).hexdigest(),'stdout-sha256':hashlib.sha256(run.stdout).hexdigest()}
(out/'native-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
