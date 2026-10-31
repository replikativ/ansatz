#!/usr/bin/env python3
"""Compile only Init-specific units; reuse pinned structural Prelude exporter units."""
import argparse, hashlib, json, os, resource, signal, subprocess, time
from pathlib import Path
HERE=Path(__file__).resolve().parent
IR=HERE.parent
PIN='819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
GiB=1024**3

def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024**2), b''):h.update(b)
 return h.hexdigest()
def available():return next(int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:'))
def group_rss(pgid):
 total=0
 for p in Path('/proc').glob('[0-9]*'):
  try:
   if int((p/'stat').read_text().rsplit(')',1)[1].split()[2])==pgid:
    total+=next(int(l.split()[1])*1024 for l in (p/'status').read_text().splitlines() if l.startswith('VmRSS:'))
  except (FileNotFoundError, ProcessLookupError, StopIteration):pass
 return total
def bounded(command, env, stdout, stderr, seconds=180, output_directory=None):
 def limits():
  resource.setrlimit(resource.RLIMIT_CORE,(0,0))
  resource.setrlimit(resource.RLIMIT_CPU,(seconds,seconds))
  resource.setrlimit(resource.RLIMIT_FSIZE,(2*GiB,2*GiB))
 if available()<2*GiB:raise RuntimeError('MemAvailable below 2GiB')
 start=time.monotonic();peak=0;stop=None;last_report=start
 with stdout.open('wb') as out,stderr.open('wb') as err:
  p=subprocess.Popen(command,env=env,stdout=out,stderr=err,start_new_session=True,preexec_fn=limits)
  while p.poll() is None:
   peak=max(peak,group_rss(p.pid))
   if peak>2*GiB:stop='2GiB RSS cap'
   elif available()<2*GiB:stop='2GiB MemAvailable floor'
   elif time.monotonic()-start>seconds:stop='wall deadline'
   elif stderr.stat().st_size>1024**2:stop='stderr cap'
   if output_directory and time.monotonic()-last_report>15:
    files={f.name:f.stat().st_size for f in output_directory.iterdir() if f.is_file()}
    print(json.dumps({'elapsed':round(time.monotonic()-start,1),'RSSpeak':peak,'files':files}),flush=True);last_report=time.monotonic()
   if stop:
    os.killpg(p.pid,signal.SIGTERM)
    try:p.wait(timeout=2)
    except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
    break
   time.sleep(.05)
  code=p.wait()
 return {'command':command,'exit':code,'stop':stop,'peakRSSBytes':peak,'wallSeconds':time.monotonic()-start,'stdoutSHA256':sha(stdout),'stderrSHA256':sha(stderr)}
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('reuse',type=Path);p.add_argument('build',type=Path)
 a=p.parse_args();reuse=a.reuse.resolve();build=a.build.resolve();build.mkdir(parents=True,exist_ok=False)
 prefix=Path(subprocess.check_output(['lean','+leanprover/lean4:v4.33.1','--print-prefix'],text=True).strip())
 assert subprocess.check_output([str(prefix/'bin/lean'),'--githash'],text=True).strip()==PIN
 # Reused source must equal the already accepted structural patched exporter.
 cohort=json.loads((reuse/'build-cohort.json').read_text())
 inputs={}
 for relative in ['bin/lean','lib/lean/libleanshared.so']:
  f=prefix/relative;inputs[str(f)]=sha(f)
 for unit in ['Export','Projection','ScalarCensus']:
  for suffix in ['olean','c','o']:
   f=reuse/f'{unit}.{suffix}';inputs[str(f)]=sha(f)
 assert sha(reuse/'Export.lean')==cohort['exporterPatchedSha256']=='e77e2ab2f85e39eed95779b92b90837edf807e14aadffeb7569ef85015e8805f'
 for unit in ['Export','Projection','ScalarCensus']:
  for suffix in ['olean','c','o']:
   assert sha(reuse/f'{unit}.{suffix}')==cohort['sourceFiles'][f'build/{unit}.{suffix}']
 for unit in ['Projection','ScalarCensus']:
  f=IR/f'paired-prelude/{unit}.lean';inputs[str(f)]=sha(f)
  assert sha(f)==cohort['sourceFiles'][f'producer/{unit}.lean']
 inputs[str(reuse/'Export.lean')]=sha(reuse/'Export.lean')
 assert sha(IR/'native/ModuleDataTransport.cpp')==cohort['sourceFiles']['native/ModuleDataTransport.cpp']
 for f in [HERE/'MatchedInitProducer.lean',HERE/'InitScalarCensus.lean',HERE/'Native.cpp',HERE/'ScalarObservation.h',IR/'native/ModuleDataTransport.cpp',Path(__file__)]:inputs[str(f)]=sha(f)
 env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_SYSROOT=str(prefix),LEAN_PATH=str(build)+os.pathsep+str(reuse))
 commands=[]
 for unit in ['InitScalarCensus','MatchedInitProducer']:
  commands.append([str(prefix/'bin/lean'),f'--root={HERE}','-o',str(build/f'{unit}.olean'),'-c',str(build/f'{unit}.c'),str(HERE/f'{unit}.lean')])
  commands.append(['cc','-fPIC','-O0','-I',str(prefix/'include'),'-c',str(build/f'{unit}.c'),'-o',str(build/f'{unit}.o')])
 commands.append(['c++','-std=c++17','-fPIC','-O1','-I',str(prefix/'include'),str(HERE/'Native.cpp'),*[str(reuse/f'{u}.o') for u in ['Export','Projection']],*[str(build/f'{u}.o') for u in ['InitScalarCensus','MatchedInitProducer']],'-L',str(prefix/'lib/lean'),f'-Wl,-rpath,{prefix}/lib/lean','-rdynamic','-Wl,--no-as-needed','-lgcc_s','-Wl,--as-needed','-lleanshared','-o',str(build/'produce')])
 receipts=[]
 for i,cmd in enumerate(commands):
  r=bounded(cmd,env,build/f'{i}.stdout',build/f'{i}.stderr');receipts.append(r)
  (build/'build-receipt.json').write_text(json.dumps({'inputs':inputs,'runs':receipts},indent=2)+'\n')
  if r['exit'] or r['stop']:raise RuntimeError(f'build stage {i} failed: {build}/{i}.stdout and .stderr')
 inputs[str(build/'produce')]=sha(build/'produce')
 (build/'build-cohort.json').write_text(json.dumps({'schema':'matched-init-native-build/1','leanCommit':PIN,'inputs':inputs,'nativeEnvironmentFinalized':False},indent=2)+'\n')
 print(json.dumps({'build':str(build),'runs':receipts,'binarySHA256':sha(build/'produce')},indent=2))
if __name__=='__main__':main()
