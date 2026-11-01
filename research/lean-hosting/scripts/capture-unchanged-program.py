#!/usr/bin/env python3
"""One bounded native frontend export; source files are never rewritten."""
import argparse, hashlib, json, os, signal, subprocess, time
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--exporter',type=Path,required=True)
p.add_argument('--sysroot',type=Path,required=True)
p.add_argument('--source',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--module',required=True)
p.add_argument('roots',nargs='+')
a=p.parse_args()
if a.output.exists(): raise SystemExit('Refusing to overwrite capture')
a.output.mkdir(parents=True)
expected='819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
actual=subprocess.check_output([str(a.sysroot/'bin/lean'),'--githash'],text=True).strip()
if actual!=expected: raise SystemExit('Producer pin mismatch: '+actual)
cmd=[str(a.exporter.resolve()),'--source',str(a.source.resolve()),'--closure',a.module,*a.roots]
env={'PATH':str(a.sysroot/'bin')+':/usr/bin:/bin','LEAN_SYSROOT':str(a.sysroot),'LEAN_PATH':str(a.sysroot/'lib/lean'),'LD_LIBRARY_PATH':str(a.sysroot/'lib/lean'),'LEAN_NUM_THREADS':'1','LANG':'C.UTF-8'}
start=time.monotonic();peak=0;reason=None
with (a.output/'ir.jsonl').open('wb') as out,(a.output/'stderr').open('wb') as err:
 child=subprocess.Popen(cmd,stdout=out,stderr=err,env=env,start_new_session=True)
 while child.poll() is None:
  rss=0
  for stat in Path('/proc').glob('[0-9]*/stat'):
   try:
    fields=stat.read_text().rsplit(')',1)[1].split()
    if int(fields[2])==child.pid: rss+=int(fields[21])*os.sysconf('SC_PAGE_SIZE')
   except (OSError,ValueError,IndexError): pass
  peak=max(peak,rss)
  available=int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')))*1024
  if rss>1800*1024*1024: reason='1800 MiB process group RSS cap'
  elif available<1024**3: reason='1 GiB available memory floor'
  elif time.monotonic()-start>120: reason='120 second cap'
  if reason:
   os.killpg(child.pid,signal.SIGTERM)
   try:child.wait(timeout=3)
   except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait()
   break
  time.sleep(.1)
receipt={'schema':'unchanged-program-native-capture/1','command':cmd,'sysroot':str(a.sysroot),'producer':actual,'sourceSha256':hashlib.sha256(a.source.read_bytes()).hexdigest(),'exporterSha256':hashlib.sha256(a.exporter.read_bytes()).hexdigest(),'exit':child.returncode,'guardStop':reason,'peakRssBytes':peak,'wallSeconds':time.monotonic()-start}
(a.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
raise SystemExit(0 if child.returncode==0 and reason is None else 1)
