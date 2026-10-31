#!/usr/bin/env python3
"""Native default Init paired export. Produces evidence, never admission or guest finalization."""
import argparse,json,os,shutil,subprocess
from pathlib import Path
from build import bounded,sha,PIN
HERE=Path(__file__).resolve().parent

def snapshot(files):return {str(p):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(files)}
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('build',type=Path);p.add_argument('census',type=Path);p.add_argument('output',type=Path)
 a=p.parse_args();build=a.build.resolve();out=a.output.resolve()
 census=json.loads(a.census.read_text());assert census['leanCommit']==PIN and census['moduleCount']==631
 paths={Path(part['file']) for m in census['modules'] for part in m['parts']+m['irParts']}
 assert len(paths)==3155
 cohort=json.loads((build/'build-cohort.json').read_text())
 for f,h in cohort['inputs'].items():assert sha(f)==h,f
 assert cohort['leanCommit']==PIN
 sources={f.name:sha(f) for f in HERE.iterdir() if f.is_file()}
 before=snapshot(paths)
 out.mkdir(parents=True,exist_ok=False)
 shutil.copyfile(build/'build-cohort.json',out/'build-cohort.json')
 (out/'module-file-cohort.json').write_text(json.dumps(before,sort_keys=True,indent=2)+'\n')
 (out/'producer-source-cohort.json').write_text(json.dumps(sources,sort_keys=True,indent=2)+'\n')
 prefix=Path(subprocess.check_output(['lean','+leanprover/lean4:v4.33.1','--print-prefix'],text=True).strip())
 env=dict(os.environ,LEAN_SYSROOT=str(prefix),LEAN_NUM_THREADS='1');env.pop('LEAN_PATH',None)
 result=bounded([str(build/'produce'),str(out)],env,out/'producer.stdout',out/'producer.stderr',seconds=240,output_directory=out)
 (out/'producer-resources.json').write_text(json.dumps(result,indent=2)+'\n')
 if result['exit'] or result['stop']:raise RuntimeError(f'Native export failed; preserved in {out}')
 assert before==snapshot(paths),'module bytes changed during read'
 assert sources=={f.name:sha(f) for f in HERE.iterdir() if f.is_file()},'producer source changed during export'
 source=json.loads((out/'source-metadata.json').read_text())
 actual={p['artifact']['filePath'] for m in source['modules'] for p in m['parts']+m['irParts']}
 assert actual==set(before),'actual selected source file set differs from census'
 files={f.name:{'sha256':sha(f),'bytes':f.stat().st_size} for f in out.iterdir() if f.is_file()}
 receipt={'schema':'matched-default-init-native-pair/1','files':files,'leanCommit':PIN,'censusSHA256':sha(a.census),
          'nativeEnvironmentFinalized':False,'proofReplay':False,'guestAdmission':False,
          'nativeGraphCloneVerification':False,'initializerExecutionObserved':False}
 (out/'native-pair-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'directory':str(out),'run':result,'files':files},indent=2))
if __name__=='__main__':main()
