#!/usr/bin/env python3
"""Validate explicit historical and current source layers; never refresh pins."""
import argparse,hashlib,json,pathlib,re
P=pathlib.Path(__file__).resolve().parent
A=argparse.ArgumentParser();A.add_argument('--reviewed-root',type=pathlib.Path);args=A.parse_args()
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def local(name):
 p=P/name
 assert not pathlib.Path(name).is_absolute() and '..'not in pathlib.Path(name).parts,name
 assert p.is_file(),p
 return p
assert digest(local('acceptance.json'))=='d261a55a887a72a573022a39f0ec2dd6c788c1f09d46e6c5c36311643e5c7fb0','Historical acceptance was modified'
assert digest(local('nat-arithmetic-v3.json'))=='f4f2fc714cb6aa84498c9e8434076832180c32e5d08da5f2cd246bdd50851342','Historical arithmetic layer was modified'
acceptance=json.loads(local('acceptance.json').read_text())
M=json.loads(local('migration.json').read_text())
legacy_changes={'sequential-probe.clj','node-decoder.clj'}
baseline={item['file']:item['sha256']for item in acceptance['source-inventory']}
assert len(baseline)==len(acceptance['source-inventory'])
expected=dict(baseline)
allowed_arithmetic={'generated-command.clj','filesystem-profile.clj','filesystem-provider.clj','filesystem-file.clj','loader.clj','verify-source.py','models/nat-arithmetic.clj'}
allowed_general={'source-exchange.clj','models/source-exchange.clj','models/mutual-declaration.clj','composite-base.clj','models/composite-base.clj','general-file.clj','models/general-file.clj','driver.clj','lineage.clj','authority.clj','adapter.clj','generated-command.clj','loader.clj','verify-source.py','models/lineage.clj','models/adapter.clj','general-source-provider.clj','general-command.clj','generated-batch.clj','models/general-source-provider.clj','models/general-foundation.clj','models/general-command.clj','models/generated-batch.clj'}
arithmetic=json.loads(local('nat-arithmetic-v3.json').read_text())
general=json.loads(local('general-command-v1.json').read_text())
assert general['parent-layer']=={'file':'nat-arithmetic-v3.json','sha256':digest(local('nat-arithmetic-v3.json'))}
for layer,allowed in [(arithmetic,allowed_arithmetic),(general,allowed_general)]:
 assert layer['schema']=='artifact-frontend-source-delta/1'
 assert layer['base-acceptance-sha256']==digest(local('acceptance.json'))
 entries={item['file']:item for item in layer['sources']}
 assert len(entries)==len(layer['sources']) and set(entries)==allowed
 for name,item in entries.items():
  assert item['base-sha256']==expected.get(name),(name,'unexplained source-layer base')
  expected[name]=item['sha256']
# Migration records keep original review evidence; deliberate changes do not
# rewrite those earlier claims or permit arbitrary newly changed leaves.
for item in M['sources']:
 name=item['file'];local(name)
 if name not in legacy_changes:assert baseline[name]==item['reviewed-source-sha256'],name
 if args.reviewed_root:
  old=args.reviewed_root/item['reviewed-research-source']
  assert digest(old)==item['reviewed-source-sha256'],old
actual={str(p.relative_to(P))for p in P.rglob('*.clj')}|{'verify-source.py'}
assert set(expected)==actual,'Unlisted/missing Clojure source file'
current={item['file']:item['sha256']for item in general['source-inventory']}
assert len(current)==len(general['source-inventory']) and current==expected,'Complete source inventory differs from explicit layers'
for name,sha in expected.items():assert digest(local(name))==sha,name
for p in P.rglob('*.clj'):
 s=p.read_text();assert '/home/'not in s and '(find-var (symbol "user"'not in s,p
 stack=[];string=False;comment=False;escape=False
 for i,c in enumerate(s):
  if comment:
   if c=='\n':comment=False
  elif string:
   if escape:escape=False
   elif c=='\\':escape=True
   elif c=='"':string=False
  elif c==';':comment=True
  elif c=='"':string=True
  elif c in '([{':stack.append(c)
  elif c in ')]}':assert stack and stack.pop()=={')':'(',']':'[','}':'{'}[c],(p,s.count('\n',0,i)+1)
 assert not stack and not string,p
seq=local('sequential-probe.clj').read_text()
assert '[ansatz.research.ir.authenticated-demand :as demand]'in seq
assert all('"'+n+'" demand/'+n in seq for n in ['ensure-header!','service-code!','original-row!'])
assert '(find-var'not in seq
loader=local('loader.clj').read_text()
units=re.findall(r'\["([^"]+\.clj)" ([^\]\s]+)\]',loader)
assert units==[tuple(item)for item in general['ordered-load-units']]
assert len(units)==38 and len({name for name,_ in units})==38
for file,namespace in units:
 assert re.search(r'\(ns\s+'+re.escape(namespace)+r'(?:\s|\))',local(file).read_text()),(file,namespace)
assert units.index(('general-command.clj','general-command-receipt-v1'))<units.index(('generated-batch.clj','general-generated-batch-v1'))
for match in re.finditer(r'\]\(([^)]+)\)',local('README.md').read_text()):
 path=match.group(1)
 if '://'not in path and not path.startswith('#'):assert (P/path.split('#')[0]).exists(),path
root=P.parents[4]
corpus=acceptance['corpus'];fixture=root/corpus['file']
assert fixture.stat().st_size==corpus['bytes'] and digest(fixture)==corpus['sha256'],fixture
fixture=root/arithmetic['fixture-directory']
for name,sha in arithmetic['fixture-files'].items():assert digest(fixture/name)==sha,name
for item in general['tracked-references']:
 path=pathlib.Path(item['file'])
 assert not path.is_absolute() and '..'not in path.parts,path
 assert digest(root/path)==item['sha256'],path
# Exact companion source/contract/producer pins remain separately reproducible.
companion=json.loads((root/'experiments/lean-ir/research/java-ir-baseline/observed-frontend/source-manifest.json').read_text())
lean=root/'experiments/lean-ir'
assert digest(lean/companion['source'])==companion['pins']['source_sha256']
assert digest(lean/companion['contract'])==companion['sourceContractSHA256']
assert digest(lean/companion['producerRunner'])==companion['runnerSHA256']
assert digest(lean/'scripts/test-produce-observed-frontend.py')==companion['producerTestSHA256']
if args.reviewed_root:
 for item in acceptance['external-evidence']+general['external-evidence']:
  assert digest(args.reviewed_root/item['file'])==item['sha256'],item['file']
identical=[item['file']for item in M['sources']if digest(local(item['file']))==item['reviewed-source-sha256']]
print(json.dumps({'historical-acceptance-unchanged':True,'source-layers':2,'reviewed-copies':len(M['sources']),'currently-byte-identical-reviewed-copies':len(identical),'intentional-generic-source-deltas':sorted(allowed_general),'ordered-load-units':len(units),'complete-source-files':len(actual),'all-Clojure-delimiters-balanced':True,'machine-paths':0,'generic-runtime-status':general['acceptance'],'JVM-or-native-executed-by-verifier':False}))
