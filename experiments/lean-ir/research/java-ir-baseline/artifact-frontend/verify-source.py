#!/usr/bin/env python3
"""Source-only migration checks. Optional reviewed checkout is read-only."""
import argparse,hashlib,json,pathlib,re
P=pathlib.Path(__file__).resolve().parent
A=argparse.ArgumentParser();A.add_argument('--reviewed-root',type=pathlib.Path);args=A.parse_args()
M=json.loads((P/'migration.json').read_text());changes={'sequential-probe.clj','node-decoder.clj'}
extension=json.loads((P/'nat-arithmetic-v3.json').read_text())
assert extension['schema']=='artifact-frontend-source-delta/1'
assert extension['base-acceptance-sha256']==hashlib.sha256((P/'acceptance.json').read_bytes()).hexdigest()
deltas={item['file']:item for item in extension['sources']}
assert set(deltas)=={'generated-command.clj','filesystem-profile.clj','filesystem-provider.clj',
                     'filesystem-file.clj','loader.clj','verify-source.py','models/nat-arithmetic.clj'}
for item in M['sources']:
 p=P/item['file'];assert p.is_file(),p
 if item['file']not in changes:assert hashlib.sha256(p.read_bytes()).hexdigest()==item['reviewed-source-sha256'],p
 if args.reviewed_root:
  old=args.reviewed_root/item['reviewed-research-source'];assert hashlib.sha256(old.read_bytes()).hexdigest()==item['reviewed-source-sha256'],old
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
seq=(P/'sequential-probe.clj').read_text();assert '[ansatz.research.ir.authenticated-demand :as demand]'in seq
assert all('"'+n+'" demand/'+n in seq for n in ['ensure-header!','service-code!','original-row!'])
assert '(find-var'not in seq
# Loading the package defines only functions/data. Guest entry points stay in
# defn bodies; this audit is not a Clojure compiler or runtime proof.
loader=(P/'loader.clj').read_text();units=re.findall(r'\["([^"]+\.clj)" ([^\]\s]+)\]',loader)
assert len(units)==24
for file,namespace in units:
 assert (P/file).is_file(),file
 assert re.search(r'\(ns\s+'+re.escape(namespace)+r'(?:\s|\))',(P/file).read_text()),(file,namespace)
for match in re.finditer(r'\]\(([^)]+)\)',(P/'README.md').read_text()):
 path=match.group(1)
 if '://'not in path and not path.startswith('#'):assert (P/path.split('#')[0]).exists(),path
acceptance=json.loads((P/'acceptance.json').read_text())
corpus=acceptance['corpus'];fixture=P.parents[4]/corpus['file']
assert fixture.stat().st_size==corpus['bytes']
assert hashlib.sha256(fixture.read_bytes()).hexdigest()==corpus['sha256'],fixture
inventory=acceptance['source-inventory']
expected={str(p.relative_to(P))for p in P.rglob('*.clj')}|{'verify-source.py'}
assert {item['file']for item in inventory}|{name for name,item in deltas.items()if item['base-sha256']is None}==expected,'Acceptance source inventory differs'
for item in inventory:
 if item['file']in deltas:assert deltas[item['file']]['base-sha256']==item['sha256'],item['file']
 else:assert hashlib.sha256((P/item['file']).read_bytes()).hexdigest()==item['sha256'],item['file']
for name,item in deltas.items():
 assert hashlib.sha256((P/name).read_bytes()).hexdigest()==item['sha256'],name
fixture=P.parents[4]/extension['fixture-directory']
for name,digest in extension['fixture-files'].items():
 assert hashlib.sha256((fixture/name).read_bytes()).hexdigest()==digest,name
if args.reviewed_root:
 for item in acceptance['external-evidence']:
  assert hashlib.sha256((args.reviewed_root/item['file']).read_bytes()).hexdigest()==item['sha256'],item['file']
print(json.dumps({'reviewed-copies':len(M['sources']),'byte-identical-copies':len(M['sources'])-len(changes),'intentional-source-deltas':sorted(changes),'versioned-arithmetic-source-deltas':sorted(deltas),'arithmetic-execution-acceptance':extension['acceptance'],'ordered-load-units':len(units),'all-Clojure-delimiters-balanced':True,'machine-paths':0,'JVM-or-native-executed':False}))
