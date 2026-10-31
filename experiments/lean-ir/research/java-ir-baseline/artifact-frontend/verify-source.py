#!/usr/bin/env python3
"""Source-only migration checks. Optional reviewed checkout is read-only."""
import argparse,hashlib,json,pathlib,re
P=pathlib.Path(__file__).resolve().parent
A=argparse.ArgumentParser();A.add_argument('--reviewed-root',type=pathlib.Path);args=A.parse_args()
M=json.loads((P/'migration.json').read_text());changes={'sequential-probe.clj','node-decoder.clj'}
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
assert len(units)==16
for file,namespace in units:
 assert (P/file).is_file(),file
 assert re.search(r'\(ns\s+'+re.escape(namespace)+r'(?:\s|\))',(P/file).read_text()),(file,namespace)
for match in re.finditer(r'\]\(([^)]+)\)',(P/'README.md').read_text()):
 path=match.group(1)
 if '://'not in path and not path.startswith('#'):assert (P/path.split('#')[0]).exists(),path
print(json.dumps({'reviewed-copies':len(M['sources']),'byte-identical-copies':len(M['sources'])-len(changes),'intentional-source-deltas':sorted(changes),'ordered-load-units':len(units),'all-Clojure-delimiters-balanced':True,'machine-paths':0,'JVM-or-native-executed':False}))
