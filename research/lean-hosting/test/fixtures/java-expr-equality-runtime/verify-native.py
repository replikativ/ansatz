#!/usr/bin/env python3
"""Verify pinned native oracle evidence or independently produced mode outputs.
Never runs a compiler, changes a source/receipt, or rewrites a golden.
"""
import argparse,hashlib,json,pathlib
P=pathlib.Path(__file__).resolve().parent
SOURCE='946fb2b740684a1c790ba2f4ff8209086211ae8d34e87f925882170dd0a38004'
OUTPUT='0d0cbf1bdae0cd79c32683fe76e5c8233f8805d24e78a99d63bd273af7363c19'
RECEIPT='93aa0912a7d6035579d1bbaab744233998b8e0723e9cec820581c756d4793b64'
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
a=argparse.ArgumentParser();a.add_argument('--run-output',type=pathlib.Path);a.add_argument('--native-output',type=pathlib.Path);args=a.parse_args()
assert digest(P/'ExprEqualityOracle.lean')==SOURCE
assert digest(P/'native-golden.txt')==OUTPUT
assert len((P/'native-golden.txt').read_text().splitlines())==54
assert digest(P/'native-observation.json')==RECEIPT
r=json.loads((P/'native-observation.json').read_text())
assert r['passed']is True and r['case-count']==54 and r['source-sha256']==SOURCE and r['output-sha256']==OUTPUT
assert r['lean-commit']=='819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
assert r['modes']==['--run','C/native']
for command in r['commands']:
 assert command['exit']==0 and command['stop']is None
 if command['label']in('run','native'):assert command['stdout-sha256']==OUTPUT
assert (args.run_output is None)==(args.native_output is None),'Supply both mode outputs'
for path in [args.run_output,args.native_output]:
 if path is not None:assert digest(path)==OUTPUT,(str(path),'differs from immutable golden')
print('PASS: pinned source, 54-case golden, successful native observation'+(' and both supplied outputs'if args.run_output else ''))
