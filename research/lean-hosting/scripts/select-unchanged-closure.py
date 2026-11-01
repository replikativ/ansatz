#!/usr/bin/env python3
"""Select original declaration rows verbatim; audit before raw runtime execution."""
import argparse, collections, json
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('capture',type=Path)
p.add_argument('output',type=Path)
p.add_argument('roots',nargs='+')
a=p.parse_args()
if a.output.exists():raise SystemExit('Refusing to overwrite selected closure')
def label(n):
 if n[0]=='anonymous':return ''
 parent=label(n[1])
 return parent+('.' if parent else '')+str(n[2])
lines=a.capture.read_text().splitlines(keepends=True)
rows=[json.loads(line) for line in lines]
byname={}
for row,line in zip(rows[1:],lines[1:]):
 key=label(row['name'])
 if key in byname:raise SystemExit('Duplicate or ambiguous rendered Name label: '+key)
 byname[key]=(row,line)
seen=set();todo=a.roots[:]
while todo:
 n=todo.pop()
 if n in seen:continue
 if n not in byname:raise SystemExit('Missing original dependency: '+n)
 row,_=byname[n]
 if row['kind']!='decl':raise SystemExit('Unresolved original declaration: '+n)
 seen.add(n);todo.extend(label(d) for d in row.get('dependencies',[]))
selected=[row for row in rows[1:] if label(row['name']) in seen]
a.output.parent.mkdir(parents=True,exist_ok=True)
a.output.write_text(lines[0]+''.join(line for row,line in zip(rows[1:],lines[1:]) if label(row['name']) in seen))
ops=collections.Counter()
def walk(x):
 if isinstance(x,list):
  if x and isinstance(x[0],str):ops[x[0]]+=1
  for value in x:walk(value)
 elif isinstance(x,dict):
  for value in x.values():walk(value)
for row in selected:walk(row['ir'])
print(json.dumps({'declarations':len(selected),'sourceLocal':sum(bool(row['sourceLocal']) for row in selected),'externs':[{'name':label(row['name']),'data':row['ir']['extern']['ext']} for row in selected if 'extern' in row['ir']],'structuralTags':dict(ops)},indent=2))
