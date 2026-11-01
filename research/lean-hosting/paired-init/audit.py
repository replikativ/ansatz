#!/usr/bin/env python3
"""Streaming paired Init correspondence audit; sqlite holds declaration payloads."""
import hashlib,json,sqlite3,sys,tempfile
from pathlib import Path
PIN='819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
def require(c,m):
 if not c:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024**2),b''):h.update(b)
 return h.hexdigest()
def records(p):
 with p.open() as f:
  for line in f:
   require(len(line)<=32*1024**2,'record byte bound')
   yield json.loads(line)
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def scalar_claims(scalar):
 claims={}
 nat_types={'Lean.Name.num','Lean.Literal.natVal','Lean.IR.LitVal.num','Lean.Compiler.LCNF.LitValue.nat','Std.Format.tag'}
 for c in scalar['claims']:
  key=(c['nodeId'],c['fieldIndex'])
  require(key not in claims and type(c['value'])is str and c['value'].isdigit() and 2147483647<int(c['value'])<=9223372036854775807,'typed scalar key/payload')
  if c['domain']=='Nat':
   require(c['sourceType']in nat_types and 'signedValue'not in c,'typed Nat source')
  else:
   require(c['domain']=='Int' and c['sourceType']=='Std.Format.nest' and int(c['value'])<=4294967295,'typed Int source')
   require(c['signedValue']==str(int(c['value'])-4294967296),'native signed32 Int decoding')
  claims[key]=c['value']
 require(len(claims)==scalar['claimCount'],'typed claim count')
 return claims
def audit(d):
 d=Path(d)
 receipt=json.loads((d/'native-pair-receipt.json').read_text())
 require(receipt['leanCommit']==PIN and not receipt['nativeEnvironmentFinalized'] and not receipt['guestAdmission'],'native receipt profile')
 for f,info in receipt['files'].items():
  require(Path(f).name==f and f not in ['.','..'],'receipt file leaf')
  require((d/f).stat().st_size==info['bytes'] and sha(d/f)==info['sha256'],'artifact digest '+f)
 source=json.loads((d/'source-metadata.json').read_text())
 require(source['leanCommit']==PIN and source['globalLevel']=='private' and len(source['modules'])==631,'source profile')
 init=['str',['anonymous'],'Init']
 require(source['requestedImports']==[dict(module=init,importAll=False,isExported=True,isMeta=False),dict(module=init,importAll=False,isExported=True,isMeta=True)],'ordinary implicit Init header')
 roots={};count=0
 for m in source['modules']:
  for p in m['parts']+m['irParts']:
   require(p['rootIndex']==count,'source root order');roots[count]=p;count+=1
 require(count==3155,'source part count')
 selected={m['selectedRoot']:roots[m['selectedRoot']]['moduleData']['constantCount'] for m in source['modules']}
 require(sum(selected.values())==66124,'source occurrence count')
 transport=next(records(d/'module-data.jsonl'))
 require(transport['input']==source,'ModuleData input coupling')
 require(not transport['inventory']['nativeRoundtripVerified'],'streaming no-clone profile')
 names=[('anonymous',)];levels=bytearray([1]);exprs=bytearray();dependencies=set()
 def mark(bits,i,label):
  require(type(i)is int and 0<=i<=25000000,label+' index bound')
  if i>=len(bits):bits.extend(b'\0'*(i+1-len(bits)))
  require(not bits[i],label+' duplicate');bits[i]=1
 def has(bits,i,label):require(type(i)is int and 0<=i<len(bits) and bits[i],label+' unresolved')
 def typed_equal(n,t):
  while names[n][0]!='anonymous':
   k,pre,v=names[n]
   require(type(t)is list and len(t)==3 and t[0]==k and t[2]==v,'typed Name leaf')
   n,t=pre,t[1]
  require(t==['anonymous'],'typed Name root')
 with tempfile.TemporaryDirectory(prefix='matched-init-audit-',dir=d) as temp:
  db=sqlite3.connect(str(Path(temp)/'shapes.sqlite'))
  db.execute('PRAGMA cache_size=-2048');db.execute('CREATE TABLE ci(n INTEGER PRIMARY KEY,shape TEXT NOT NULL)')
  def add(k,p):
   try:db.execute('INSERT INTO ci VALUES (?,?)',(p['name'],canonical(dict(kind=k,payload=p))))
   except sqlite3.IntegrityError:raise ValueError('duplicate declaration')
  meta=0;decl_count=0
  for row in records(d/'kernel.ndjson'):
   if 'meta'in row:
    require(row['meta']['lean']['githash']==PIN,'kernel source pin');meta+=1
   elif 'in'in row:
    i=row['in'];require(i==len(names),'name order')
    if 'str'in row:
     v=row['str'];pre=v['pre'];require(0<=pre<len(names),'Name parent');names.append(('str',pre,v['str']))
    else:
     v=row['num'];pre=v['pre'];require(0<=pre<len(names),'Name parent');names.append(('num',pre,str(v['i'])))
   elif 'il'in row:
    i=row['il'];mark(levels,i,'level')
    for k in ['succ','max','imax']:
     if k in row:
      v=row[k]
      if isinstance(v,dict):
       for x in v.values():has(levels,x,'level child')
      elif isinstance(v,list):
       for x in v:has(levels,x,'level child')
      else:has(levels,v,'level child')
   elif 'ie'in row:
    i=row['ie'];mark(exprs,i,'expression')
    for k,fields in {'app':['fn','arg'],'lam':['type','body'],'forallE':['type','body'],'letE':['type','value','body'],'proj':['struct']}.items():
     if k in row:
      for f in fields:has(exprs,row[k][f],'expression child')
    if 'sort'in row:has(levels,row['sort'],'sort level')
    if 'const'in row:
     dependencies.add(row['const']['name'])
     for l in row['const']['us']:has(levels,l,'constant level')
   elif 'inductive'in row:
    for key,k in [('types','inductive'),('ctors','ctor'),('recs','rec')]:
     for p in row['inductive'][key]:add(k,p);decl_count+=1
   else:
    require(len(row)==1 and next(iter(row))in {'axiom','def','thm','opaque','quot'},'kernel record kind')
    k,p=next(iter(row.items()));add(k,p);decl_count+=1
  require(meta==1 and decl_count==65994,'kernel complete domain')
  db.commit()
  domain={r[0] for r in db.execute('SELECT n FROM ci')}
  require(dependencies<=domain,'constant dependency closure')
  occurrences={root:bytearray(n)for root,n in selected.items()};first={};last={};last_origin={};winner_by_name={};selected_names=set();duplicates=0
  cor=records(d/'correspondence.jsonl');head=next(cor)
  require(head['schema']=='matched-default-init-source-correspondence/1' and head['constantCount']==65994 and head['occurrenceCount']==66124 and head['quotInit'] and head['bodyPolicy']=='full','correspondence profile')
  quot=0
  for row in cor:
   shape=row['shape'];p=shape['payload'];n=p['name'];typed_equal(n,row['typedName'])
   origin=row['source'];root=origin['sourcePartRoot'];i=origin['sourceCIIndex'];module=origin['moduleIndex']
   require(0<=module<631 and source['modules'][module]['selectedRoot']==root,'source occurrence module/root')
   require(root in occurrences and 0<=i<len(occurrences[root]) and not occurrences[root][i],'source occurrence index')
   occurrences[root][i]=1
   if n not in first:first[n]=origin
   else:
    duplicates+=1
    old=last[n]
    # This pinned census contains only theorem/theorem duplicates. Full type
    # shape equality is deliberately stronger than the source alpha-equality.
    require((shape['kind'],p['type'],tuple(p['levelParams']),tuple(p.get('all',[])))==old and old[0]=='thm','pinned theorem subsumption')
   last[n]=(shape['kind'],p['type'],tuple(p['levelParams']),tuple(p.get('all',[])))
   last_origin[n]=origin
   require(row['firstAttribution']==first[n],'first attribution')
   if n in winner_by_name:require(row['winner']==winner_by_name[n],'winner disagreement')
   winner_by_name[n]=row['winner']
   if row['selected']:
    require(n not in selected_names and origin==row['winner'],'winner selected once');selected_names.add(n)
    require(canonical(shape)==db.execute('SELECT shape FROM ci WHERE n=?',(n,)).fetchone()[0],'full selected checking shape')
   has(exprs,p['type'],'declaration type')
   if 'value'in p:has(exprs,p['value'],'full declaration body')
   for u in p['levelParams']:require(0<=u<len(names),'level parameter name')
   for f in p.get('all',[]):require(f in domain,'family closure')
   if shape['kind']=='inductive':
    for c in p['ctors']:
     v=json.loads(db.execute('SELECT shape FROM ci WHERE n=?',(c,)).fetchone()[0]);require(v['kind']=='ctor' and v['payload']['induct']==n,'constructor family')
   if shape['kind']=='ctor':
    v=json.loads(db.execute('SELECT shape FROM ci WHERE n=?',(p['induct'],)).fetchone()[0]);require(v['kind']=='inductive' and n in v['payload']['ctors'],'constructor parent')
   if shape['kind']=='rec':
    for r in p['rules']:has(exprs,r['rhs'],'recursor body');require(r['ctor']in domain,'recursor constructor')
   if shape['kind']=='quot':quot+=1
  require(set(first)==domain==selected_names and duplicates==130 and quot==4,'correspondence inventory')
  require(all(all(bits) for bits in occurrences.values()),'complete per-module source occurrence inventory')
  for n,winner in winner_by_name.items():
   require(winner==last_origin[n],'last subsuming theorem selected')
  db.close()
 scalar=json.loads((d/'typed-scalars.json').read_text())
 require(scalar['schema']=='matched-init-typed-scalars/1' and scalar['graphNodes']==transport['inventory']['nodes'],'typed scalar graph coupling')
 claims=scalar_claims(scalar)
 actual={};node_count=refs=imms=0;N=transport['inventory']['nodes']
 for node in records(d/'module-data.jsonl'):
  if node.get('kind')=='manifest':continue
  require(node['id']==node_count,'transport node order');node_count+=1
  for i,e in enumerate(node.get('fields',[])):
   require(len(e)==1,'edge shape')
   if 'ref'in e:require(0<=e['ref']<N,'transport reference');refs+=1
   else:
    require('immediate'in e and int(e['immediate'])>=0,'transport immediate');imms+=1
    if int(e['immediate'])>2147483647:actual[(node['id'],i)]=e['immediate']
 require(actual==claims and len(claims)==scalar['claimCount'],'complete typed scalar coverage')
 refs+=int('ref'in transport['root']);imms+=int('immediate'in transport['root'])
 require(node_count==N and refs==transport['inventory']['referenceOccurrences'] and imms==transport['inventory']['immediateOccurrences'],'native graph census')
 result={'schema':'matched-default-init-pair-audit/1','declarations':decl_count,'occurrences':66124,'duplicates':duplicates,'modules':631,'parts':3155,'names':len(names),'levels':sum(levels),'expressions':sum(exprs),'moduleDataRecords':N,'typedScalarClaims':len(claims),'typedIntClaims':sum(c['domain']=='Int' for c in scalar['claims']),'checkingShapesEqual':True,'completeOccurrenceInventory':True,'lastSubsumingWinner':True,'firstAttribution':True,'dependencyClosure':True,'familyClosure':True,'typedNameCollisionFree':True,'quotInit':True,'fullBodies':True,'nativeGraphCloneVerification':False,'proofReplay':False,'guestFinalizationAccepted':False,'initializerExecutionObserved':False,'nativePairReceiptSHA256':sha(d/'native-pair-receipt.json'),'auditSourceSHA256':sha(Path(__file__))}
 (d/'pair-audit.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 return result
if __name__=='__main__':print(json.dumps(audit(sys.argv[1]),indent=2))
