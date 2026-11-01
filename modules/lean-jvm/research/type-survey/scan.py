#!/usr/bin/env python3
"""Lexical Lean type-family census of immutable git snapshots, not elaborated types.
Reads blobs without checking out or building any project. Comments and strings are
masked; counts are per file and per declaration header, stratified by corpus.
"""
import argparse, collections, hashlib, json, re, subprocess
from pathlib import Path

FAMILIES={
 'Nat':{'Nat','ℕ'}, 'Int':{'Int','ℤ'}, 'Bool':{'Bool'}, 'String':{'String'}, 'Unit':{'Unit','PUnit'},
 'Float/Float32':{'Float','Float32'},
 'machine integers':{'UInt8','UInt16','UInt32','UInt64','USize','Int8','Int16','Int32','Int64','ISize'},
 'Char':{'Char'}, 'List':{'List'}, 'Array':{'Array'}, 'ByteArray':{'ByteArray'},
 'packed/scientific arrays':{'FloatArray','Float32Array','DataArray','DataArrayN','ScalarArray','Vec'},
 'Option':{'Option'}, 'Prod/tuples':{'Prod','PProd','×'}, 'Sum/Except':{'Sum','PSum','Except','EExcept','⊕'},
 'Fin/BitVec':{'Fin','BitVec'}, 'Subtype/Vector':{'Subtype','Vector'}, 'Rat':{'Rat','ℚ'},
 'Real/Complex specifications':{'Real','Complex','ℝ','ℂ'},
 'maps/sets':{'HashMap','DHashMap','HashSet','TreeMap','DTreeMap','TreeSet','RBMap','RBSet','PersistentHashMap','PersistentHashSet','NameMap','NameSet'},
 'mathematical sets':{'Finset','Set'},
 'JSON':{'Json','JsonNumber','JSON'}, 'IO/EIO/BaseIO':{'IO','EIO','BaseIO'},
 'monad transformers/runners':{'ReaderT','ReaderM','StateT','StateM','StateRefT','StateRefT\'','ExceptT','OptionT','EStateM','CoreM','MetaM','TermElabM','CommandElabM','TelemetryT'},
 'async/resources':{'Task','Promise','Async','ContextAsync','Mutex','Condvar','Channel','Socket','Handle','Stream','Conn'},
 'paths/time/URI':{'FilePath','URI','DateTime','Timestamp','Millisecond','Nanosecond','Duration'},
 'metaprogramming values':{'Name','Syntax','Expr','Level','Environment','MessageData','TSyntax'},
}
TOKEN=re.compile(r"(?:[^\W\d]\w*'?)(?:\.(?:[^\W\d]\w*'?))*|[×⊕]",re.UNICODE)
COMMAND=re.compile(r"(?m)^([ \t]{0,4})(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec|local|scoped)\s+)*(def|abbrev|opaque|structure|inductive|class|instance|theorem|lemma|example)\b")


def git(repo,*args): return subprocess.check_output(['git','-C',str(repo),*args])

def mask(text):
    out=[]; index=0; depth=0; quoted=False
    while index<len(text):
        c=text[index]; pair=text[index:index+2]
        if depth:
            if pair=='/-': depth+=1; out.extend('  '); index+=2
            elif pair=='-/': depth-=1; out.extend('  '); index+=2
            else: out.append('\n' if c=='\n' else ' '); index+=1
        elif quoted:
            if c=='\\' and index+1<len(text): out.extend('  '); index+=2
            else:
                if c=='"': quoted=False
                out.append('\n' if c=='\n' else ' '); index+=1
        elif pair=='/-': depth=1; out.extend('  '); index+=2
        elif pair=='--':
            stop=text.find('\n',index)
            if stop<0: stop=len(text)
            out.extend(' '*(stop-index)); index=stop
        elif c=='"': quoted=True; out.append(' '); index+=1
        elif c=="'" and index+2<len(text) and text[index+2]=="'": out.extend('   '); index+=3
        else: out.append(c); index+=1
    return ''.join(out)

def mentions(text):
    names=set()
    for token in TOKEN.findall(text): names.update(token.split('.'))
    return {family for family,aliases in FAMILIES.items() if names&aliases}

def header_end(text,start,stop):
    depth=0; index=start
    while index<stop:
        c=text[index]
        if c in '([{': depth+=1
        elif c in ')]}': depth=max(0,depth-1)
        if depth==0 and (text.startswith(':=',index) or re.match(r'where\b',text[index:index+6])): return index
        if depth==0 and c=='\n' and re.match(r'[ \t]*\|',text[index+1:stop]): return index
        index+=1
    return stop

def declarations(text):
    commands=list(COMMAND.finditer(text))
    for i,match in enumerate(commands):
        stop=commands[i+1].start() if i+1<len(commands) else len(text)
        kind=match.group(2); start=match.end()
        if kind in {'structure','inductive','class'}:
            body=text[start:stop]
        else: body=text[start:header_end(text,start,stop)]
        # Exclude declaration names themselves from the annotation counts.
        body=re.sub(r"^\s*(?:[^\W\d]\w*'?)(?:\.(?:[^\W\d]\w*'?))*",'',body,count=1)
        yield kind,text.count('\n',0,match.start())+1,mentions(body)

def paths(repo,commit,prefixes,exclude):
    all_paths=git(repo,'ls-tree','-r','-z','--name-only',commit).decode().split('\0')
    return [p for p in all_paths if p.endswith('.lean') and not p.endswith('/lakefile.lean') and p!='lakefile.lean'
            and any(p.startswith(prefix) for prefix in prefixes) and not any(p.startswith(prefix) for prefix in exclude)]

def survey(repo,commit,prefixes,exclude):
    selected=paths(repo,commit,prefixes,exclude)
    process=subprocess.Popen(['git','-C',str(repo),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    counts={family:collections.Counter() for family in FAMILIES}; samples={family:[] for family in FAMILIES}
    kinds=collections.Counter(); byte_count=0; records=0; skipped=[]
    try:
        for relative in selected:
            assert '\n' not in relative
            process.stdin.write((commit+':'+relative+'\n').encode());process.stdin.flush()
            fields=process.stdout.readline().decode().split(); assert len(fields)==3 and fields[1]=='blob'
            size=int(fields[2]); raw=process.stdout.read(size);assert process.stdout.read(1)==b'\n'
            if size>8*1024*1024: skipped.append(relative);continue
            byte_count+=size; source=mask(raw.decode('utf-8'))
            for family in mentions(source): counts[family]['codeFiles']+=1
            file_definition=set(); file_data=set()
            for kind,line,families in declarations(source):
                kinds[kind]+=1
                bucket='proofHeaders' if kind in {'theorem','lemma','example'} else 'dataDeclarations' if kind in {'structure','inductive','class'} else 'definitionHeaders'
                for family in families:
                    counts[family][bucket]+=1
                    if bucket=='definitionHeaders': file_definition.add(family)
                    if bucket=='dataDeclarations': file_data.add(family)
                    if bucket!='proofHeaders' and len(samples[family])<5:
                        samples[family].append({'path':relative,'line':line,'kind':kind})
            for family in file_definition: counts[family]['definitionFiles']+=1
            for family in file_data: counts[family]['dataFiles']+=1
    finally:
        process.stdin.close();process.stdout.close();assert process.wait()==0
    return {'commit':commit,'prefixes':prefixes,'excludePrefixes':exclude,'files':len(selected)-len(skipped),'sourceBytes':byte_count,'skippedOversizedFiles':skipped,'declarationKinds':dict(kinds),'families':{family:dict(counts[family]) for family in FAMILIES},'examples':samples}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--development',type=Path,required=True);parser.add_argument('--web-app',type=Path,required=True);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    dev=args.development; pin='819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
    configs=[('lean-init-std',dev/'lean4',pin,['src/Init/','src/Std/'],[]),('lean-metaprogramming',dev/'lean4',pin,['src/Lean/'],[]),('lean-compile-benchmarks',dev/'lean4',pin,['tests/compile_bench/'],[]),('scilean-library',dev/'scilean',None,['SciLean/'],[]),('scilean-examples',dev/'scilean',None,['examples/'],[]),('mcmc-executable',dev/'mcmc-lean',None,['formal/Mcmc/Executable/','formal/Mcmc/Oracle.lean'],[]),('mcmc-formal',dev/'mcmc-lean',None,['formal/Mcmc/'],['formal/Mcmc/Executable/','formal/Mcmc/Oracle.lean']),('mathlib-data-probability',dev/'mathlib4',None,['Mathlib/Data/','Mathlib/Probability/'],[]),('todomvc-app',args.web_app,None,[''],[])]
    result={'schema':'lean-type-family-lexical-survey/1','method':'Immutable git source snapshots; nested comments and strings masked. Per-file and declaration-header mentions, not elaborated type frequencies or execution coverage. Data declarations include constructor/field bodies. Names are not resolved; families overlap. Definitions may be noncomputable, proofs or stale code. Corpora are purposive, not a representative random sample of Lean projects.','scannerSHA256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'familyTokens':{name:sorted(tokens) for name,tokens in FAMILIES.items()},'corpora':{}}
    for name,repo,commit,prefixes,exclude in configs:
        commit=commit or git(repo,'rev-parse','HEAD').decode().strip()
        result['corpora'][name]=survey(repo,commit,prefixes,exclude)
        for toolchain in ['lean-toolchain','formal/lean-toolchain']:
            exists=subprocess.run(['git','-C',str(repo),'cat-file','-e',commit+':'+toolchain],capture_output=True).returncode==0
            if exists:
                result['corpora'][name]['toolchainSource']=toolchain
                result['corpora'][name]['toolchain']=git(repo,'show',commit+':'+toolchain).decode().strip()
                break
        print(name,result['corpora'][name]['files'],'files',flush=True)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print('Wrote',args.output)

if __name__=='__main__': main()
