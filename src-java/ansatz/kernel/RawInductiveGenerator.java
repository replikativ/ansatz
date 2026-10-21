package ansatz.kernel;

import java.util.*;
import clojure.lang.Keyword;

/** Source-only inductive admission. Unlike the imported-bundle checker, this
 * computes metadata and a complete recursor family from source descriptors.
 * Current profile: safe, non-nested families. Nested occurrences are discovered
 * from syntax and fail closed; no caller-provided numNested is accepted.
 */
public final class RawInductiveGenerator {
    private RawInductiveGenerator() {}
    private static final Object DEFAULT = Keyword.intern(null, "default");
    private static final Object IMPLICIT = Keyword.intern(null, "implicit");
    public static final class Constructor {
        public final Name name; public final Expr type;
        public Constructor(Name name, Expr type) { this.name=name; this.type=type; }
    }
    public static final class Type {
        public final Name name; public final Expr type; public final Constructor[] constructors;
        public Type(Name name, Expr type, Constructor[] constructors) {
            this.name=name; this.type=type; this.constructors=constructors.clone();
        }
    }
    public static final class Source {
        public final Name[] levelParams; public final int numParams;
        public final Type[] types; public final boolean isUnsafe;
        public Source(Name[] levelParams, int numParams, Type[] types, boolean isUnsafe) {
            this.levelParams=levelParams.clone(); this.numParams=numParams;
            this.types=types.clone(); this.isUnsafe=isUnsafe;
        }
    }
    public static final class Result {
        public final Env env; public final ConstantInfo[] constants;
        Result(Env env, ConstantInfo[] constants) { this.env=env; this.constants=constants.clone(); }
    }
    private static final class Budget {
        long left; Budget(long fuel) { if(fuel<1) throw fail("invalid generation fuel"); left=fuel; }
        void tick() { if(--left<0) throw fail("source inductive traversal fuel exhausted"); }
    }
    private static final class At {
        final Expr e; final int depth;
        At(Expr e,int depth) { this.e=e; this.depth=depth; }
    }
    private static RuntimeException fail(String message) { return new IllegalArgumentException(message); }
    private static Name recName(Name name) { return Name.mkStr(name,"rec"); }
    private static boolean reserved(Name name) {
        for(Name p=name;p!=null && p.tag!=Name.ANONYMOUS;p=p.prefix)
            if(p.tag==Name.STR && "_nested".equals(p.str)) return true;
        return false;
    }
    private static void reserve(Env env, Set<Name> used, Name name) {
        if(name==null || name.tag==Name.ANONYMOUS || reserved(name)) throw fail("invalid/reserved source inductive name");
        if(!used.add(name) || env.lookup(name)!=null) throw fail("source inductive name collision: "+name);
    }
    private static void children(Deque<At> work, Expr e, int depth) {
        switch(e.tag) {
        case Expr.APP: work.push(new At((Expr)e.o1,depth)); work.push(new At((Expr)e.o0,depth)); break;
        case Expr.LAM: case Expr.FORALL:
            work.push(new At((Expr)e.o2,depth+1)); work.push(new At((Expr)e.o1,depth)); break;
        case Expr.LET:
            work.push(new At((Expr)e.o3,depth+1)); work.push(new At((Expr)e.o2,depth)); work.push(new At((Expr)e.o1,depth)); break;
        case Expr.MDATA: case Expr.PROJ: work.push(new At((Expr)e.o1,depth)); break;
        default: break;
        }
    }
    private static Expr head(Expr e) { while(e.tag==Expr.APP)e=(Expr)e.o0; return e; }
    private static Expr[] args(Expr e) {
        ArrayList<Expr> out=new ArrayList<>();
        while(e.tag==Expr.APP) { out.add((Expr)e.o1); e=(Expr)e.o0; }
        Collections.reverse(out); return out.toArray(new Expr[0]);
    }
    private static Expr app(Expr e,Collection<Expr> args) { for(Expr a:args)e=Expr.app(e,a); return e; }
    private static boolean occurs(Expr root,Set<Name> names,Budget budget) {
        Deque<At> work=new ArrayDeque<>(); work.push(new At(root,0));
        while(!work.isEmpty()) {
            budget.tick(); At a=work.pop(); Expr e=a.e;
            if(e.tag==Expr.CONST && names.contains((Name)e.o0))return true;
            children(work,e,a.depth);
        }
        return false;
    }
    private static void preflight(Expr root,Set<Name> names,Object[] levels,int np,boolean uniform,Budget budget) {
        if(root==null || root.bvarRange()!=0)throw fail("source inductive expression must be closed");
        Deque<At> work=new ArrayDeque<>(); work.push(new At(root,0));
        while(!work.isEmpty()) {
            budget.tick(); At a=work.pop(); Expr e=a.e;
            if(e.tag==Expr.FVAR || e.tag==Expr.MVAR || e.hasMVar())throw fail("unresolved source inductive variable");
            if((e.tag==Expr.CONST || e.tag==Expr.PROJ) && reserved((Name)e.o0))throw fail("reserved nested auxiliary reference");
            Expr fn=head(e);
            if(uniform && fn.tag==Expr.CONST && names.contains((Name)fn.o0)) {
                Expr[] as=args(e);
                if(as.length<=np) {
                    boolean ok=as.length==np && a.depth>=np && Expr.levelsEquals(fn.o1,levels);
                    for(int i=0;ok && i<np;i++)ok=as[i].tag==Expr.BVAR && as[i].longVal==a.depth-1-i;
                    if(!ok)throw fail("nonuniform syntactic occurrence of source inductive: "+fn.o0);
                    continue;
                }
            }
            // Discover nested containers independently of caller metadata, even
            // if a later beta/definition reduction could erase this occurrence.
            if(uniform && e.tag==Expr.APP && fn.tag==Expr.CONST && !names.contains((Name)fn.o0)) {
                for(Expr arg:args(e)) if(occurs(arg,names,budget))
                    throw fail("nested source inductive generation is not implemented");
            }
            children(work,e,a.depth);
        }
    }
    private static LocalDecl fresh(TypeChecker tc,Expr pi,long[] next) {
        long id=next[0]++;
        Expr type=TypeChecker.consumeTypeAnnotations((Expr)pi.o1);
        tc.addLocalDecl(id,pi.o0,type);
        return new LocalDecl(id,pi.o0,type,pi.o3);
    }
    private static TypeChecker checker(Env env,Object[] levels,long fuel) {
        TypeChecker tc=new TypeChecker(env,TypeChecker.DEFN_SAFE,levels); tc.setFuel(fuel); return tc;
    }
    private static void addLocals(TypeChecker tc,List<LocalDecl> locals) {
        for(LocalDecl l:locals)tc.addLocalDecl(l.id,l.name,l.type);
    }
    private static List<Expr> values(List<LocalDecl> locals) {
        ArrayList<Expr> out=new ArrayList<>();for(LocalDecl l:locals)out.add(l.fvar);return out;
    }
    private static boolean explicit(Object info) { return info==null || DEFAULT.equals(info); }
    private static boolean hasLoose(Expr e,int index,Budget budget) {
        Deque<At> work=new ArrayDeque<>();work.push(new At(e,0));
        while(!work.isEmpty()) {budget.tick();At a=work.pop();
            if(a.e.tag==Expr.BVAR && a.e.longVal==index+a.depth)return true;
            children(work,a.e,a.depth);
        }return false;
    }
    private static boolean inDomain(Expr body,int index,Budget budget) {
        // Native has_loose_bvars_in_domain(...,strict=true), including implicit
        // transitivity. A result-only dependency does not make a binder implicit.
        while(body.tag==Expr.FORALL) {
            budget.tick();
            if(hasLoose((Expr)body.o1,index,budget) &&
               (explicit(body.o3) || inDomain((Expr)body.o2,0,budget)))return true;
            body=(Expr)body.o2;index++;
        }return false;
    }
    private static Expr inferImplicit(Expr type,int motivesStart,int numMotives,Budget budget) {
        ArrayList<Expr> binders=new ArrayList<>();Expr body=type;
        while(body.tag==Expr.FORALL) {budget.tick();binders.add(body);body=(Expr)body.o2;}
        for(int i=binders.size()-1;i>=0;i--) {
            Expr b=binders.get(i);
            // Existing import-oriented generator starts motives implicit. Native
            // starts them explicit and infers implicitness only from later domains;
            // an EMPTY family's motive must therefore remain explicit.
            Object info=(i>=motivesStart && i<motivesStart+numMotives)?DEFAULT:b.o3;
            if(explicit(info)&&inDomain(body,0,budget))info=IMPLICIT;
            body=Expr.forall(b.o0,(Expr)b.o1,body,info);
        }return body;
    }
    private static boolean propOnly(Env env,InductiveBundle bundle,Level result,List<LocalDecl> params,long[] next,long fuel) {
        if(Level.isNeverZero(result))return false;
        if(bundle.inductives.length>1 || bundle.ctors.length>1)return true;
        if(bundle.ctors.length==0)return false;
        TypeChecker tc=checker(env,bundle.levelParams,fuel);addLocals(tc,params);
        ArrayList<Expr> relevant=new ArrayList<>();Expr t=bundle.ctors[0].type;int n=0;
        while(t.tag==Expr.FORALL) {
            LocalDecl local=fresh(tc,t,next);
            if(n>=bundle.numParams) {
                Expr sort=tc.ensureSortExpr(tc.check((Expr)t.o1));
                if(!Level.eq((Level)sort.o0,Level.ZERO_LEVEL))relevant.add(local.fvar);
            }
            t=Reducer.instantiate1((Expr)t.o2,local.fvar);n++;
        }
        Expr[] resultArgs=args(t);
        for(Expr needed:relevant) {
            boolean found=false;for(Expr a:resultArgs)if(TypeChecker.exprDeepEquals(needed,a)){found=true;break;}
            if(!found)return true;
        }return false;
    }
    /** Atomically generate a complete safe ordinary/mutual family. No source
     * result is exposed before strict bundle AND computation checks pass. */
    public static Result generate(Env base,Source source,long fuel) {
        Budget budget=new Budget(fuel);
        if(base==null || source==null || source.numParams<0 || source.types.length==0)throw fail("invalid source inductive block");
        if(source.isUnsafe)throw fail("unsafe source inductive generation is not implemented");
        Object[] lps=source.levelParams.clone();Object[] levels=new Object[lps.length];
        Set<Name> univs=new HashSet<>(), names=new LinkedHashSet<>(), used=new HashSet<>();
        for(int i=0;i<lps.length;i++) { Name n=(Name)lps[i];if(n==null || !univs.add(n))throw fail("duplicate/invalid source universe parameter");levels[i]=Level.param(n); }
        for(Type t:source.types) {if(t==null)throw fail("null source inductive");reserve(base,used,t.name);names.add(t.name);reserve(base,used,recName(t.name));}
        for(Type t:source.types)for(Constructor c:t.constructors) {if(c==null)throw fail("null source constructor");reserve(base,used,c.name);}
        for(Type t:source.types) {
            preflight(t.type,names,levels,source.numParams,false,budget);
            for(Constructor c:t.constructors)preflight(c.type,names,levels,source.numParams,true,budget);
        }
        int[] indices=new int[source.types.length];long[] next={1};
        ArrayList<LocalDecl> params=new ArrayList<>();Level resultLevel=null;
        for(int i=0;i<source.types.length;i++) {
            Type t=source.types[i];TypeChecker tc=checker(base,lps,fuel);addLocals(tc,params);
            tc.ensureSortExpr(tc.check(t.type));Expr body=tc.whnfExpr(t.type);int n=0;
            while(body.tag==Expr.FORALL) {
                LocalDecl local;
                if(n<source.numParams && i>0) {
                    local=params.get(n);
                    if(!tc.isDefEq((Expr)body.o1,local.type))throw fail("source inductive parameters differ");
                } else {local=fresh(tc,body,next);if(n<source.numParams)params.add(local);}
                body=tc.whnfExpr(Reducer.instantiate1((Expr)body.o2,local.fvar));n++;
            }
            if(n<source.numParams)throw fail("source inductive has too few parameters");
            indices[i]=n-source.numParams;Level level=(Level)tc.ensureSortExpr(body).o0;
            if(resultLevel==null)resultLevel=level;else if(!Level.eq(resultLevel,level))throw fail("source inductive result universes differ");
        }
        boolean recursive=false,reflexive=false;
        for(Type t:source.types)for(Constructor c:t.constructors) {
            Expr body=c.type;
            while(body.tag==Expr.FORALL) {
                Expr domain=(Expr)body.o1;
                if(occurs(domain,names,budget)) {recursive=true;if(domain.tag==Expr.FORALL)reflexive=true;}
                body=(Expr)body.o2;
            }
        }
        ConstantInfo[] inds=new ConstantInfo[source.types.length];ArrayList<ConstantInfo> ctors=new ArrayList<>();
        Object[] all=names.toArray();
        for(int i=0;i<source.types.length;i++) {
            Type t=source.types[i];Name[] ctorNames=new Name[t.constructors.length];
            for(int j=0;j<t.constructors.length;j++)ctorNames[j]=t.constructors[j].name;
            inds[i]=ConstantInfo.mkInduct(t.name,lps,t.type,source.numParams,indices[i],all,ctorNames,0,recursive,reflexive,false);
            for(int j=0;j<t.constructors.length;j++) {
                Constructor c=t.constructors[j];int arity=0;Expr b=c.type;
                while(b.tag==Expr.FORALL){arity++;b=(Expr)b.o2;}
                if(arity<source.numParams)throw fail("source constructor has too few parameters");
                Expr returnHead=head(b); Expr[] returnArgs=args(b);
                if(returnHead.tag!=Expr.CONST || !t.name.equals(returnHead.o0) ||
                   !Expr.levelsEquals(returnHead.o1,levels) || returnArgs.length!=source.numParams+indices[i])
                    throw fail("invalid manifest source constructor return parent/type: "+c.name);
                ctors.add(ConstantInfo.mkCtor(c.name,lps,c.type,t.name,j,source.numParams,arity-source.numParams,false));
            }
        }
        InductiveBundle derived=new InductiveBundle(lps,source.numParams,false,inds,ctors.toArray(new ConstantInfo[0]),new ConstantInfo[0]);
        Env temporary=base;for(ConstantInfo ind:inds)temporary=temporary.addConstant(ind);
        for(ConstantInfo ctor:ctors) {TypeChecker.checkConstructorDeclaration(temporary,ctor,fuel);temporary=temporary.addConstant(ctor);}
        Level elim;
        if(propOnly(temporary,derived,resultLevel,params,next,fuel))elim=Level.ZERO_LEVEL;
        else {Name n=Name.fromString("u");int i=1;while(univs.contains(n))n=Name.fromString("u").appendAfter(i++);elim=Level.param(n);}
        boolean kTarget=inds.length==1 && Level.ZERO_LEVEL.equals(resultLevel) && ctors.size()==1 && ctors.get(0).numFields==0;
        Expr[] indConsts=new Expr[inds.length];for(int i=0;i<inds.length;i++)indConsts[i]=Expr.mkConst(inds[i].name,levels,levels.length>0);
        RecursorGenerator generator=new RecursorGenerator(temporary,derived,fuel,levels,levels.length>0,params,indices,indConsts,elim,kTarget,next[0]);
        generator.mkRecInfos();ConstantInfo[] generated=generator.generateRecursors();
        ConstantInfo[] recs=new ConstantInfo[generated.length];
        for(int i=0;i<recs.length;i++) {
            ConstantInfo c=generated[i];
            recs[i]=ConstantInfo.mkRecursor(c.name,c.levelParams,inferImplicit(c.type,c.numParams,c.numMotives,budget),c.all,c.numParams,c.numIndices,c.numMotives,c.numMinors,c.rules,kTarget,false);
        }
        InductiveBundle complete=new InductiveBundle(lps,source.numParams,false,inds,derived.ctors,recs);
        Env checked=TypeChecker.checkInductiveBundle(base,complete,fuel);
        for(ConstantInfo rec:recs)checkComputations(checked,rec,complete,fuel,budget);
        ArrayList<ConstantInfo> constants=new ArrayList<>();Collections.addAll(constants,inds);constants.addAll(ctors);Collections.addAll(constants,recs);
        return new Result(checked,constants.toArray(new ConstantInfo[0]));
    }
    private static void checkComputations(Env env,ConstantInfo rec,InductiveBundle bundle,long fuel,Budget budget) {
        // Independent native-style lhs vs reduct type check. Merely checking a
        // RHS has SOME type misses under-applied minor premises.
        TypeChecker typeChecker=checker(env,rec.levelParams,fuel);typeChecker.ensureSortExpr(typeChecker.check(rec.type));
        Object[] recLevels=new Object[rec.levelParams.length];for(int i=0;i<recLevels.length;i++)recLevels[i]=Level.param((Name)rec.levelParams[i]);
        Object[] indLevels=new Object[bundle.levelParams.length];for(int i=0;i<indLevels.length;i++)indLevels[i]=Level.param((Name)bundle.levelParams[i]);
        for(ConstantInfo ctor:bundle.ctors) {
            if(!Name.mkStr(ctor.inductName,"rec").equals(rec.name))continue;
            TypeChecker tc=checker(env,rec.levelParams,fuel);long[] next={1};
            Expr t=rec.type;ArrayList<Expr> prefix=new ArrayList<>();
            for(int i=0;i<rec.numParams+rec.numMotives+rec.numMinors;i++) {
                budget.tick();if(t.tag!=Expr.FORALL)throw fail("malformed generated recursor telescope");
                LocalDecl local=fresh(tc,t,next);prefix.add(local.fvar);t=Reducer.instantiate1((Expr)t.o2,local.fvar);
            }
            List<Expr> params=prefix.subList(0,rec.numParams);Expr ctorType=ctor.type;
            for(Expr param:params) {if(ctorType.tag!=Expr.FORALL)throw fail("malformed constructor parameters");ctorType=Reducer.instantiate1((Expr)ctorType.o2,param);}
            ArrayList<Expr> fields=new ArrayList<>();
            while(ctorType.tag==Expr.FORALL) {
                budget.tick();LocalDecl local=fresh(tc,ctorType,next);fields.add(local.fvar);ctorType=Reducer.instantiate1((Expr)ctorType.o2,local.fvar);
            }
            Expr[] resultArgs=args(tc.whnfExpr(ctorType));
            if(resultArgs.length!=rec.numParams+rec.numIndices)throw fail("generated computation constructor index count differs");
            Expr intro=app(app(Expr.mkConst(ctor.name,indLevels,indLevels.length>0),params),fields);
            Expr lhs=app(Expr.mkConst(rec.name,recLevels,recLevels.length>0),prefix);
            lhs=app(lhs,Arrays.asList(resultArgs).subList(rec.numParams,resultArgs.length));lhs=Expr.app(lhs,intro);
            Expr expected=tc.check(lhs);Expr reduct=tc.whnfExpr(lhs);Expr actual=tc.check(reduct);
            if(!tc.isDefEq(actual,expected))throw fail("generated recursor computation rule is not type-preserving: "+ctor.name);
        }
    }
}
