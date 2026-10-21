package ansatz.kernel;

import java.util.*;

/** Additive, deliberately bounded source-nesting experiment. The accepted
 * profile is one parameter-free Type with first-order recursion through one
 * checked unary, unindexed, non-mutual container (List-style constructors).
 * Provisional metadata is private to discovery; only the fully restored and
 * checked immutable result escapes. The ordinary source generator is unchanged.
 */
public final class RawNestedInductiveGenerator {
    private RawNestedInductiveGenerator() {}
    public static final class Result {
        public final Env env;
        public final ConstantInfo[] constants;
        public final int numNested;
        Result(Env env,ConstantInfo[] constants,int numNested) {
            this.env=env;this.constants=constants.clone();this.numNested=numNested;
        }
    }
    private static RuntimeException fail(String s) { return new IllegalArgumentException(s); }
    private static Expr head(Expr e) { while(e.tag==Expr.APP)e=(Expr)e.o0;return e; }
    private static Expr[] args(Expr e) {
        ArrayList<Expr> a=new ArrayList<>();while(e.tag==Expr.APP){a.add((Expr)e.o1);e=(Expr)e.o0;}
        Collections.reverse(a);return a.toArray(new Expr[0]);
    }
    private static boolean named(Expr e,Name name) {
        return e.tag==Expr.CONST && name.equals(e.o0) && Expr.levelsEquals(e.o1,new Object[0]);
    }
    private static boolean type(Expr e) {
        return e.tag==Expr.SORT && Level.eq((Level)e.o0,Level.succ(Level.ZERO_LEVEL));
    }
    private static boolean param(Expr e,int depth) { return e.tag==Expr.BVAR && e.longVal==depth-1; }
    private static boolean containerApp(Expr e,Name name,int depth) {
        Expr[] a=args(e);return named(head(e),name) && a.length==1 && param(a[0],depth);
    }
    private static void reserve(Env base,Set<Name> used,Name name) {
        if(name==null || name.tag==Name.ANONYMOUS || base.lookup(name)!=null || !used.add(name))
            throw fail("source nested name collision");
        for(Name p=name;p.tag!=Name.ANONYMOUS;p=p.prefix)
            if(p.tag==Name.STR && "_nested".equals(p.str))throw fail("reserved source nested name");
    }
    private static void validateContainer(Env base,ConstantInfo c,long fuel) {
        if(c==null || !c.isInduct() || c.numParams!=1 || c.numIndices!=0 || c.numNested!=0 ||
           c.isUnsafe || c.levelParams.length!=0 || c.all.length!=1 || !c.name.equals(c.all[0]) ||
           c.type.tag!=Expr.FORALL || !type((Expr)c.type.o1) || !type((Expr)c.type.o2))
            throw fail("nested source profile requires a checked unary first-order Type container");
        long left=fuel;
        for(Name ctorName:c.ctors) {
            ConstantInfo ctor=base.lookup(ctorName);
            if(ctor==null || !ctor.isCtor() || ctor.isUnsafe || ctor.numParams!=1 || !c.name.equals(ctor.inductName))
                throw fail("invalid source nesting container constructor");
            Expr t=ctor.type;
            if(t.tag!=Expr.FORALL || !type((Expr)t.o1))throw fail("invalid unary container parameter");
            t=(Expr)t.o2;int depth=1;
            while(t.tag==Expr.FORALL) {
                if(--left<0)throw fail("source nesting profile fuel exhausted");
                Expr d=(Expr)t.o1;
                if(!param(d,depth) && !containerApp(d,c.name,depth))
                    throw fail("nested source container field is outside first-order unary profile");
                t=(Expr)t.o2;depth++;
            }
            if(!containerApp(t,c.name,depth))throw fail("invalid unary container return");
        }
    }
    /** Pure syntactic route selection, never exception-driven fallback. */
    public static boolean hasNestedSource(RawInductiveGenerator.Source source,long fuel) {
        if(source==null || fuel<1)throw fail("invalid source nested discovery input");
        Set<Name> names=new HashSet<>();for(RawInductiveGenerator.Type t:source.types)names.add(t.name);
        ArrayDeque<Expr> work=new ArrayDeque<>();
        for(RawInductiveGenerator.Type t:source.types)for(RawInductiveGenerator.Constructor c:t.constructors)work.push(c.type);
        long left=fuel;
        while(!work.isEmpty()) {
            if(--left<0)throw fail("source nested discovery fuel exhausted");Expr e=work.pop(),fn=head(e);
            if(e.tag==Expr.APP && fn.tag==Expr.CONST && !names.contains((Name)fn.o0)) {
                ArrayDeque<Expr> args=new ArrayDeque<>();for(Expr arg:args(e))args.push(arg);
                while(!args.isEmpty()) {
                    if(--left<0)throw fail("source nested discovery fuel exhausted");Expr a=args.pop();
                    if(a.tag==Expr.CONST && names.contains((Name)a.o0))return true;
                    children(args,a);
                }
            }
            children(work,e);
        }
        return false;
    }
    private static void children(ArrayDeque<Expr> work,Expr e) {
        switch(e.tag) {
        case Expr.APP:work.push((Expr)e.o0);work.push((Expr)e.o1);break;
        case Expr.LAM:case Expr.FORALL:work.push((Expr)e.o1);work.push((Expr)e.o2);break;
        case Expr.LET:work.push((Expr)e.o1);work.push((Expr)e.o2);work.push((Expr)e.o3);break;
        case Expr.MDATA:case Expr.PROJ:work.push((Expr)e.o1);break;
        default:break;
        }
    }
    public static Result generate(Env base,RawInductiveGenerator.Source source,long fuel) {
        if(base==null || source==null || fuel<1 || source.isUnsafe || source.numParams!=0 ||
           source.levelParams.length!=0 || source.types.length!=1)
            throw fail("source nested profile requires one safe parameter-free Type");
        RawInductiveGenerator.Type t=source.types[0];
        if(!type(t.type))throw fail("source nested profile requires an unindexed Type header");
        Set<Name> used=new HashSet<>();reserve(base,used,t.name);reserve(base,used,Name.mkStr(t.name,"rec"));
        Name container=null;ArrayList<ConstantInfo> ctors=new ArrayList<>();long left=fuel;
        for(int i=0;i<t.constructors.length;i++) {
            RawInductiveGenerator.Constructor c=t.constructors[i];reserve(base,used,c.name);
            Expr body=c.type;int fields=0;
            while(body.tag==Expr.FORALL) {
                if(--left<0)throw fail("source nesting traversal fuel exhausted");
                Expr d=(Expr)body.o1;
                if(!named(d,t.name)) {
                    Expr fn=head(d);Expr[] as=args(d);
                    if(fn.tag!=Expr.CONST || !Expr.levelsEquals(fn.o1,new Object[0]) || as.length!=1 || !named(as[0],t.name))
                        throw fail("source nested field is outside first-order unary profile");
                    Name n=(Name)fn.o0;
                    if(container!=null && !container.equals(n))throw fail("multiple nesting containers are not implemented");
                    container=n;
                }
                fields++;body=(Expr)body.o2;
            }
            if(!named(body,t.name))throw fail("invalid source nested constructor return parent");
            ctors.add(ConstantInfo.mkCtor(c.name,new Object[0],c.type,t.name,i,0,fields,false));
        }
        if(container==null) {
            RawInductiveGenerator.Result ordinary=RawInductiveGenerator.generate(base,source,fuel);
            return new Result(ordinary.env,ordinary.constants,0);
        }
        validateContainer(base,base.lookup(container),fuel);
        // This internal flag only selects the existing discovery pass. It is
        // inferred from the exact raw field profile above, never supplied by
        // a caller and never used as final metadata or published to an Env.
        ConstantInfo provisional=ConstantInfo.mkInduct(t.name,new Object[0],t.type,0,0,
            new Object[]{t.name},Arrays.stream(t.constructors).map(c->c.name).toArray(Name[]::new),1,true,false,false);
        InductiveBundle raw=new InductiveBundle(new Object[0],0,false,new ConstantInfo[]{provisional},
            ctors.toArray(new ConstantInfo[0]),new ConstantInfo[0]);
        NestedElimResult discovery=NestedInductiveEliminator.eliminate(base,raw);
        if(discovery.auxNames.size()!=1 || discovery.auxBundle.inductives.length!=2)
            throw fail("source nested discovery exceeded unary profile");
        for(Name n:discovery.auxNames) {
            if(base.lookup(n)!=null)throw fail("temporary nested name collision");
            Name restored=discovery.auxRecToRestoredRec.get(Name.mkStr(n,"rec"));reserve(base,used,restored);
        }
        RawInductiveGenerator.Type[] auxTypes=new RawInductiveGenerator.Type[discovery.auxBundle.inductives.length];
        Map<Name,ConstantInfo> auxCtorMap=discovery.auxBundle.ctorMap();
        for(int i=0;i<auxTypes.length;i++) {
            ConstantInfo ind=discovery.auxBundle.inductives[i];
            RawInductiveGenerator.Constructor[] cs=new RawInductiveGenerator.Constructor[ind.ctors.length];
            for(int j=0;j<cs.length;j++){ConstantInfo c=auxCtorMap.get(ind.ctors[j]);cs[j]=new RawInductiveGenerator.Constructor(c.name,c.type);}
            auxTypes[i]=new RawInductiveGenerator.Type(ind.name,ind.type,cs);
        }
        RawInductiveGenerator.Result generated=RawInductiveGenerator.generate(base,
            new RawInductiveGenerator.Source(new Name[0],0,auxTypes,false),fuel);
        ConstantInfo[] auxRecs=Arrays.stream(generated.constants).filter(ConstantInfo::isRecursor).toArray(ConstantInfo[]::new);
        ConstantInfo[] restored=InductiveChecker.restoreGeneratedRecursors(raw,discovery,auxRecs);
        ConstantInfo finalInd=ConstantInfo.mkInduct(t.name,new Object[0],t.type,0,0,new Object[]{t.name},
            provisional.ctors,discovery.auxNames.size(),true,false,false);
        InductiveBundle complete=new InductiveBundle(new Object[0],0,false,new ConstantInfo[]{finalInd},raw.ctors,restored);
        InductiveChecker.compareRestoredImportedBundle(complete,discovery,auxRecs);
        Env checked=TypeChecker.checkInductiveBundle(base,complete,fuel);
        checkRestoredTerms(checked,complete,discovery,fuel);
        checkRestoredComputations(checked,generated,discovery,fuel);
        ArrayList<ConstantInfo> out=new ArrayList<>();out.add(finalInd);out.addAll(ctors);Collections.addAll(out,restored);
        return new Result(checked,out.toArray(new ConstantInfo[0]),discovery.auxNames.size());
    }
    private static void checkRestoredTerms(Env env,InductiveBundle bundle,NestedElimResult discovery,long fuel) {
        TypeChecker tc=new TypeChecker(env,TypeChecker.DEFN_SAFE,new Object[0]);tc.setFuel(fuel);
        for(Expr nested:discovery.nestedKeys)tc.check(nested);
        for(ConstantInfo c:bundle.ctors)tc.ensureSortExpr(tc.check(c.type));
        for(ConstantInfo rec:bundle.recursors) {
            TypeChecker recTc=new TypeChecker(env,TypeChecker.DEFN_SAFE,rec.levelParams);recTc.setFuel(fuel);
            recTc.ensureSortExpr(recTc.check(rec.type));
            for(ConstantInfo.RecursorRule rule:rec.rules)recTc.check(rule.rhs);
        }
        for(ConstantInfo c:bundle.inductives)checkNoAux(c.type,discovery,fuel);
        for(ConstantInfo c:bundle.ctors)checkNoAux(c.type,discovery,fuel);
        for(ConstantInfo c:bundle.recursors) {
            checkNoAux(c.type,discovery,fuel);
            for(ConstantInfo.RecursorRule rule:c.rules)checkNoAux(rule.rhs,discovery,fuel);
        }
    }

    private static void checkNoAux(Expr root,NestedElimResult discovery,long fuel) {
        ArrayDeque<Expr> work=new ArrayDeque<>();work.push(root);long left=fuel;
        while(!work.isEmpty()) {
            if(--left<0)throw fail("restored term traversal fuel exhausted");
            Expr e=work.pop();
            if(e.tag==Expr.CONST || e.tag==Expr.PROJ) {
                Name name=(Name)e.o0;
                for(Name p=name;p.tag!=Name.ANONYMOUS;p=p.prefix)
                    if(discovery.auxToNested.containsKey(p))throw fail("temporary auxiliary name escaped source restoration");
            }
            switch(e.tag) {
            case Expr.APP:work.push((Expr)e.o0);work.push((Expr)e.o1);break;
            case Expr.LAM:case Expr.FORALL:work.push((Expr)e.o1);work.push((Expr)e.o2);break;
            case Expr.LET:work.push((Expr)e.o1);work.push((Expr)e.o2);work.push((Expr)e.o3);break;
            case Expr.MDATA:case Expr.PROJ:work.push((Expr)e.o1);break;
            default:break;
            }
        }
    }
    private static Expr close(Expr term,List<LocalDecl> locals) {
        long[] ids=new long[locals.size()];for(int i=0;i<ids.length;i++)ids[i]=locals.get(i).id;
        Expr out=Reducer.abstractFvars(term,ids.length,ids);
        for(int i=locals.size()-1;i>=0;i--) {
            LocalDecl l=locals.get(i);out=Expr.lam(l.name,Reducer.abstractFvars(l.type,i,ids),out,l.binderInfo);
        }
        return out;
    }
    private static void checkRestoredComputations(Env finalEnv,RawInductiveGenerator.Result aux,
            NestedElimResult discovery,long fuel) {
        for(ConstantInfo rec:aux.constants) if(rec.isRecursor()) for(ConstantInfo.RecursorRule rule:rec.rules) {
            TypeChecker tc=new TypeChecker(aux.env,TypeChecker.DEFN_SAFE,rec.levelParams);tc.setFuel(fuel);
            long next=1;long left=fuel;ArrayList<LocalDecl> locals=new ArrayList<>();ArrayList<Expr> prefix=new ArrayList<>();
            Expr type=rec.type;
            for(int i=0;i<rec.numParams+rec.numMotives+rec.numMinors;i++) {
                if(--left<0 || type.tag!=Expr.FORALL)throw fail("invalid nested recursor telescope");
                LocalDecl local=new LocalDecl(next++,type.o0,(Expr)type.o1,type.o3);
                tc.addLocalDecl(local.id,local.name,local.type);locals.add(local);prefix.add(local.fvar);
                type=Reducer.instantiate1((Expr)type.o2,local.fvar);
            }
            ConstantInfo ctor=aux.env.lookup(rule.ctor);if(ctor==null)throw fail("missing auxiliary rule constructor");
            Expr ctorType=ctor.type;ArrayList<Expr> fields=new ArrayList<>();
            while(ctorType.tag==Expr.FORALL) {
                if(--left<0)throw fail("nested computation traversal fuel exhausted");
                LocalDecl local=new LocalDecl(next++,ctorType.o0,(Expr)ctorType.o1,ctorType.o3);
                tc.addLocalDecl(local.id,local.name,local.type);locals.add(local);fields.add(local.fvar);
                ctorType=Reducer.instantiate1((Expr)ctorType.o2,local.fvar);
            }
            Object[] levels=new Object[rec.levelParams.length];
            for(int i=0;i<levels.length;i++)levels[i]=Level.param((Name)rec.levelParams[i]);
            Expr lhs=Expr.mkConst(rec.name,levels,levels.length>0);
            for(Expr x:prefix)lhs=Expr.app(lhs,x);
            Expr intro=Expr.mkConst(ctor.name,new Object[0],false);for(Expr x:fields)intro=Expr.app(intro,x);
            lhs=Expr.app(lhs,intro);
            Expr lhsType=tc.check(lhs),reduct=tc.whnfExpr(lhs),rhsType=tc.check(reduct);
            if(!tc.isDefEq(lhsType,rhsType))throw fail("auxiliary computation lost type preservation");
            Expr restoredLhs=discovery.restoreNested(close(lhs,locals));
            Expr restoredRhs=discovery.restoreNested(close(reduct,locals));
            checkNoAux(restoredLhs,discovery,fuel);checkNoAux(restoredRhs,discovery,fuel);
            TypeChecker restoredTc=new TypeChecker(finalEnv,TypeChecker.DEFN_SAFE,rec.levelParams);restoredTc.setFuel(fuel);
            Expr actualLhsType=restoredTc.check(restoredLhs),actualRhsType=restoredTc.check(restoredRhs);
            if(!restoredTc.isDefEq(actualLhsType,actualRhsType) || !restoredTc.isDefEq(restoredLhs,restoredRhs))
                throw fail("restored nested computation is not type preserving");
        }
    }
}
