package ansatz.lean.jvm.internal.exec;

import java.math.BigInteger;
import java.util.*;
import ansatz.lean.jvm.internal.exec.Interpreter.*;
import ansatz.lean.jvm.internal.exec.ExprDirectInstantiation.*;
import ansatz.lean.jvm.internal.exec.ExprDelayedInstantiation.*;
import ansatz.lean.jvm.internal.exec.LevelInstantiation.*;
import static ansatz.lean.jvm.internal.exec.Interpreter.*;

/** Lean Expr transform machinery: the resumable replace/lift/lower/instantiate/abstract
 * job stack, beta reduction and loose-bvar queries. Jobs run as budgeted
 * RuntimeAction steps and call guest constructors/helpers through the interpreter;
 * heap writes go through Interpreter ownership operations. */
final class ExprTransforms {
    private final Interpreter vm;

    ExprTransforms(Interpreter vm) {
        this.vm=vm;
    }

    /** Private stage-one policy. Source authentication is the research loader's
     * obligation; this immutable object only binds exact ordinary constructor roles. */
    static final class ExprConstructorPolicy {
        final Header[] helpers;
        private ExprConstructorPolicy(Header[] helpers) { this.helpers=helpers.clone(); }
        static ExprConstructorPolicy originalHeaders(Header[] helpers) {
            require(helpers!=null&&helpers.length==9,"Nine original Expr constructor Headers required");
            String[] names={"Lean.Expr.bvar._override","Lean.Expr.sort._override","Lean.Expr.const._override","Lean.Expr.app._override","Lean.Expr.lam._override._boxed","Lean.Expr.forallE._override._boxed","Lean.Expr.letE._override._boxed","Lean.Expr.mdata._override","Lean.Expr.proj._override"};
            String[] hashes={"65c182e597519411555771e582645ee70b608f98413158d2cf3e525eaa689be1","7ef9c9c1c18da89d2811e3c31a516e05106d3ab6e0ac9a972cbe9eb6dde68f6d","729dc14162f591752d010053a082eedfb8d39d3c12db845d49ba2361a6e0bfe3","80d03ae09c95edb7d931e5f36dd67e6d0452a7efb9002b4cff43f5d7cc0d4ef4","6549605db438808e61e47fc97321040ecba177aa36bdf7146656d625f535b40f","93904f8bf3678937186f334bc847b417487ab0132964b32914497b30219bb9ad","3131e7471a4cb37f4cf7b468a3fcc8910ba1026c0f19d9e50b56689765e2dc5e","b0c8524c099135bec06dacbf9abc3eb0ab4b413ffc6004d55ac782290179a7f4","cf155c3f689c3251707318535264965a5482ed40177d2d255d6076331bc668ab"};
            String[][] parameters={new String[]{"tobject"},new String[]{"tobject"},new String[]{"tobject","tobject"},new String[]{"object","object"},new String[]{"tobject","object","object","tagged"},new String[]{"tobject","object","object","tagged"},new String[]{"tobject","object","object","object","tagged"},new String[]{"tobject","object"},new String[]{"tobject","tobject","object"}};
            for(int role=0;role<9;role++) {
                Header h=helpers[role];
                require(h!=null&&h.kind.equals("fdecl")&&h.originalSha256.equals(hashes[role]),"Expr constructor role/source hash differs");
                if(role!=0) require(h.source==helpers[0].source,"Expr constructors have different source bindings");
                Object name=Arrays.asList("anonymous");
                for(String segment:names[role].split("\\.")) name=Arrays.asList("str",name,segment);
                require(h.exactName.equals(frozenName(name)),"Expr constructor typed Name differs");
                Map<String,Object> d=h.declaration;
                require(d.keySet().equals(new HashSet<>(Arrays.asList("f","info","type","xs")))
                        &&map(d.get("info")).isEmpty()&&d.get("f").equals(h.exactName)
                        &&"object".equals(d.get("type")),"Expr constructor declaration differs");
                List<Object> xs=list(d.get("xs"));
                require(xs.size()==parameters[role].length,"Expr constructor raw arity differs");
                for(int i=0;i<xs.size();i++) {
                    Map<String,Object> p=map(xs.get(i)),x=map(p.get("x"));
                    require(p.keySet().equals(new HashSet<>(Arrays.asList("borrow","ty","x")))
                            &&x.keySet().equals(Collections.singleton("idx"))&&number(x.get("idx"))==i+1
                            &&Boolean.FALSE.equals(p.get("borrow"))&&parameters[role][i].equals(p.get("ty")),
                            "Expr constructor raw parameter differs");
                }
                Map<String,Object> runtime=map(h.evidence.get("runtime"));
                require(runtime.keySet().equals(new HashSet<>(Arrays.asList("initializer","role")))
                        &&runtime.get("initializer")==null&&"ordinary".equals(runtime.get("role")),"Expr constructor is not ordinary");
            }
            return new ExprConstructorPolicy(helpers);
        }
    }
    Function exprConstructor(ExprConstructorPolicy policy,int role) {
        Header header=policy.helpers[role]; int id=vm.program.functionId(header); Function f=vm.program.functions[id];
        require(f.header==header&&f.intrinsic==0&&f.hostExtern==null&&vm.program.guestExports[id]==null,
                "Expr constructor is not the current exact ordinary Function");
        requireExecutableAbi(f); require(f.resultType==OBJ,"Expr constructor requires OBJ result");
        for(int lane:f.paramTypes) require(lane==OBJ,"Expr constructor requires OBJ parameters");
        return vm.preflightCallable(f,true);
    }
    static final int EXPR_LIFT_JOB=0,EXPR_SUBST_JOB=1,EXPR_BETA_JOB=2,EXPR_ABSTRACT_JOB=3,EXPR_CALLBACK_JOB=4,EXPR_LOWER_JOB=5;
    static final int MAX_EXPR_JOB_FRAMES=100_000,MAX_EXPR_JOB_CACHE=100_000,MAX_EXPR_JOB_OFFSET=1_048_575;
    static final class ExprCredit {
        Object value; boolean owned;
        ExprCredit(Object value,boolean owned) { this.value=value; this.owned=owned; }
    }
    abstract static class ExprJob {
        ExprCredit result,childResult; boolean completed; int cleanup;
    }
    static final class ReplaceJob extends ExprJob {
        Object input; int mode,cutoff; long amount; Object[] substitutions;
        ExprSubstSlice slice;
        Node abstractArray; int prefixLength;
        final ArrayDeque<ExprReplaceFrame> frames=new ArrayDeque<>();
        final IdentityHashMap<Node,HashMap<Integer,ExprCredit>> cache=new IdentityHashMap<>();
        final IdentityHashMap<Node,ExprCredit> callbackCache=new IdentityHashMap<>();
        final ArrayList<ExprCredit> cacheValues=new ArrayList<>();
        final IdentityHashMap<Node,Boolean> active=new IdentityHashMap<>();
        int stage,reservedCacheEntries;
    }
    static final class ExprReplaceFrame {
        Node original; int offset,stage,cursor,cleanup,abstractScan; boolean shared,active;
        ExprCredit[] children=new ExprCredit[3]; ExprCredit result;
        ExprReplaceFrame(Node original,int offset) { this.original=original; this.offset=offset; }
    }
    static final class BetaJob extends ExprJob {
        ExprCredit function,temporary,accumulator,replacement;
        Object[] reverseArgs; int consumed,remaining,stage;
        final ArrayDeque<ExprBetaFrame> frames=new ArrayDeque<>();
    }
    static final class ExprBetaFrame {
        ExprCredit expression;
        ExprBetaFrame(ExprCredit expression) { this.expression=expression; }
    }
    static final class ExprPacket {
        Function function; Object[] arguments,expectedFields; boolean[] owned;
        int role,expectedTag,expectedFlag; boolean started,entered;
        ExprReplaceFrame replaceFrame; BetaJob beta; ExprDirectTask directTarget; DelayedTransformTask delayedTarget;
    }
    private static final int MAX_INSTANTIATION_WORK=1_000_000;
    static final class InstantiationBudget { long work; }
    static final class MVarContextCell { LevelCredit current; }
    void instantiationWork(InstantiationBudget budget,long amount,String bound,String interrupted) {
        require(budget!=null,"Missing instantiation budget");
        require(amount>=0&&amount<=MAX_INSTANTIATION_WORK-budget.work,bound);
        long before=budget.work; budget.work+=amount;
        if((before>>>10)!=(budget.work>>>10)&&Thread.currentThread().isInterrupted()) throw error(interrupted);
    }
    static final class ExprMachineryState {
        ExprConstructorPolicy policy;
        final ArrayDeque<ExprJob> jobs=new ArrayDeque<>();
        ExprCredit input,result,retiring; final ArrayList<ExprCredit> arguments=new ArrayList<>();
        Node borrowedPredicate; ExprCallbackPacket callback;
        ExprPacket call; InstantiationBudget budget; int stage,cleanup,liveFrames,liveCacheEntries;
    }
    private void exprJobWork(ExprMachineryState state,long amount) {
        instantiationWork(state.budget,amount,"Expr machinery work outside bounded profile","Expr machinery interrupted");
    }
    private static final int XR_ENTER=0,XR_CHILDREN=1,XR_LIFT_WAIT=2,XR_BUILD=3,XR_HELPER=4,XR_FINISH=5,XR_CLEAN=6,XR_ABSTRACT_SCAN=7,XR_CALLBACK_WAIT=8,XR_CALLBACK_NONE=9;
    static int exprChildCount(int tag) {
        return tag==5||tag==6||tag==7?2:tag==8?3:tag==10||tag==11?1:0;
    }
    static int exprChildField(int tag,int child) {
        return tag==5?child:tag==6||tag==7||tag==8?child+1:tag==10?1:2;
    }
    static int exprCtorRole(int tag) {
        switch(tag) { case 0:return 0; case 3:return 1; case 4:return 2; case 5:return 3;
            case 6:return 4; case 7:return 5; case 8:return 6; case 10:return 7; case 11:return 8;
            default:throw error("Expr tag has no rebuilding constructor role"); }
    }
    private static final int[] EXPR_CTOR_TAGS={0,3,4,5,6,7,8,10,11};
    ExprCredit exprCredit(Object value) { return new ExprCredit(value,false); }
    void acquireExpr(ExprCredit credit) {
        require(credit!=null&&!credit.owned,"Expr credit already acquired"); vm.inc(credit.value,1); credit.owned=true;
    }
    private void selectExpr(ExprReplaceFrame frame,Object value) {
        frame.result=exprCredit(value); acquireExpr(frame.result); frame.stage=XR_FINISH;
    }
    private boolean releaseExprCredit(RuntimeAction action,ExprMachineryState state,ExprCredit credit) {
        if(credit==null||!credit.owned) return false;
        state.retiring=credit; action.retiring=credit.value; action.releaseClaimed=false;
        boolean dispatch;
        try { dispatch=vm.beginRelease(credit.value,1,ACTION_BODY); credit.owned=false; }
        finally { if(action.releaseClaimed) credit.owned=false; }
        if(!dispatch) { state.retiring=null; action.retiring=null; action.releaseClaimed=false; }
        return dispatch;
    }
    private void pushExprFrame(ExprMachineryState state,ReplaceJob job,Object input,int offset) {
        require(offset>=0&&offset<=MAX_EXPR_JOB_OFFSET,"Expr binder offset outside bounded profile");
        require(state.liveFrames<MAX_EXPR_JOB_FRAMES,"Expr machinery frame limit");
        Node node=vm.exprNode(input); job.frames.addLast(new ExprReplaceFrame(node,offset)); state.liveFrames++;
    }
    void pushReplaceJob(ExprMachineryState state,int mode,Object input,int cutoff,long amount,Object[] substitutions) {
        require(state.jobs.size()<MAX_EXPR_JOB_FRAMES,"Expr machinery job limit");
        ReplaceJob job=new ReplaceJob(); job.input=input; job.mode=mode; job.cutoff=cutoff; job.amount=amount;
        job.substitutions=substitutions; state.jobs.addLast(job);
    }
    static boolean sameExprField(Object left,Object right) {
        return left==right||!(left instanceof Node)&&left!=null&&left.equals(right);
    }
    ExprPacket prepareExprConstructorPacket(ExprConstructorPolicy policy,int role,Object[] values) {
        Function helper=exprConstructor(policy,role);
        require(helper.params.length==values.length,"Expr constructor packet arity differs");
        ExprPacket packet=new ExprPacket(); packet.function=helper; packet.role=role;
        packet.arguments=values.clone(); packet.owned=new boolean[values.length]; packet.expectedTag=EXPR_CTOR_TAGS[role]; packet.expectedFlag=-1;
        int fields=packet.expectedTag==6||packet.expectedTag==7?3:packet.expectedTag==8?4:values.length;
        packet.expectedFields=Arrays.copyOf(values,fields);
        if(packet.expectedTag>=6&&packet.expectedTag<=8) {
            require(values[fields] instanceof Long,"Expr constructor boxed flag requires Long");
            long flag=(Long)values[fields]; require(flag>=0&&flag<=(packet.expectedTag==8?1:4),"Expr constructor flag outside profile");
            packet.expectedFlag=(int)flag;
        }
        return packet;
    }
    void acquireExprConstructorPacket(ExprPacket packet) {
        IdentityHashMap<Node,Integer> owners=new IdentityHashMap<>();
        for(int i=0;i<packet.arguments.length;i++) {
            Object value=packet.arguments[i]; vm.validateHostObject(value); vm.inc(value,1); packet.owned[i]=true;
            if(value instanceof Node) owners.merge((Node)value,1,Integer::sum);
        }
        for(Map.Entry<Node,Integer> entry:owners.entrySet())
            require(entry.getKey().refCount()==0||entry.getKey().refCount()>=entry.getValue(),"Expr constructor packet owner occurrences differ");
    }
    ExprCredit takeExprConstructorResult(RuntimeAction action,ExprPacket packet) {
        Object value=vm.objects[action.slot]; Node node=vm.exprNode(value);
        require(node.storageTag()==packet.expectedTag&&node.fieldCount()==packet.expectedFields.length,"Expr constructor returned unexpected head");
        for(int i=0;i<node.fieldCount();i++) require(sameExprField(node.storageField(i),packet.expectedFields[i]),"Expr constructor returned unexpected child");
        if(packet.expectedFlag>=0) require((node.storageByte(8))==packet.expectedFlag,"Expr constructor returned unexpected flag");
        ExprCredit credit=new ExprCredit(value,true); vm.objects[action.slot]=null; return credit;
    }
    private void callExprConstructor(RuntimeAction action,ExprMachineryState state,int role,Object[] values,ExprReplaceFrame frame,BetaJob beta) {
        exprJobWork(state,1); require(state.call==null&&vm.objects[action.slot]==null,"Expr constructor receiver occupied");
        ExprPacket packet=prepareExprConstructorPacket(state.policy,role,values); packet.replaceFrame=frame; packet.beta=beta;
        state.call=packet; acquireExprConstructorPacket(packet); packet.started=true;
        vm.enterExplicit(packet.function,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Expr constructor did not publish frame or CodeRequest");
    }
    private void receiveExprConstructor(RuntimeAction action,ExprMachineryState state) {
        ExprPacket packet=state.call; require(packet.entered,"Expr constructor receiver precedes entry");
        require(packet.replaceFrame!=null||packet.beta!=null&&packet.beta.replacement==null,"Missing Expr beta receiver");
        ExprCredit credit=takeExprConstructorResult(action,packet);
        if(packet.replaceFrame!=null) { packet.replaceFrame.result=credit; packet.replaceFrame.stage=XR_FINISH; }
        else packet.beta.replacement=credit;
        state.call=null;
    }
    private void requestBVar(RuntimeAction action,ExprMachineryState state,ExprReplaceFrame frame,BigInteger index) {
        exprJobWork(state,1+(index.bitLength()+63L)/64);
        require(index.signum()>=0&&index.compareTo(BigInteger.valueOf(MAX_EXPR_JOB_OFFSET-1))<=0,"Expr bvar constructor range outside bounded profile");
        Object logical=index.bitLength()<=63?Long.valueOf(index.longValue()):index;
        frame.stage=XR_HELPER; callExprConstructor(action,state,0,new Object[]{logical},frame,null);
    }
    private void rebuildExpr(RuntimeAction action,ExprMachineryState state,ExprReplaceFrame frame) {
        Node original=frame.original; int count=exprChildCount(original.storageTag()); boolean changed=false;
        Object[] fields=original.copyFields();
        for(int i=0;i<count;i++) {
            require(frame.children[i]!=null&&frame.children[i].owned,"Expr replacement child result missing");
            int at=exprChildField(original.storageTag(),i); fields[at]=frame.children[i].value;
            changed|=!sameExprField(fields[at],original.storageField(at));
        }
        if(!changed) { selectExpr(frame,original); return; }
        Object[] values=fields;
        if(original.storageTag()>=6&&original.storageTag()<=8) {
            values=Arrays.copyOf(fields,fields.length+1); values[fields.length]=Long.valueOf(original.storageByte(8));
        }
        frame.stage=XR_HELPER; callExprConstructor(action,state,exprCtorRole(original.storageTag()),values,frame,null);
    }
    private void completeReplaceFrame(ExprMachineryState state,ReplaceJob job,ExprReplaceFrame frame) {
        require(frame.result!=null&&frame.result.owned,"Missing Expr replacement result owner");
        require(job.frames.peekLast()==frame,"Expr replacement frame order differs");
        Iterator<ExprReplaceFrame> ancestors=job.frames.descendingIterator(); ancestors.next();
        ExprReplaceFrame parent=ancestors.hasNext()?ancestors.next():null;
        if(parent!=null) require(parent.stage==XR_CHILDREN&&parent.cursor<parent.children.length&&parent.children[parent.cursor]==null,
                "Expr parent is not waiting for an empty child receiver");
        if(frame.active) job.active.remove(frame.original);
        if(parent==null) { job.result=frame.result; job.stage=2; job.cache.clear(); job.callbackCache.clear(); job.active.clear(); job.cleanup=0; }
        else parent.children[parent.cursor++]=frame.result;
        frame.result=null; job.frames.removeLast(); state.liveFrames--;
    }
    /** Borrowed view of caller-owned substitutions, never a guest Array or owner.
     * Direction is explicit: native reverse-empty still visits loose bvars. */
    static final class ExprSubstSlice {
        final Node array;
        final Object single;
        final int begin,end;
        final boolean reverse;
        ExprSubstSlice(Node array,Object single,int begin,int end,boolean reverse) {
            this.array=array; this.single=single; this.begin=begin; this.end=end; this.reverse=reverse;
        }
        int size() { return end-begin; }
        Object at(int relative) {
            require(relative>=0&&relative<size(),"Expr substitution index outside selected slice");
            return array==null?single:array.storageField(reverse?end-1-relative:begin+relative);
        }
    }
    private static int exprSubstitutionCount(ReplaceJob job) { return job.slice==null?job.substitutions.length:job.slice.size(); }
    private static Object exprSubstitutionAt(ReplaceJob job,int relative) { return job.slice==null?job.substitutions[relative]:job.slice.at(relative); }
    static boolean pureExprTransform(int op) {
        return op==EXPR_INSTANTIATE||op==EXPR_INSTANTIATE1||op==EXPR_INSTANTIATE_RANGE
                ||op==EXPR_INSTANTIATE_REV||op==EXPR_INSTANTIATE_REV_RANGE||op==EXPR_LIFT||op==EXPR_LOWER;
    }
    static final int MAX_EXPR_LOOSE_WORK=1_000_000,MAX_EXPR_LOOSE_STACK=100_000,MAX_EXPR_LOOSE_KEYS=100_000;
    static final class LooseSearchFrame {
        final Node node; final int offset; final boolean exit;
        LooseSearchFrame(Node node,int offset,boolean exit) { this.node=node; this.offset=offset; this.exit=exit; }
    }
    static boolean borrowedExprLooseQuery(int op) { return op==EXPR_HAS_LOOSE; }
    /** Preserve the full immediate comparison before C++ unsigned32 narrowing.
     * Only the continued assertion domain is rejected; earlier source identity
     * shortcuts remain identity even if narrowed cutoff<delta. */
    private long[] lowerExprParameters(Object input,Object cutoffValue,Object deltaValue) {
        BigInteger cutoff=pureExprNat(cutoffValue),delta=pureExprNat(deltaValue);
        long s=0,d=0;
        if(cutoff.compareTo(SMALL_MAX)<=0&&delta.compareTo(SMALL_MAX)<=0&&cutoff.compareTo(delta)>=0) {
            s=cutoff.longValue()&0xffffffffL; d=delta.longValue()&0xffffffffL;
            if(d==0||s>=(vm.exprCachedData(input)>>>44)) { s=0; d=0; }
            else require(s>=d,"Expr lower narrowed assertion domain outside bounded profile");
        }
        return new long[]{s,d};
    }
    static BigInteger pureExprNat(Object value) {
        require(!(value instanceof BigInteger)||value.getClass()==BigInteger.class,"Expr transform Nat requires exact immutable BigInteger");
        return nat(value);
    }
    Node pureExprArray(Object value) {
        Node node=vm.array(value);
        require(node.storageTag()==246&&!node.isReadyTask()&&node.scalarCount()==0&&kindMetadata(node) instanceof ArrayState,
                "Invalid Expr substitution Array storage");
        int size=arrayState(node).size;
        require(size>=0&&size<=node.fieldCount()&&node.fieldCount()<=MAX_ARRAY_CAPACITY,"Invalid Expr substitution Array live extent");
        return node;
    }
    private ExprSubstSlice pureExprSlice(Function function,Object[] args) {
        int op=function.intrinsic;
        if(op==EXPR_INSTANTIATE1) return new ExprSubstSlice(null,vm.exprNode(args[1]),0,1,false);
        boolean range=op==EXPR_INSTANTIATE_RANGE||op==EXPR_INSTANTIATE_REV_RANGE;
        Node substitutions=pureExprArray(args[range?3:1]); int begin=0,end=arrayState(substitutions).size;
        if(range) {
            BigInteger b=pureExprNat(args[1]),e=pureExprNat(args[2]);
            require(b.compareTo(SMALL_MAX)<=0&&e.compareTo(SMALL_MAX)<=0&&b.compareTo(e)<=0
                    &&e.compareTo(BigInteger.valueOf(end))<=0,"Expr instantiation range panic path outside bounded profile");
            begin=b.intValue(); end=e.intValue();
        }
        return new ExprSubstSlice(substitutions,null,begin,end,op==EXPR_INSTANTIATE_REV||op==EXPR_INSTANTIATE_REV_RANGE);
    }
    void validatePureExprTransform(Function function,Object[] args) {
        vm.exprTransformsProfile(function);
        int op=function.intrinsic,arity=op==EXPR_LIFT||op==EXPR_LOWER?3:op==EXPR_INSTANTIATE_RANGE||op==EXPR_INSTANTIATE_REV_RANGE?4:2;
        require(args!=null&&args.length==arity,"Pure Expr transform native arity mismatch");
        vm.exprNode(args[0]);
        if(op==EXPR_LOWER) lowerExprParameters(args[0],args[1],args[2]);
        else if(op==EXPR_LIFT) { pureExprNat(args[1]); pureExprNat(args[2]); }
        else pureExprSlice(function,args);
    }
    void preparePureExprTransform(RuntimeAction action,Function function,Object[] args) {
        ExprMachineryState state=new ExprMachineryState(); state.policy=vm.exprTransformsProfile(function);
        state.budget=new InstantiationBudget();
        if(function.intrinsic==EXPR_LOWER) {
            long[] parameters=lowerExprParameters(args[0],args[1],args[2]);
            require(parameters[0]<=MAX_EXPR_JOB_OFFSET,"Expr lower continued cutoff outside profile");
            pushReplaceJob(state,EXPR_LOWER_JOB,args[0],(int)parameters[0],parameters[1],new Object[0]);
        } else if(function.intrinsic==EXPR_LIFT) {
            BigInteger cutoff=pureExprNat(args[1]),delta=pureExprNat(args[2]);
            long s=0,d=0;
            // Typed canonical Nat values above signed63 are native heap Nats.
            // Immediates narrow to unsigned32 in the pinned C++ function call.
            if(cutoff.compareTo(SMALL_MAX)<=0&&delta.compareTo(SMALL_MAX)<=0) {
                s=cutoff.longValue()&0xffffffffL; d=delta.longValue()&0xffffffffL;
                if(d==0||s>=(vm.exprCachedData(args[0])>>>44)) { s=0; d=0; }
            }
            // Any continued cutoff is below the source20-bit cached range.
            require(s<=MAX_EXPR_JOB_OFFSET,"Expr lift cutoff exceeds continued visitor profile");
            pushReplaceJob(state,EXPR_LIFT_JOB,args[0],(int)s,d,new Object[0]);
        } else {
            ReplaceJob job=new ReplaceJob(); job.mode=EXPR_SUBST_JOB; job.input=args[0];
            job.substitutions=new Object[0]; job.slice=pureExprSlice(function,args); state.jobs.addLast(job);
        }
        action.exprMachinery=state; vm.objects[action.slot]=null;
    }
    /** Borrowed original/current aliases; only flagged acquired credits and the
     * owned receiver/Option packet can own. AP becomes authoritative at start. */
    static final class ExprCallbackPacket {
        ExprReplaceFrame frame;
        Object[] arguments;
        ExprCredit current,predicate,option;
        int stage;
        boolean started,receiverOwned;
    }
    void validateExprReplace(Function function,Object[] args) {
        vm.exprTransformsProfile(function);
        require(args!=null&&args.length==2,"Expr.replace native arity mismatch");
        vm.validateExprReplaceCallback(args[0]);
        require(vm.node(args[0]).refCount()>=0&&vm.exprNode(args[1]).refCount()>=0,"Invalid Expr.replace borrowed owner count");
    }
    private void prepareExprReplaceCallback(ExprMachineryState state,ExprReplaceFrame frame) {
        require(state.callback==null&&state.borrowedPredicate!=null,"Expr.replace callback packet already occupied");
        vm.validateExprReplaceCallback(state.borrowedPredicate);
        ExprCallbackPacket packet=new ExprCallbackPacket(); packet.frame=frame;
        packet.arguments=new Object[]{frame.original};
        packet.current=exprCredit(frame.original); packet.predicate=exprCredit(state.borrowedPredicate);
        state.callback=packet; frame.stage=XR_CALLBACK_WAIT;
    }
    private void stepExprReplaceCallback(RuntimeAction action,ExprMachineryState state) {
        ExprCallbackPacket packet=state.callback; require(packet!=null,"Missing Expr.replace callback packet");
        if(packet.stage==0) {
            // Pinned replace_fn, unlike Find: Expr INC precedes predicate INC.
            acquireExpr(packet.current); acquireExpr(packet.predicate);
            packet.stage=1; packet.started=true;
            packet.current.owned=false; packet.predicate.owned=false;
            vm.applyExplicit(packet.predicate.value,packet.arguments,ACTION_BODY,action.slot); return;
        }
        if(packet.stage==1) {
            Object value=vm.objects[action.slot]; packet.receiverOwned=true;
            if(ERASED.equals(value)) {
                vm.objects[action.slot]=null; packet.receiverOwned=false;
                packet.frame.stage=XR_CALLBACK_NONE; state.callback=null; return;
            }
            Node option=vm.constructorNode(value);
            require(option.closureFunction()==null&&option.storageTag()==1&&option.fieldCount()==1&&option.scalarCount()==0&&option.refCount()>=0,
                    "Expr.replace callback did not return canonical Option Expr");
            Node replacement=vm.exprNode(option.storageField(0));
            // Allocate both escrows before acquiring or moving any owner.
            packet.frame.result=exprCredit(replacement); packet.option=exprCredit(option);
            acquireExpr(packet.frame.result);
            packet.option.owned=true; vm.objects[action.slot]=null; packet.receiverOwned=false;
            packet.stage=2;
        }
        if(packet.stage==2) {
            packet.stage=3;
            if(releaseExprCredit(action,state,packet.option)) return;
        }
        require(packet.stage==3&&!packet.option.owned,"Expr.replace returned before Option cleanup");
        packet.frame.stage=XR_FINISH; state.callback=null;
    }
    private void stepReplaceJob(RuntimeAction action,ExprMachineryState state,ReplaceJob job) {
        if(job.stage==0) {
            if(job.mode==EXPR_CALLBACK_JOB) { job.stage=1; pushExprFrame(state,job,job.input,0); return; }
            Node input=vm.exprNode(job.input); long range=vm.exprCachedData(input)>>>44;
            boolean shortcut=job.mode==EXPR_ABSTRACT_JOB?!abstractFlags(input):
                    (job.mode==EXPR_LIFT_JOB||job.mode==EXPR_LOWER_JOB)?(job.amount==0||job.cutoff>=range):((exprSubstitutionCount(job)==0&&(job.slice==null||!job.slice.reverse))||range==0);
            if(shortcut) {
                job.result=exprCredit(input); acquireExpr(job.result); job.stage=2; return;
            }
            job.stage=1; pushExprFrame(state,job,input,0); return;
        }
        if(job.stage==2) {
            if(job.cleanup<job.cacheValues.size()) {
                ExprCredit credit=job.cacheValues.get(job.cacheValues.size()-1-job.cleanup++); releaseExprCredit(action,state,credit); return;
            }
            require(job.reservedCacheEntries==job.cacheValues.size()&&state.liveCacheEntries>=job.reservedCacheEntries,"Expr cache reservation ledger differs");
            state.liveCacheEntries-=job.reservedCacheEntries; job.reservedCacheEntries=0;
            job.cacheValues.clear(); job.input=null; job.substitutions=null; job.slice=null; job.abstractArray=null; job.completed=true; return;
        }
        ExprReplaceFrame frame=job.frames.peekLast(); require(frame!=null,"Missing Expr replacement frame"); Node node=frame.original;
        if(frame.stage==XR_ENTER) {
            // Public callback replace uses !exclusive; offset jobs retain the
            // distinct native likely-unshared RC hint, intentionally ignoring MT.
            frame.shared=job.mode==EXPR_CALLBACK_JOB?!exclusive(node):node.refCount()!=1;
            HashMap<Integer,ExprCredit> offsets=frame.shared&&job.mode!=EXPR_CALLBACK_JOB?job.cache.get(node):null;
            ExprCredit cached=frame.shared&&job.mode==EXPR_CALLBACK_JOB?job.callbackCache.get(node):offsets==null?null:offsets.get(frame.offset);
            if(cached!=null) { require(cached.owned,"Expr replacement cache owner missing"); selectExpr(frame,cached.value); frame.shared=false; return; }
            if(job.mode==EXPR_CALLBACK_JOB) { prepareExprReplaceCallback(state,frame); return; }
            if(job.mode==EXPR_ABSTRACT_JOB) {
                if(!abstractFlags(node)) { selectExpr(frame,node); return; }
                if(node.storageTag()==1||node.storageTag()==2) {
                    frame.abstractScan=job.prefixLength; frame.stage=XR_ABSTRACT_SCAN; return;
                }
            } else {
                long threshold=(long)job.cutoff+frame.offset;
                if(job.mode==EXPR_LOWER_JOB&&threshold>0xffffffffL) { selectExpr(frame,node); return; }
                if(threshold>=(vm.exprCachedData(node)>>>44)) { selectExpr(frame,node); return; }
                if(node.storageTag()==0) {
                    BigInteger index=nat(node.storageField(0)); exprJobWork(state,1+(index.bitLength()+63L)/64);
                    if(index.compareTo(BigInteger.valueOf(threshold))>=0) {
                        if(job.mode==EXPR_LIFT_JOB) { requestBVar(action,state,frame,index.add(BigInteger.valueOf(job.amount))); return; }
                        if(job.mode==EXPR_LOWER_JOB) { requestBVar(action,state,frame,index.subtract(BigInteger.valueOf(job.amount))); return; }
                        BigInteger at=index.subtract(BigInteger.valueOf(frame.offset));
                        if(at.compareTo(BigInteger.valueOf(exprSubstitutionCount(job)))<0) {
                            frame.stage=XR_LIFT_WAIT;
                            pushReplaceJob(state,EXPR_LIFT_JOB,exprSubstitutionAt(job,at.intValue()),0,frame.offset,new Object[0]); return;
                        }
                        requestBVar(action,state,frame,index.subtract(BigInteger.valueOf(exprSubstitutionCount(job)))); return;
                    }
                }
            }
            startExprReplaceChildren(job,frame); return;
        }
        if(frame.stage==XR_CALLBACK_NONE) { startExprReplaceChildren(job,frame); return; }
        if(frame.stage==XR_ABSTRACT_SCAN) {
            if(frame.abstractScan==0) { selectExpr(frame,node); return; }
            int i=--frame.abstractScan; exprJobWork(state,1);
            Node candidate=vm.exprNode(job.abstractArray.storageField(i));
            if(candidate.storageTag()==node.storageTag()&&abstractNamesEqual(state,node.storageField(0),candidate.storageField(0)))
                requestBVar(action,state,frame,BigInteger.valueOf((long)frame.offset+job.prefixLength-i-1));
            return;
        }
        if(frame.stage==XR_LIFT_WAIT) {
            require(job.childResult!=null&&job.childResult.owned,"Missing substituted lifted result");
            frame.result=job.childResult; job.childResult=null; frame.stage=XR_FINISH; return;
        }
        if(frame.stage==XR_CHILDREN) {
            int count=exprChildCount(node.storageTag());
            if(frame.cursor<count) {
                int offset=frame.offset;
                if(job.mode!=EXPR_CALLBACK_JOB&&((node.storageTag()==6||node.storageTag()==7)&&frame.cursor==1||node.storageTag()==8&&frame.cursor==2)) offset=Math.addExact(offset,1);
                pushExprFrame(state,job,node.storageField(exprChildField(node.storageTag(),frame.cursor)),offset); return;
            }
            frame.stage=XR_BUILD;
        }
        if(frame.stage==XR_BUILD) { rebuildExpr(action,state,frame); return; }
        if(frame.stage==XR_FINISH) {
            if(frame.shared) {
                require(state.liveCacheEntries<MAX_EXPR_JOB_CACHE,"Expr machinery live cache entries outside bounded profile");
                state.liveCacheEntries++; job.reservedCacheEntries++;
                ExprCredit stored=exprCredit(frame.result.value); job.cacheValues.add(stored); acquireExpr(stored);
                if(job.mode==EXPR_CALLBACK_JOB) require(job.callbackCache.putIfAbsent(node,stored)==null,"Duplicate callback Expr cache entry");
                else {
                    HashMap<Integer,ExprCredit> offsets=job.cache.computeIfAbsent(node,key->new HashMap<>());
                    require(offsets.putIfAbsent(frame.offset,stored)==null,"Duplicate Expr replacement cache entry");
                }
            }
            frame.stage=XR_CLEAN; frame.cleanup=0;
        }
        if(frame.stage==XR_CLEAN) {
            if(frame.cleanup<3) { ExprCredit credit=frame.children[2-frame.cleanup++]; releaseExprCredit(action,state,credit); return; }
            completeReplaceFrame(state,job,frame); return;
        }
        throw error("Expr replacement constructor continuation did not return");
    }
    private void startExprReplaceChildren(ReplaceJob job,ExprReplaceFrame frame) {
        Node node=frame.original; int count=exprChildCount(node.storageTag());
        if(count==0) { selectExpr(frame,node); return; }
        require(!job.active.containsKey(node),"Expr replacement structural cycle outside profile");
        job.active.put(node,Boolean.TRUE); frame.active=true; frame.stage=XR_CHILDREN; frame.cursor=0;
    }
    private static final int XB_INIT=0,XB_DESCEND=1,XB_ZETA_WAIT=2,XB_LAST_WAIT=3,XB_BASE_WAIT=4,
            XB_APP=5,XB_APP_WAIT=6,XB_DRAIN_TEMP=7,XB_DRAIN_FRAMES=8,XB_DRAIN_FUNCTION=9,XB_DONE=10;
    private void pushBetaFrame(ExprMachineryState state,BetaJob job,ExprCredit credit,boolean acquire) {
        require(state.liveFrames<MAX_EXPR_JOB_FRAMES,"Expr machinery frame limit");
        job.frames.addLast(new ExprBetaFrame(credit)); state.liveFrames++;
        if(acquire) acquireExpr(credit); else require(credit.owned,"Beta child parameter lacks moved result owner");
    }
    private void stepBetaJob(RuntimeAction action,ExprMachineryState state,BetaJob job) {
        if(job.stage==XB_INIT) {
            require(job.function!=null&&job.function.owned,"Beta wrapper function owner missing");
            if(job.reverseArgs.length==0) { job.result=job.function; job.function=null; job.completed=true; return; }
            pushBetaFrame(state,job,exprCredit(job.function.value),true); job.stage=XB_DESCEND; return;
        }
        if(job.stage==XB_DESCEND) {
            ExprBetaFrame frame=job.frames.peekLast(); require(frame!=null&&frame.expression.owned,"Beta recursive parameter owner missing");
            Node expression=vm.exprNode(frame.expression.value);
            if(expression.storageTag()==6) {
                if(job.consumed+1<job.reverseArgs.length) {
                    job.consumed++; pushBetaFrame(state,job,exprCredit(expression.storageField(2)),true); return;
                }
                job.stage=XB_LAST_WAIT; pushReplaceJob(state,EXPR_SUBST_JOB,expression.storageField(2),0,0,job.reverseArgs); return;
            }
            if(expression.storageTag()==8&&job.consumed<job.reverseArgs.length) {
                job.stage=XB_ZETA_WAIT;
                pushReplaceJob(state,EXPR_SUBST_JOB,expression.storageField(3),0,0,new Object[]{expression.storageField(2)}); return;
            }
            if(expression.storageTag()==10) { pushBetaFrame(state,job,exprCredit(expression.storageField(1)),true); return; }
            job.remaining=job.reverseArgs.length-job.consumed;
            job.stage=XB_BASE_WAIT;
            pushReplaceJob(state,EXPR_SUBST_JOB,expression,0,0,Arrays.copyOfRange(job.reverseArgs,job.remaining,job.reverseArgs.length)); return;
        }
        if(job.stage==XB_ZETA_WAIT) {
            require(job.childResult!=null&&job.childResult.owned,"Beta zeta replacement owner missing");
            ExprCredit child=job.childResult;
            // C++20 prvalue initializes the next by-value parameter directly.
            // Keep its receiver owner until the frame-cap preflight succeeds.
            pushBetaFrame(state,job,child,false); job.childResult=null; job.stage=XB_DESCEND; return;
        }
        if(job.stage==XB_LAST_WAIT) {
            require(job.childResult!=null&&job.childResult.owned,"Beta final substitution owner missing");
            job.result=job.childResult; job.childResult=null; job.stage=XB_DRAIN_FRAMES; return;
        }
        if(job.stage==XB_BASE_WAIT) {
            require(job.childResult!=null&&job.childResult.owned,"Beta application base owner missing");
            // The instantiate full-expression temporary anchors mk_rev_app's f,
            // independently from that function's owned accumulator r.
            job.temporary=job.childResult; job.childResult=null;
            job.accumulator=exprCredit(job.temporary.value); acquireExpr(job.accumulator); job.stage=XB_APP; return;
        }
        if(job.stage==XB_APP) {
            require(job.accumulator!=null&&job.accumulator.owned,"Beta application accumulator missing");
            if(job.remaining==0) { job.result=job.accumulator; job.accumulator=null; job.stage=XB_DRAIN_TEMP; return; }
            job.stage=XB_APP_WAIT;
            callExprConstructor(action,state,3,new Object[]{job.accumulator.value,job.reverseArgs[job.remaining-1]},null,job); return;
        }
        if(job.stage==XB_APP_WAIT) {
            require(job.replacement!=null&&job.replacement.owned,"Beta application constructor owner missing");
            ExprCredit old=job.accumulator; job.accumulator=job.replacement; job.replacement=null;
            job.remaining--; job.stage=XB_APP; releaseExprCredit(action,state,old); return;
        }
        if(job.stage==XB_DRAIN_TEMP) { job.stage=XB_DRAIN_FRAMES; releaseExprCredit(action,state,job.temporary); return; }
        if(job.stage==XB_DRAIN_FRAMES) {
            if(!job.frames.isEmpty()) {
                ExprBetaFrame frame=job.frames.removeLast(); state.liveFrames--;
                releaseExprCredit(action,state,frame.expression); return;
            }
            job.stage=XB_DRAIN_FUNCTION;
        }
        if(job.stage==XB_DRAIN_FUNCTION) { job.stage=XB_DONE; releaseExprCredit(action,state,job.function); return; }
        require(job.stage==XB_DONE&&job.result!=null&&job.result.owned,"Incomplete beta job result");
        job.function=null; job.temporary=null; job.accumulator=null; job.replacement=null; job.reverseArgs=null; job.completed=true;
    }
    void stepExprMachinery(RuntimeAction action) {
        ExprMachineryState state=action.exprMachinery; require(state!=null,"Missing private Expr machinery state"); exprJobWork(state,1);
        if(state.retiring!=null) {
            require(!state.retiring.owned,"Expr cleanup returned without retiring owner claim");
            state.retiring=null; action.retiring=null; action.releaseClaimed=false;
        }
        if(state.call!=null) { receiveExprConstructor(action,state); return; }
        if(state.callback!=null) { stepExprReplaceCallback(action,state); return; }
        if(state.stage==0) {
            ExprJob job=state.jobs.peekLast(); require(job!=null,"Missing private Expr job");
            if(!job.completed) {
                if(job instanceof ReplaceJob) stepReplaceJob(action,state,(ReplaceJob)job);
                else stepBetaJob(action,state,(BetaJob)job);
                return;
            }
            require(job.result!=null&&job.result.owned,"Private Expr job completed without result owner");
            Iterator<ExprJob> ancestors=state.jobs.descendingIterator(); ancestors.next();
            ExprJob parent=ancestors.hasNext()?ancestors.next():null;
            if(parent!=null) require(parent.childResult==null,"Private Expr child receiver occupied");
            if(parent==null) { state.result=job.result; state.stage=1; }
            else parent.childResult=job.result;
            job.result=null; state.jobs.removeLast();
            return;
        }
        if(state.stage==1) { state.stage=2; state.cleanup=0; releaseExprCredit(action,state,state.input); return; }
        if(state.stage==2) {
            if(state.cleanup<state.arguments.size()) {
                ExprCredit credit=state.arguments.get(state.arguments.size()-1-state.cleanup++); releaseExprCredit(action,state,credit); return;
            }
            state.stage=3;
        }
        require(state.stage==3&&state.result!=null&&state.result.owned&&state.liveFrames==0&&state.liveCacheEntries==0,"Incomplete private Expr output");
        Object result=state.result.value; action.output=result; state.result.owned=false;
        state.input=null; state.result=null; state.arguments.clear(); state.borrowedPredicate=null; state.callback=null; action.arguments=null; action.exprMachinery=null;
        vm.finishAction(action,result);
    }
    static boolean abstractPrimitive(int op) { return op==EXPR_ABSTRACT_RANGE||op==EXPR_ABSTRACT; }
    private boolean abstractFlags(Node node) { return (vm.exprCachedData(node)&(7L<<40))!=0; }
    private boolean abstractNamesEqual(ExprMachineryState state,Object left,Object right) {
        ExprEquality comparison=vm.new ExprEquality(false); comparison.work=state.budget.work;
        try { return vm.nameEquals(left,right,comparison); }
        finally { state.budget.work=comparison.work; }
    }
    private int abstractPrefix(Function function,Object[] args) {
        int arity=function.intrinsic==EXPR_ABSTRACT_RANGE?3:2;
        require(args!=null&&args.length==arity,"Expr abstraction native arity differs");
        vm.exprNode(args[0]); Node values=vm.array(args[arity-1]); int size=arrayState(values).size;
        int prefix=size;
        if(function.intrinsic==EXPR_ABSTRACT_RANGE) {
            Object count=args[1];
            require(count instanceof Long&&((Long)count)>=0||count instanceof BigInteger&&((BigInteger)count).signum()>=0,
                    "Expr abstraction requires nonnegative Nat range");
            // Native heap-Nat branch selects the whole array, even for a small MPZ.
            if(count instanceof Long) prefix=(int)Math.min((Long)count,(long)size);
        }
        require(prefix<=MAX_EXPR_JOB_FRAMES,"Expr abstraction prefix outside bounded profile");
        return prefix;
    }
    void validateAbstractArguments(Function function,Object[] args) {
        vm.exprTransformsProfile(function); abstractPrefix(function,args);
    }
    void prepareAbstractAction(RuntimeAction action,Function function,Object[] args) {
        ExprMachineryState state=new ExprMachineryState(); state.policy=vm.exprTransformsProfile(function);
        state.budget=new InstantiationBudget();
        ReplaceJob job=new ReplaceJob(); job.mode=EXPR_ABSTRACT_JOB; job.input=args[0];
        job.abstractArray=vm.array(args[args.length-1]); job.prefixLength=abstractPrefix(function,args);
        state.jobs.addLast(job); action.exprMachinery=state; vm.objects[action.slot]=null;
        // The parked native caller backs every borrowed input; no owned research
        // entry, argument vector, root reset or additional input INC is used.
    }
}
