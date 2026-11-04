package ansatz.lean.jvm.internal.exec;

import java.io.ByteArrayOutputStream;
import java.math.BigInteger;
import java.math.BigDecimal;
import java.math.RoundingMode;
import java.lang.ref.WeakReference;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.concurrent.atomic.AtomicLong;
import java.security.SecureRandom;
import java.security.ProviderException;
import ansatz.lean.jvm.internal.fs.FileSession;
import ansatz.lean.jvm.internal.exec.ExternRegistry.*;
import ansatz.lean.jvm.internal.exec.Interpreter.*;
import ansatz.lean.jvm.internal.exec.ExprDirectInstantiation.*;
import ansatz.lean.jvm.internal.exec.LevelInstantiation.*;
import ansatz.lean.jvm.internal.exec.ExprTransforms.*;
import static ansatz.lean.jvm.internal.exec.Interpreter.*;

/** Delayed-assignment instantiation session and the full instantiateMVars research
 * profile: scoped Expr caches, pending-name resolution, substitution install/restore
 * frames and delayed transforms, all as resumable budgeted steps. */
final class ExprDelayedInstantiation {
    private final Interpreter vm;

    ExprDelayedInstantiation(Interpreter vm) {
        this.vm=vm;
    }

    /* Scoped cache, resolver and substitution state for delayed expression
     * instantiation. Source authority remains with the trusted adapter. */
    private static final int DC_LOOKUP=2,DC_INSERT=3;
    private static final int MAX_DELAYED_KEYS=100_000,MAX_DELAYED_ENTRIES=100_000,MAX_DELAYED_GENERATIONS=100_000;
    static final int MAX_DELAYED_FRAMES=100_000,MAX_DELAYED_NAMES=100_000;
    static final int PENDING_IN_PROGRESS=0,PENDING_YES=1,PENDING_NO=2;
    static final int DELAYED_IDLE=0,DELAYED_RUNNING=1,DELAYED_RESULT=2,DELAYED_SEALED=3,DELAYED_DRAINED=4;
    /** Immutable and guest-reference-free. Fork may share these chains. */
    static final class ScopeGeneration {
        final int serial; final ScopeGeneration parent;
        ScopeGeneration(int serial,ScopeGeneration parent) { this.serial=serial; this.parent=parent; }
    }
    static final class ScopedEntry {
        ExprCredit result; ScopeGeneration generation;
        int validLevel,resultScope; boolean reserved;
    }
    static final class ScopedBucket {
        Node key; int depth; final ArrayList<ScopedEntry> entries=new ArrayList<>();
    }
    static final class ScopedExprCache {
        final IdentityHashMap<Node,HashMap<Integer,ScopedBucket>> index=new IdentityHashMap<>();
        final ArrayList<ScopedBucket> buckets=new ArrayList<>();
        ScopeGeneration current=new ScopeGeneration(0,null);
        int scope,generationCounter,generationCount=1,liveEntries;
        boolean sealed; int drainBucket,drainEntry; ScopedEntry retiringEntry;
    }
    /** computed aliases its caller's one owner flag; it is NOT another credit.
     * optional/shared/returned and retiringEntry each represent literal copies
     * or moved occurrences with distinct, resumable disposition. */
    static final class ScopedCacheOperation {
        ScopedBucket bucket; ScopedEntry top,retiringEntry,newEntry;
        ScopeGeneration currentCursor,entryCursor;
        ExprCredit computed,shared,optional,returned,replacement;
        Node key; int kind,depth,resultScope,stage,walkLevel,rewindStage; boolean hit,completed,rewound;
    }
    static final class PendingNameEntry {
        ExprCredit name; int hash,state;
    }
    static final class SubstitutionEntry {
        ExprCredit name,value; int hash,depth,scope; boolean live;
    }
    static final class SavedSubstitution {
        ExprCredit name,oldValue; int oldDepth,oldScope; boolean hadOld;
    }
    /** Shared production maintenance frame. saved records own independent old
     * copies and survive restoration; oldValue drains before its Name key. */
    static final class SubstitutionFrame {
        Object fvars,sourceArguments; final ArrayList<ExprCredit> arguments=new ArrayList<>();
        final ArrayList<SavedSubstitution> saved=new ArrayList<>();
        SubstitutionEntry existing,replacement; ExprCredit newName,newValue,retiringName,retiringValue;
        int depth,index,stage,cleanup; boolean scopePushed,restored,completed,ownsArguments,erasing;
    }
    /** Lookup/lift borrows the map entry value; a nested existing ReplaceJob
     * has no root input credit and must not INC merely to start the lift. */
    static final class SubstitutionLookup {
        Object name; SubstitutionEntry entry; ExprCredit optional,returned;
        int depth,stage; boolean present,completed;
    }
    abstract static class ResolverTask {
        ResolverTask child; ExprCredit received; int stage,cursor,cleanup;
        boolean result,completed;
    }
    static final class ResolvableExprFrame extends ResolverTask {
        Node original; boolean entryShared;
        ResolvableExprFrame(Node original) { this.original=original; }
    }
    static final class ResolvablePendingFrame extends ResolverTask {
        Object name; PendingNameEntry entry; ExprCredit option,temporary;
        ResolvablePendingFrame(Object name) { this.name=name; }
    }
    static final class ResolvableAppFrame extends ResolverTask {
        Node original; Object head,cursor; int argumentCount;
        ExprCredit option,recordTemporary,fvars,pendingName;
        ResolvableAppFrame(Node original) { this.original=original; }
    }
    static final class DelayedHelperPacket {
        Function function; Object[] arguments; boolean[] owned;
        ResolverTask target; DelayedTransformTask transformTarget; int role; boolean started,entered;
    }
    static final class DelayedSession {
        MVarContextCell context; InstantiationBudget budget; ExprInstantiationPolicy policy;
        ScopedExprCache cache=new ScopedExprCache();
        final IdentityHashMap<Node,Boolean> resolvableExpressions=new IdentityHashMap<>();
        final HashMap<Integer,ArrayList<PendingNameEntry>> pending=new HashMap<>();
        final ArrayList<PendingNameEntry> pendingOwners=new ArrayList<>();
        final ArrayList<ExprCredit> saved=new ArrayList<>();
        final HashMap<Integer,ArrayList<DirectNameEntry>> normalized=new HashMap<>();
        final ArrayList<DirectNameEntry> nameOwners=new ArrayList<>();
        final HashMap<Integer,ArrayList<SubstitutionEntry>> substitutions=new HashMap<>();
        final ArrayList<SubstitutionEntry> substitutionOwners=new ArrayList<>();
        final ArrayDeque<ResolverTask> resolver=new ArrayDeque<>();
        DelayedHelperPacket call; ExprPacket constructorCall;
        ScopedCacheOperation cacheOperation; SubstitutionFrame substitution; SubstitutionLookup lookup;
        final ArrayDeque<SubstitutionFrame> substitutionFrames=new ArrayDeque<>();
        ExprCredit retiring,result; int depth,resultScope,phase,drainStage,drainCursor;
        boolean booleanResult;
    }
    /* Complete two-pass expression instantiation, entered through the checked
     * native ABI and its configured source-bound helper policy. */
    static final boolean EXPR_INSTANTIATION_NATIVE_READY=true;
    static final int DT_IDLE=0,DT_RUNNING=1,DT_RESULT=2,DT_SEALED=3,DT_DRAINED=4;
    abstract static class DelayedTransformTask {
        DelayedTransformTask child;
        ExprCredit result,received;
        int stage,cleanup;
        boolean completed,helperDone;
    }
    /** NORMAL snapshots sharing and the caller watermark before child work.
     * Child occurrences stay owned until their literal case-block boundaries. */
    static final class DelayedVisitFrame extends DelayedTransformTask {
        Node original;
        int entryDepth,savedWatermark,cursor;
        boolean shared,cacheHit,skipInsert;
        final ExprCredit[] children=new ExprCredit[3];
        DelayedVisitFrame(Node original) { this.original=original; }
    }
    static final class DelayedFVarFrame extends DelayedTransformTask {
        Node original; Object name;
        DelayedFVarFrame(Node original) { this.original=original; }
    }
    /** A private optional result: present/result, never a fabricated guest Some. */
    static final class DelayedAssignmentFrame extends DelayedTransformTask {
        Object name;
        ExprCredit option,assigned,newValue;
        boolean present,outer;
        DelayedAssignmentFrame(Object name) { this.name=name; }
    }
    static final class DelayedAppFrame extends DelayedTransformTask {
        Node original; Object head,cursor;
        int argumentCount;
        ExprCredit option,recordTemporary,fvars,pendingName,discardedAssignment;
        DelayedAppFrame(Node original) { this.original=original; }
    }
    /** Prefix function Apps bypass NORMAL cache in both lookup and insertion. */
    static final class DelayedPrefixFrame extends DelayedTransformTask {
        Node original;
        ExprCredit argument,function;
        DelayedPrefixFrame(Node original) { this.original=original; }
    }
    static final class DelayedResolveFrame extends DelayedTransformTask {
        Node original;
        Object cursor,fvars,pendingName;
        final ArrayList<ExprCredit> arguments=new ArrayList<>();
        ExprCredit argumentTemporary,option,expressionTemporary,newValue,betaParameter;
        SubstitutionFrame substitutions;
        int argumentCount,extraCount;
        DelayedResolveFrame(Node original,Object fvars,Object pendingName) {
            this.original=original; this.fvars=fvars; this.pendingName=pendingName;
        }
    }
    /** This phase is independent of foundation.phase: the foundation may be
     * running its resolver/cache/substitution operation inside a live transform. */
    static final class DelayedTransform {
        DelayedSession foundation;
        final ArrayDeque<DelayedTransformTask> tasks=new ArrayDeque<>();
        Object input;
        ExprCredit result;
        int phase;
    }
    /** One cell and budget span both passes. Direct members survive through
     * delayed work and pair construction; e1 and e2 are separate occurrences. */
    static final class ExprFullResearchState {
        MVarContextCell context;
        InstantiationBudget budget;
        ExprDirectSession direct;
        DelayedTransform delayed;
        ExprCredit input,e1,e2,pair;
        int stage,pairFields;
    }
    void prepareExprFullAction(RuntimeAction action,ExprInstantiationPolicy policy,Object ownedContext,Node root) {
        ExprFullResearchState state=new ExprFullResearchState(); action.exprFull=state;
        state.context=new MVarContextCell(); state.context.current=new LevelCredit(ownedContext,true); state.budget=new InstantiationBudget();
        state.input=new ExprCredit(root,true); ExprDirectSession direct=new ExprDirectSession(); state.direct=direct;
        direct.context=state.context; direct.budget=state.budget; direct.policy=policy;
        direct.levels=vm.levels.newLevelSession(state.context,state.budget,policy.levels);
        direct.tasks.addLast(new DirectVisitFrame(root)); direct.phase=ExprDirectInstantiation.DS_RUNNING;
        vm.objects[action.slot]=null;
    }
    ExprInstantiationPolicy exprInstantiationProfile(Function function) {
        require(EXPR_INSTANTIATION_NATIVE_READY,"Full Expr native is not yet enabled");
        require(vm.explicit&&vm.taskRuntime!=null&&vm.exprInstantiationPolicy!=null,"Expr instantiation requires active explicit runtime and configured original helpers");
        ExprInstantiationPolicy policy=vm.exprInstantiationPolicy;
        require(policy.levels==vm.levelInstantiationPolicy,"Expr/Level configured policy identity differs");
        Header origin=function.header;
        require(origin!=null&&origin.source==policy.helpers[0].source&&origin.kind.equals("extern")
                &&origin.originalSha256.equals("7e53092b477181a60a5e66f6cf2e2f33827b9f05411b294359b860431fc8a9ef"),
                "Expr instantiation native source Header differs");
        Object name=Arrays.asList("str",Arrays.asList("str",Arrays.asList("anonymous"),"Lean"),"instantiateExprMVarsImp");
        require(origin.exactName.equals(frozenName(name)),"Expr instantiation native typed Name differs");
        for(int role=0;role<5;role++) { vm.levels.levelInstantiationHelper(policy.levels,role); vm.exprDirect.exprInstantiationHelper(policy,role); }
        for(int role=0;role<9;role++) vm.exprTransforms.exprConstructor(policy.constructors,role);
        return policy;
    }
    void validateExprInstantiationArguments(Function function,Object[] args) {
        exprInstantiationProfile(function);
        require(args!=null&&args.length==2,"Expr instantiation native arity differs");
        vm.validateHostObject(args[0]); Node root=vm.exprNode(args[1]);
        if(args[0]==args[1]) require(root.refCount()==0||root.refCount()>=2,"Expr instantiation input alias credits differ");
    }
    ExprDirectSession currentDirectSession(RuntimeAction action) {
        return action==null?null:action.exprFull!=null&&(action.exprFull.stage==0||action.exprFull.stage>=5)?action.exprFull.direct:null;
    }
    DelayedSession currentDelayedSession(RuntimeAction action) {
        return action==null?null:action.exprFull!=null&&action.exprFull.delayed!=null&&action.exprFull.stage>=3&&action.exprFull.stage<=4
                        ?action.exprFull.delayed.foundation:null;
    }
    private boolean delayedOuterMode(DelayedSession session) { return session.substitutions.isEmpty(); }
    private boolean delayedNormalizedContains(DelayedSession session,Object name) {
        int hash=delayedNameHash(session,name); ArrayList<DirectNameEntry> bucket=session.normalized.get(hash);
        if(bucket!=null) for(DirectNameEntry entry:bucket) {
            delayedWork(session,1); require(entry.name.owned,"Delayed normalized Name owner missing");
            if(mvarNameEqual(session.budget,name,entry.name.value)) return true;
        }
        return false;
    }
    private void delayedNormalizedInsert(DelayedSession session,Object name) {
        int hash=delayedNameHash(session,name); ArrayList<DirectNameEntry> bucket=session.normalized.get(hash);
        if(bucket!=null) for(DirectNameEntry entry:bucket) {
            delayedWork(session,1); if(mvarNameEqual(session.budget,name,entry.name.value)) return;
        }
        require(session.nameOwners.size()<MAX_DELAYED_NAMES,"Delayed normalized Name bound");
        DirectNameEntry entry=new DirectNameEntry(hash,vm.exprTransforms.exprCredit(name)); session.nameOwners.add(entry);
        if(bucket==null) { bucket=new ArrayList<>(); session.normalized.put(hash,bucket); }
        bucket.add(entry); vm.exprTransforms.acquireExpr(entry.name);
    }
    void pushTransform(DelayedTransform transform,DelayedTransformTask task) {
        require(transform.phase==DT_RUNNING&&transform.tasks.size()<MAX_DELAYED_FRAMES,"Delayed transform task bound");
        transform.tasks.addLast(task);
    }
    private ExprCredit takeTransformChild(DelayedTransformTask parent,Class<?> expected) {
        DelayedTransformTask child=parent.child;
        require(child!=null&&child.completed&&expected.isInstance(child)&&child.result!=null&&child.result.owned,
                "Delayed transform child receiver differs");
        ExprCredit result=child.result; child.result=null; parent.child=null; return result;
    }
    private DelayedAssignmentFrame takeTransformAssignment(DelayedTransformTask parent) {
        require(parent.child instanceof DelayedAssignmentFrame&&parent.child.completed,"Delayed optional assignment not ready");
        DelayedAssignmentFrame child=(DelayedAssignmentFrame)parent.child; parent.child=null;
        require(!child.present||child.result!=null&&child.result.owned,"Delayed private optional result owner missing"); return child;
    }
    private void transformSelect(DelayedTransformTask frame,Object value) { frame.result=vm.exprTransforms.exprCredit(value); vm.exprTransforms.acquireExpr(frame.result); }
    private void callTransformHelper(RuntimeAction action,DelayedSession session,DelayedTransformTask target,int role,Object name,Object record,ExprCredit newValue) {
        delayedWork(session,1); require(role>=0&&role<=4,"Delayed transform helper role differs"); requireDelayedReceiverFree(action,session);
        Function helper=vm.exprDirect.exprInstantiationHelper(session.policy,role);
        DelayedHelperPacket packet=new DelayedHelperPacket(); packet.function=helper; packet.role=role; packet.transformTarget=target;
        packet.arguments=new Object[helper.params.length]; packet.owned=new boolean[packet.arguments.length];
        if(role==2||role==3) packet.arguments[0]=record;
        else {
            require(session.context.current!=null&&session.context.current.owned,"Delayed transform context absent");
            packet.arguments[0]=session.context.current.value; packet.arguments[1]=name; vm.nameNode(name);
            if(role==4) { require(newValue!=null&&newValue.owned,"Delayed setter value absent"); packet.arguments[2]=newValue.value; vm.exprNode(newValue.value); }
        }
        for(Object argument:packet.arguments) vm.validateHostObject(argument);
        session.call=packet;
        for(int i=0;i<packet.arguments.length;i++) {
            if(role==4&&i==0) { packet.owned[i]=true; session.context.current.owned=false; session.context.current=null; }
            else { vm.inc(packet.arguments[i],1); packet.owned[i]=true; }
        }
        IdentityHashMap<Node,Integer> known=new IdentityHashMap<>();
        for(Object argument:packet.arguments) if(argument instanceof Node) known.merge((Node)argument,1,Integer::sum);
        for(Map.Entry<Node,Integer> entry:known.entrySet()) require(entry.getKey().refCount()==0||entry.getKey().refCount()>=entry.getValue(),"Delayed helper owner aliases differ");
        packet.started=true; vm.enterExplicit(helper,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Delayed transform helper did not publish frame/CodeRequest");
    }
    private void receiveTransformHelper(RuntimeAction action,DelayedSession session) {
        DelayedHelperPacket packet=session.call;
        require(packet!=null&&packet.entered&&packet.target==null&&packet.transformTarget!=null,"Delayed transform helper target differs");
        Object value=vm.objects[action.slot]; DelayedTransformTask target=packet.transformTarget;
        if(packet.role==4) {
            vm.validateHostObject(value); require(session.context.current==null,"Delayed setter replaces owned context");
            session.context.current=new LevelCredit(value,true); vm.objects[action.slot]=null; target.helperDone=true;
        } else {
            require(target.received==null,"Delayed transform helper receiver occupied");
            if(packet.role<=1) vm.exprDirect.validateDirectOption(value,packet.role==0);
            else if(packet.role==2) { Node array=vm.exprTransforms.pureExprArray(value); require(array.arraySize()<=MAX_DELAYED_NAMES,"Delayed fvars Array bound"); }
            else vm.nameNode(value);
            target.received=new ExprCredit(value,true); vm.objects[action.slot]=null;
        }
        session.call=null;
    }
    private void callTransformConstructor(RuntimeAction action,DelayedSession session,DelayedTransformTask target,int role,Object[] values) {
        delayedWork(session,1); requireDelayedReceiverFree(action,session);
        ExprPacket packet=vm.exprTransforms.prepareExprConstructorPacket(session.policy.constructors,role,values); packet.delayedTarget=target;
        session.constructorCall=packet; vm.exprTransforms.acquireExprConstructorPacket(packet); packet.started=true;
        vm.enterExplicit(packet.function,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Delayed constructor did not publish frame/CodeRequest");
    }
    private void receiveTransformConstructor(RuntimeAction action,DelayedSession session) {
        ExprPacket packet=session.constructorCall;
        require(packet!=null&&packet.entered&&packet.delayedTarget!=null&&packet.delayedTarget.received==null,"Delayed constructor receiver differs");
        ExprCredit result=vm.exprTransforms.takeExprConstructorResult(action,packet); packet.delayedTarget.received=result; session.constructorCall=null;
    }
    private void stepTransformFVar(RuntimeAction action,DelayedTransform transform,DelayedFVarFrame frame) {
        DelayedSession session=transform.foundation;
        if(frame.stage==0) {
            require(session.lookup==null,"Delayed FVar lookup occupied"); SubstitutionLookup lookup=new SubstitutionLookup();
            lookup.name=frame.original.storageField(0); lookup.depth=session.depth; session.lookup=lookup; frame.stage=1; return;
        }
        SubstitutionLookup lookup=session.lookup; require(lookup!=null,"Delayed FVar lookup missing");
        stepSubstitutionLookup(action,session,lookup); if(!lookup.completed) return;
        if(lookup.present) { require(lookup.returned!=null&&lookup.returned.owned,"Delayed FVar returned owner absent"); frame.result=lookup.returned; lookup.returned=null; }
        else transformSelect(frame,frame.original);
        session.lookup=null; frame.completed=true;
    }
    private void stepTransformAssignment(RuntimeAction action,DelayedTransform transform,DelayedAssignmentFrame frame) {
        DelayedSession session=transform.foundation;
        if(frame.stage==0) { frame.stage=1; callTransformHelper(action,session,frame,0,frame.name,null,null); return; }
        if(frame.stage==1) {
            require(frame.received!=null&&frame.received.owned,"Delayed assignment Option absent"); frame.option=frame.received; frame.received=null;
            if(ERASED.equals(frame.option.value)) { frame.present=false; frame.stage=20; return; }
            frame.assigned=vm.exprTransforms.exprCredit(((Node)frame.option.value).storageField(0)); vm.exprTransforms.acquireExpr(frame.assigned); frame.outer=delayedOuterMode(session);
            if(frame.outer&&delayedNormalizedContains(session,frame.name)) {
                transformSelect(frame,frame.assigned.value); frame.present=true; frame.stage=20; return;
            }
            if(frame.outer) delayedNormalizedInsert(session,frame.name);
            frame.stage=2; pushTransform(transform,new DelayedVisitFrame(vm.exprNode(frame.assigned.value))); return;
        }
        if(frame.stage==2) {
            frame.newValue=takeTransformChild(frame,DelayedVisitFrame.class);
            if(frame.outer&&frame.newValue.value!=frame.assigned.value) {
                require(session.saved.size()<ExprDirectInstantiation.MAX_DIRECT_SAVED,"Delayed saved assignment bound");
                ExprCredit saved=vm.exprTransforms.exprCredit(frame.assigned.value); session.saved.add(saved); vm.exprTransforms.acquireExpr(saved);
                frame.stage=3; callTransformHelper(action,session,frame,4,frame.name,null,frame.newValue); return;
            }
            frame.stage=4;
        }
        if(frame.stage==3) { require(frame.helperDone,"Delayed setter completion absent"); frame.stage=4; }
        if(frame.stage==4) {
            if(frame.outer) transformSelect(frame,frame.newValue.value);
            else { frame.result=frame.newValue; frame.newValue=null; }
            frame.present=true; frame.stage=20;
        }
        if(frame.stage==20) { frame.stage=21; releaseDelayed(action,session,frame.newValue); return; }
        if(frame.stage==21) { frame.stage=22; releaseDelayed(action,session,frame.assigned); return; }
        if(frame.stage==22) { frame.stage=23; releaseDelayed(action,session,frame.option); return; }
        require(frame.stage==23,"Delayed assignment continuation differs");
        frame.newValue=null; frame.assigned=null; frame.option=null; frame.completed=true;
    }
    private void stepTransformPrefix(RuntimeAction action,DelayedTransform transform,DelayedPrefixFrame frame) {
        DelayedSession session=transform.foundation;
        if(frame.stage==0) { frame.stage=1; pushTransform(transform,new DelayedVisitFrame(vm.exprNode(frame.original.storageField(1)))); return; }
        if(frame.stage==1) {
            frame.argument=takeTransformChild(frame,DelayedVisitFrame.class); Node f=vm.exprNode(frame.original.storageField(0)); frame.stage=2;
            pushTransform(transform,f.storageTag()==5?new DelayedPrefixFrame(f):new DelayedVisitFrame(f)); return;
        }
        if(frame.stage==2) {
            frame.function=takeTransformChild(frame,vm.exprNode(frame.original.storageField(0)).storageTag()==5?DelayedPrefixFrame.class:DelayedVisitFrame.class);
            if(frame.function.value==frame.original.storageField(0)&&frame.argument.value==frame.original.storageField(1)) { transformSelect(frame,frame.original); frame.stage=4; }
            else { frame.stage=3; callTransformConstructor(action,session,frame,3,new Object[]{frame.function.value,frame.argument.value}); return; }
        }
        if(frame.stage==3) { require(frame.received!=null&&frame.received.owned,"Delayed App constructor result absent"); frame.result=frame.received; frame.received=null; frame.stage=4; }
        if(frame.stage==4) { frame.stage=5; releaseDelayed(action,session,frame.function); return; }
        if(frame.stage==5) { frame.stage=6; releaseDelayed(action,session,frame.argument); return; }
        require(frame.stage==6,"Delayed prefix continuation differs"); frame.function=null; frame.argument=null; frame.completed=true;
    }
    private void stepTransformApp(RuntimeAction action,DelayedTransform transform,DelayedAppFrame frame) {
        DelayedSession session=transform.foundation;
        if(frame.stage==0) {
            frame.head=frame.original; frame.argumentCount=0; frame.stage=1;
        }
        if(frame.stage==1) {
            Node head=vm.exprNode(frame.head);
            if(head.storageTag()==5) { require(frame.argumentCount<ExprDirectInstantiation.MAX_DIRECT_ARGUMENTS,"Delayed App spine bound"); frame.argumentCount++; frame.head=head.storageField(0); return; }
            if(head.storageTag()!=2) { frame.stage=20; pushTransform(transform,new DelayedPrefixFrame(frame.original)); return; }
            frame.stage=2; callTransformHelper(action,session,frame,1,head.storageField(0),null,null); return;
        }
        if(frame.stage==2) {
            require(frame.received!=null&&frame.received.owned,"Delayed App Option absent"); frame.option=frame.received; frame.received=null;
            if(ERASED.equals(frame.option.value)) { frame.stage=20; pushTransform(transform,new DelayedPrefixFrame(frame.original)); return; }
            frame.recordTemporary=vm.exprTransforms.exprCredit(((Node)frame.option.value).storageField(0)); vm.exprTransforms.acquireExpr(frame.recordTemporary);
            frame.stage=3; callTransformHelper(action,session,frame,2,null,frame.recordTemporary.value,null); return;
        }
        if(frame.stage==3) {
            require(frame.received!=null&&frame.received.owned,"Delayed App fvars absent"); frame.fvars=frame.received; frame.received=null;
            frame.stage=4; releaseDelayed(action,session,frame.recordTemporary); return;
        }
        if(frame.stage==4) {
            frame.recordTemporary=vm.exprTransforms.exprCredit(((Node)frame.option.value).storageField(0)); vm.exprTransforms.acquireExpr(frame.recordTemporary);
            frame.stage=5; callTransformHelper(action,session,frame,3,null,frame.recordTemporary.value,null); return;
        }
        if(frame.stage==5) {
            require(frame.received!=null&&frame.received.owned,"Delayed App pending Name absent"); frame.pendingName=frame.received; frame.received=null;
            frame.stage=6; releaseDelayed(action,session,frame.recordTemporary); return;
        }
        if(frame.stage==6) {
            frame.recordTemporary=null;
            if(((Node)frame.fvars.value).arraySize()>frame.argumentCount) { frame.stage=20; pushTransform(transform,new DelayedPrefixFrame(frame.original)); return; }
            require(session.phase==DELAYED_IDLE&&session.resolver.isEmpty(),"Delayed pending resolver occupied");
            session.phase=DELAYED_RUNNING; pushResolver(session,new ResolvablePendingFrame(frame.pendingName.value)); frame.stage=7; return;
        }
        if(frame.stage==7) {
            stepResolver(action,session); if(session.phase!=DELAYED_RESULT) return;
            if(takeResolverResult(session)) {
                frame.stage=21; pushTransform(transform,new DelayedResolveFrame(frame.original,frame.fvars.value,frame.pendingName.value)); return;
            }
            require(delayedOuterMode(session),"Unresolvable delayed App in inner mode outside source profile");
            frame.stage=8; pushTransform(transform,new DelayedAssignmentFrame(frame.pendingName.value)); return;
        }
        if(frame.stage==8) {
            DelayedAssignmentFrame assignment=takeTransformAssignment(frame); frame.discardedAssignment=assignment.result; assignment.result=null;
            frame.stage=9; releaseDelayed(action,session,frame.discardedAssignment); return;
        }
        if(frame.stage==9) { frame.discardedAssignment=null; frame.stage=20; pushTransform(transform,new DelayedPrefixFrame(frame.original)); return; }
        if(frame.stage==20||frame.stage==21) { frame.result=takeTransformChild(frame,frame.stage==20?DelayedPrefixFrame.class:DelayedResolveFrame.class); frame.stage=30; }
        if(frame.stage==30) { frame.stage=31; releaseDelayed(action,session,frame.pendingName); return; }
        if(frame.stage==31) { frame.stage=32; releaseDelayed(action,session,frame.fvars); return; }
        if(frame.stage==32) { frame.stage=33; releaseDelayed(action,session,frame.option); return; }
        require(frame.stage==33,"Delayed App continuation differs"); frame.pendingName=null; frame.fvars=null; frame.option=null; frame.completed=true;
    }
    private void enterTransformBeta(RuntimeAction parent,DelayedTransform transform,DelayedResolveFrame frame) {
        DelayedSession session=transform.foundation;
        require(vm.runtimeAction==parent&&vm.objects[parent.slot]==null&&session.call==null&&session.constructorCall==null&&session.retiring==null,
                "Delayed beta receiver occupied");
        require(frame.betaParameter!=null&&frame.betaParameter.owned,"Delayed beta parameter absent");
        for(int role=0;role<9;role++) vm.exprTransforms.exprConstructor(session.policy.constructors,role);
        RuntimeAction child=vm.newAction(ACTION_EXPR_MACHINERY,null,ACTION_BODY,parent.slot,ASSIGN,null);
        ExprMachineryState worker=new ExprMachineryState(); worker.policy=session.policy.constructors; worker.budget=session.budget;
        BetaJob beta=new BetaJob(); beta.function=frame.betaParameter; beta.reverseArgs=new Object[frame.extraCount];
        for(int i=0;i<beta.reverseArgs.length;i++) {
            ExprCredit arg=frame.arguments.get(i); require(arg.owned,"Delayed beta reverse argument backing absent"); beta.reverseArgs[i]=arg.value;
        }
        worker.jobs.addLast(beta); child.exprMachinery=worker; vm.objects[child.slot]=null;
        vm.publishAction(child); frame.betaParameter=null;
    }
    private void stepTransformResolve(RuntimeAction action,DelayedTransform transform,DelayedResolveFrame frame) {
        DelayedSession session=transform.foundation;
        if(frame.stage==0) {
            if(frame.cursor==null) frame.cursor=frame.original;
            Node cursor=vm.exprNode(frame.cursor);
            if(cursor.storageTag()==5) { frame.stage=1; pushTransform(transform,new DelayedVisitFrame(vm.exprNode(cursor.storageField(1)))); return; }
            Node fvars=vm.exprTransforms.pureExprArray(frame.fvars); int n=fvars.arraySize();
            require(n<=frame.arguments.size(),"Delayed resolve argument arity differs"); frame.extraCount=frame.arguments.size()-n;
            require(session.substitution==null&&session.substitutionFrames.size()<MAX_DELAYED_FRAMES,"Delayed resolve substitution receiver occupied");
            SubstitutionFrame install=new SubstitutionFrame(); frame.substitutions=install;
            install.fvars=fvars; install.depth=session.depth; install.ownsArguments=false; install.arguments.addAll(frame.arguments);
            install.stage=SF_ENTER; session.substitution=install; frame.stage=3; return;
        }
        if(frame.stage==1) {
            frame.argumentTemporary=takeTransformChild(frame,DelayedVisitFrame.class);
            require(frame.arguments.size()<ExprDirectInstantiation.MAX_DIRECT_ARGUMENTS,"Delayed reverse argument buffer bound");
            ExprCredit copy=vm.exprTransforms.exprCredit(frame.argumentTemporary.value); frame.arguments.add(copy); vm.exprTransforms.acquireExpr(copy);
            frame.stage=2; releaseDelayed(action,session,frame.argumentTemporary); return;
        }
        if(frame.stage==2) { frame.argumentTemporary=null; frame.cursor=vm.exprNode(frame.cursor).storageField(0); frame.stage=0; return; }
        if(frame.stage==3) {
            SubstitutionFrame install=frame.substitutions; require(session.substitution==install,"Delayed install current frame differs");
            stepSubstitutionInstall(action,session,install); if(!install.completed) return;
            session.substitution=null; session.substitutionFrames.addLast(install);
            frame.stage=4; callTransformHelper(action,session,frame,0,frame.pendingName,null,null); return;
        }
        if(frame.stage==4) {
            require(frame.received!=null&&frame.received.owned,"Delayed pending Option absent"); frame.option=frame.received; frame.received=null;
            require(!ERASED.equals(frame.option.value),"Resolvable pending assignment missing outside source profile");
            frame.expressionTemporary=vm.exprTransforms.exprCredit(((Node)frame.option.value).storageField(0)); vm.exprTransforms.acquireExpr(frame.expressionTemporary);
            frame.stage=5; pushTransform(transform,new DelayedVisitFrame(vm.exprNode(frame.expressionTemporary.value))); return;
        }
        if(frame.stage==5) {
            frame.newValue=takeTransformChild(frame,DelayedVisitFrame.class); frame.stage=6;
            releaseDelayed(action,session,frame.expressionTemporary); return;
        }
        if(frame.stage==6) {
            frame.expressionTemporary=null;
            require(session.substitution==null&&session.substitutionFrames.peekLast()==frame.substitutions,"Delayed scope restore order differs");
            session.substitution=frame.substitutions; beginSubstitutionRestore(session,frame.substitutions); frame.stage=7; return;
        }
        if(frame.stage==7) {
            stepSubstitutionRestore(action,session,frame.substitutions); if(!frame.substitutions.completed) return;
            session.substitution=null; require(session.substitutionFrames.removeLast()==frame.substitutions,"Delayed restored scope differs");
            frame.betaParameter=vm.exprTransforms.exprCredit(frame.newValue.value); vm.exprTransforms.acquireExpr(frame.betaParameter); frame.stage=8;
            enterTransformBeta(action,transform,frame); return;
        }
        if(frame.stage==8) {
            Object value=vm.objects[action.slot]; vm.exprNode(value); frame.result=new ExprCredit(value,true); vm.objects[action.slot]=null;
            frame.stage=9; releaseDelayed(action,session,frame.newValue); return;
        }
        if(frame.stage==9) { frame.newValue=null; frame.stage=10; releaseDelayed(action,session,frame.option); return; }
        if(frame.stage==10) {
            frame.option=null; stepSubstitutionFrameDrain(action,session,frame.substitutions);
            if(!frame.substitutions.completed||frame.substitutions.stage!=SF_DRAINED) return;
            frame.substitutions=null; frame.cleanup=0; frame.stage=11; return;
        }
        if(frame.stage==11) {
            if(frame.cleanup<frame.arguments.size()) { ExprCredit arg=frame.arguments.get(frame.cleanup++); releaseDelayed(action,session,arg); return; }
            frame.arguments.clear(); frame.fvars=null; frame.pendingName=null; frame.cursor=null; frame.completed=true; return;
        }
        throw error("Delayed resolution continuation differs");
    }
    private void transformCompositeResult(RuntimeAction action,DelayedTransform transform,DelayedVisitFrame frame) {
        Node original=frame.original; Object[] values=original.copyFields(); boolean changed=false;
        int count=ExprTransforms.exprChildCount(original.storageTag());
        for(int i=0;i<count;i++) {
            require(frame.children[i]!=null&&frame.children[i].owned,"Delayed composite child owner absent");
            int at=ExprTransforms.exprChildField(original.storageTag(),i); values[at]=frame.children[i].value; changed|=values[at]!=original.storageField(at);
        }
        if(!changed) { transformSelect(frame,original); frame.stage=30; return; }
        if(original.storageTag()>=6&&original.storageTag()<=8) { values=Arrays.copyOf(values,values.length+1); values[values.length-1]=Long.valueOf(original.storageByte(8)); }
        frame.stage=21; callTransformConstructor(action,transform.foundation,frame,ExprTransforms.exprCtorRole(original.storageTag()),values);
    }
    private void stepTransformVisit(RuntimeAction action,DelayedTransform transform,DelayedVisitFrame frame) {
        DelayedSession session=transform.foundation; Node original=frame.original;
        if(frame.stage==0) {
            frame.entryDepth=session.depth; long word=vm.exprCachedData(original);
            if(((word&(1L<<40))==0||delayedOuterMode(session))&&(word&(1L<<41))==0) {
                transformSelect(frame,original); frame.stage=51; return;
            }
            frame.shared=!exclusive(original);
            if(frame.shared) { startScopedOperation(session,DC_LOOKUP,original,frame.entryDepth,null,0); frame.stage=1; return; }
            frame.stage=2;
        }
        if(frame.stage==1) {
            ScopedCacheOperation op=session.cacheOperation; require(op!=null,"Delayed lookup operation absent");
            stepScopedCache(action,session); if(!op.completed) return;
            session.cacheOperation=null;
            if(op.hit) { require(op.returned!=null&&op.returned.owned,"Delayed cache hit return absent"); frame.result=op.returned; op.returned=null; frame.cacheHit=true; frame.stage=51; return; }
            frame.stage=2;
        }
        if(frame.stage==2) {
            frame.savedWatermark=session.resultScope; session.resultScope=0;
            switch(original.storageTag()) {
                case 1: frame.skipInsert=true; frame.stage=10; pushTransform(transform,new DelayedFVarFrame(original)); return;
                case 2:
                    require(delayedOuterMode(session),"Bare Expr MVar in inner mode outside source profile");
                    frame.skipInsert=true; transformSelect(frame,original); frame.stage=40; return;
                case 5: frame.stage=10; pushTransform(transform,new DelayedAppFrame(original)); return;
                case 6: case 7: case 8: case 10: case 11: frame.stage=20; break;
                default: throw error("Contradictory delayed Expr flags on atomic storage");
            }
        }
        if(frame.stage==10) {
            frame.result=takeTransformChild(frame,original.storageTag()==1?DelayedFVarFrame.class:DelayedAppFrame.class); frame.stage=40;
        }
        if(frame.stage==20) {
            int count=ExprTransforms.exprChildCount(original.storageTag());
            if(frame.child!=null) {
                require(frame.cursor<count,"Delayed child cursor outside layout"); frame.children[frame.cursor]=takeTransformChild(frame,DelayedVisitFrame.class); frame.cursor++;
            }
            if(frame.cursor<count) {
                boolean body=original.storageTag()>=6&&original.storageTag()<=8&&frame.cursor==count-1;
                require(frame.entryDepth<ExprTransforms.MAX_EXPR_JOB_OFFSET||!body,"Delayed binder depth bound");
                session.depth=frame.entryDepth+(body?1:0);
                pushTransform(transform,new DelayedVisitFrame(vm.exprNode(original.storageField(ExprTransforms.exprChildField(original.storageTag(),frame.cursor))))); return;
            }
            session.depth=frame.entryDepth; transformCompositeResult(action,transform,frame); return;
        }
        if(frame.stage==21) {
            require(frame.received!=null&&frame.received.owned,"Delayed composite constructor return absent");
            frame.result=frame.received; frame.received=null; frame.stage=30;
        }
        if(frame.stage==30) {
            int count=ExprTransforms.exprChildCount(original.storageTag());
            if(frame.cleanup<count) { ExprCredit child=frame.children[count-1-frame.cleanup++]; releaseDelayed(action,session,child); return; }
            Arrays.fill(frame.children,null); frame.stage=40;
        }
        if(frame.stage==40) {
            require(session.depth==frame.entryDepth&&frame.result!=null&&frame.result.owned,"Delayed insertion depth/result differs");
            if(frame.shared&&!frame.skipInsert) {
                ExprCredit computed=frame.result;
                // The operation aliases this exact moved occurrence, not a new credit.
                startScopedOperation(session,DC_INSERT,original,frame.entryDepth,computed,session.resultScope); frame.result=null; frame.stage=41; return;
            }
            frame.stage=50;
        }
        if(frame.stage==41) {
            ScopedCacheOperation op=session.cacheOperation; require(op!=null,"Delayed insertion operation absent");
            stepScopedCache(action,session); if(!op.completed) return;
            require(op.returned!=null&&op.returned.owned,"Delayed insertion returned owner absent");
            frame.result=op.returned; op.returned=null; session.cacheOperation=null; frame.stage=50;
        }
        if(frame.stage==50) { session.resultScope=Math.max(frame.savedWatermark,session.resultScope); frame.stage=51; }
        require(frame.stage==51&&frame.result!=null&&frame.result.owned,"Delayed NORMAL result absent"); frame.completed=true;
    }
    void stepDelayedTransform(RuntimeAction action,DelayedTransform transform) {
        DelayedSession session=transform.foundation; delayedWork(session,1); resumeDelayedRetiring(action,session);
        require(transform.phase==DT_RUNNING,"Delayed transform not running");
        if(session.call!=null&&session.call.transformTarget!=null) { receiveTransformHelper(action,session); return; }
        if(session.constructorCall!=null) { receiveTransformConstructor(action,session); return; }
        DelayedTransformTask task=transform.tasks.peekLast(); require(task!=null,"Delayed transform frame absent");
        if(!task.completed) {
            if(task instanceof DelayedVisitFrame) stepTransformVisit(action,transform,(DelayedVisitFrame)task);
            else if(task instanceof DelayedFVarFrame) stepTransformFVar(action,transform,(DelayedFVarFrame)task);
            else if(task instanceof DelayedAssignmentFrame) stepTransformAssignment(action,transform,(DelayedAssignmentFrame)task);
            else if(task instanceof DelayedAppFrame) stepTransformApp(action,transform,(DelayedAppFrame)task);
            else if(task instanceof DelayedPrefixFrame) stepTransformPrefix(action,transform,(DelayedPrefixFrame)task);
            else stepTransformResolve(action,transform,(DelayedResolveFrame)task);
            return;
        }
        Iterator<DelayedTransformTask> iterator=transform.tasks.descendingIterator(); iterator.next();
        DelayedTransformTask parent=iterator.hasNext()?iterator.next():null;
        if(parent==null) {
            require(task instanceof DelayedVisitFrame&&task.result!=null&&task.result.owned&&transform.result==null
                    &&session.context.current!=null&&session.context.current.owned&&session.phase==DELAYED_IDLE,
                    "Delayed transform root ownership differs");
            transform.result=task.result; task.result=null; transform.phase=DT_RESULT;
        } else { require(parent.child==null,"Delayed transform parent receiver occupied"); parent.child=task; }
        transform.tasks.removeLast();
    }
    ExprCredit takeDelayedTransformResult(DelayedTransform transform) {
        require(transform.phase==DT_RESULT&&transform.tasks.isEmpty()&&transform.result!=null&&transform.result.owned,
                "Delayed transform result unavailable");
        ExprCredit result=transform.result; transform.result=null; transform.input=null; transform.phase=DT_IDLE; return result;
    }
    void delayedWork(DelayedSession session,long amount) {
        vm.exprTransforms.instantiationWork(session.budget,amount,"Delayed Expr work outside bounded runtime profile","Delayed Expr interrupted");
    }
    private void requireDelayedReceiverFree(RuntimeAction action,DelayedSession session) {
        require(vm.runtimeAction==action&&currentDelayedSession(action)==session
                &&session.call==null&&session.constructorCall==null&&vm.objects[action.slot]==null,
                "Multiple outstanding delayed helper/constructor packets");
    }
    void delayedHelperEntry(Function function,Object[] arguments) {
        RuntimeAction action=vm.runtimeAction;
        DelayedSession session=currentDelayedSession(action);
        if(session==null) return;
        DelayedHelperPacket packet=session.call;
        if(packet==null||packet.entered||packet.function!=function||packet.arguments!=arguments) return;
        require(packet.started,"Delayed helper entered before packet publication");
        packet.entered=true; Arrays.fill(packet.owned,false);
    }
    private boolean releaseDelayed(RuntimeAction action,DelayedSession session,ExprCredit credit) {
        if(credit==null||!credit.owned) return false;
        require(session.retiring==null,"Two delayed retiring occurrences");
        session.retiring=credit; action.retiring=credit.value; action.releaseClaimed=false;
        boolean dispatch;
        try { dispatch=vm.beginRelease(credit.value,1,ACTION_BODY); credit.owned=false; }
        finally { if(action.releaseClaimed) credit.owned=false; }
        if(!dispatch) { session.retiring=null; action.retiring=null; action.releaseClaimed=false; }
        return dispatch;
    }
    private void resumeDelayedRetiring(RuntimeAction action,DelayedSession session) {
        if(session.retiring!=null) {
            require(!session.retiring.owned,"Delayed retiring occurrence was not claimed");
            session.retiring=null; action.retiring=null; action.releaseClaimed=false;
        }
    }
    boolean mvarNameEqual(InstantiationBudget budget,Object left,Object right) {
        ExprEquality comparison=vm.new ExprEquality(false); comparison.work=budget.work;
        try { return vm.nameEquals(left,right,comparison); }
        finally { budget.work=comparison.work; }
    }
    int delayedNameHash(DelayedSession session,Object value) {
        delayedWork(session,1); Node name=vm.nameNode(value); return (int)(name==null?1723:readScalar(name,0,U64));
    }
    private void scopedPush(DelayedSession session) {
        delayedWork(session,1); ScopedExprCache cache=session.cache;
        require(!cache.sealed&&cache.generationCount<MAX_DELAYED_GENERATIONS&&cache.scope<MAX_DELAYED_GENERATIONS
                &&cache.generationCounter<Integer.MAX_VALUE,"Scoped Expr generation bound");
        ScopeGeneration next=new ScopeGeneration(cache.generationCounter+1,cache.current);
        cache.current=next; cache.generationCounter++; cache.generationCount++; cache.scope++;
    }
    private void scopedPop(DelayedSession session) {
        delayedWork(session,1); ScopedExprCache cache=session.cache;
        require(!cache.sealed&&cache.scope>0&&cache.current!=null&&cache.current.parent!=null,"Scoped Expr pop outside active scope");
        cache.current=cache.current.parent; cache.scope--;
    }
    private ScopedBucket scopedBucket(DelayedSession session,Node key,int depth,boolean create) {
        delayedWork(session,1); ScopedExprCache cache=session.cache;
        require(!cache.sealed&&depth>=0&&depth<=ExprTransforms.MAX_EXPR_JOB_OFFSET,"Scoped Expr key outside profile");
        HashMap<Integer,ScopedBucket> depths=cache.index.get(key); ScopedBucket bucket=depths==null?null:depths.get(depth);
        if(bucket!=null||!create) return bucket;
        require(cache.buckets.size()<MAX_DELAYED_KEYS,"Scoped Expr (identity,depth) key bound");
        bucket=new ScopedBucket(); bucket.key=key; bucket.depth=depth; cache.buckets.add(bucket);
        if(depths==null) { depths=new HashMap<>(); cache.index.put(key,depths); }
        depths.put(depth,bucket); return bucket;
    }
    private void startScopedOperation(DelayedSession session,int kind,Object key,int depth,ExprCredit computed,int resultScope) {
        require(session.cacheOperation==null&&session.call==null&&session.constructorCall==null,"Scoped Expr operation already active");
        require(kind==DC_LOOKUP||kind==DC_INSERT,"Unknown scoped Expr operation");
        Node original=vm.exprNode(key);
        if(kind==DC_INSERT) require(computed!=null&&computed.owned&&resultScope>=0&&resultScope<=MAX_DELAYED_GENERATIONS,
                "Scoped Expr computed/result-scope owner missing");
        ScopedCacheOperation op=new ScopedCacheOperation(); op.kind=kind; op.key=original; op.depth=depth;
        op.computed=computed; op.resultScope=resultScope; session.cacheOperation=op;
        op.bucket=scopedBucket(session,original,depth,kind==DC_INSERT);
    }
    private void finishScopedRetiring(DelayedSession session,ScopedCacheOperation op) {
        if(op.retiringEntry==null) return;
        ScopedEntry entry=op.retiringEntry;
        require(entry.result!=null&&!entry.result.owned,"Scoped Expr eviction owner not drained");
        if(entry.reserved) { require(session.cache.liveEntries>0,"Scoped Expr reservation underflow"); session.cache.liveEntries--; entry.reserved=false; }
        entry.result=null; op.retiringEntry=null;
    }
    private void dropScopedTop(RuntimeAction action,DelayedSession session,ScopedCacheOperation op) {
        require(op.retiringEntry==null&&op.bucket!=null&&!op.bucket.entries.isEmpty(),"Missing scoped eviction entry");
        op.retiringEntry=op.bucket.entries.remove(op.bucket.entries.size()-1); op.top=null; op.rewindStage=0;
        releaseDelayed(action,session,op.retiringEntry.result);
    }
    private void stepScopedRewind(RuntimeAction action,DelayedSession session,ScopedCacheOperation op) {
        ScopedExprCache cache=session.cache;
        if(op.bucket==null||op.bucket.entries.isEmpty()) { op.rewound=true; return; }
        if(op.rewindStage==0) {
            op.top=op.bucket.entries.get(op.bucket.entries.size()-1);
            if(op.top.resultScope>cache.scope) { dropScopedTop(action,session,op); return; }
            op.rewindStage=1; return;
        }
        ScopedEntry top=op.top; require(top!=null&&top.result!=null&&top.result.owned,"Scoped rewind top owner missing");
        if(op.rewindStage==1) {
            if(top.validLevel>cache.scope) {
                require(top.generation!=null&&top.generation.parent!=null,"Scoped degrade chain exhausted");
                top.generation=top.generation.parent; top.validLevel--; return;
            }
            op.currentCursor=cache.current; op.walkLevel=cache.scope; op.rewindStage=2; return;
        }
        if(op.rewindStage==2) {
            if(op.walkLevel>top.validLevel) { require(op.currentCursor!=null&&op.currentCursor.parent!=null,"Scoped current chain exhausted"); op.currentCursor=op.currentCursor.parent; op.walkLevel--; return; }
            require(top.generation!=null&&op.currentCursor!=null,"Scoped generation cursor missing");
            if(top.generation.serial==op.currentCursor.serial) { op.rewound=true; return; }
            op.entryCursor=top.generation; op.walkLevel=top.validLevel; op.rewindStage=3; return;
        }
        require(op.rewindStage==3,"Invalid scoped rewind stage");
        if(op.walkLevel>top.resultScope) {
            require(op.entryCursor.parent!=null&&op.currentCursor.parent!=null,"Scoped mismatch chain exhausted");
            op.entryCursor=op.entryCursor.parent; op.currentCursor=op.currentCursor.parent; op.walkLevel--;
            if(op.entryCursor.serial==op.currentCursor.serial) { top.validLevel=op.walkLevel; top.generation=op.entryCursor; op.rewound=true; }
            return;
        }
        dropScopedTop(action,session,op);
    }
    private void stepScopedCache(RuntimeAction action,DelayedSession session) {
        delayedWork(session,1); resumeDelayedRetiring(action,session);
        ScopedCacheOperation op=session.cacheOperation; require(op!=null&&!op.completed,"No running scoped Expr operation");
        finishScopedRetiring(session,op);
        if(op.stage==0) { stepScopedRewind(action,session,op); if(op.rewound) op.stage=1; return; }
        if(op.kind==DC_LOOKUP) {
            if(op.stage==1) {
                if(op.bucket==null||op.bucket.entries.isEmpty()) { op.completed=true; return; }
                ScopedEntry top=op.bucket.entries.get(op.bucket.entries.size()-1);
                if(top.validLevel!=session.cache.scope) { op.completed=true; return; }
                session.resultScope=Math.max(session.resultScope,top.resultScope);
                op.optional=vm.exprTransforms.exprCredit(top.result.value); vm.exprTransforms.acquireExpr(op.optional); op.hit=true; op.stage=2; return;
            }
            if(op.stage==2) { op.returned=vm.exprTransforms.exprCredit(op.optional.value); vm.exprTransforms.acquireExpr(op.returned); op.stage=3; return; }
            if(op.stage==3) { op.stage=4; releaseDelayed(action,session,op.optional); return; }
            require(op.stage==4,"Invalid scoped lookup completion"); op.optional=null; op.completed=true; return;
        }
        if(op.stage==1) {
            require(op.computed!=null&&op.computed.owned,"Scoped insertion computed owner missing");
            op.shared=vm.exprTransforms.exprCredit(op.computed.value); vm.exprTransforms.acquireExpr(op.shared); op.stage=10; return;
        }
        if(op.stage==10) {
            if(!op.bucket.entries.isEmpty()&&op.bucket.entries.get(op.bucket.entries.size()-1).resultScope==op.resultScope) {
                op.replacement=vm.exprTransforms.exprCredit(op.bucket.entries.get(op.bucket.entries.size()-1).result.value); vm.exprTransforms.acquireExpr(op.replacement); op.stage=11; return;
            }
            op.stage=13;
        }
        if(op.stage==11) { op.stage=12; releaseDelayed(action,session,op.shared); return; }
        if(op.stage==12) { op.shared=op.replacement; op.replacement=null; op.stage=13; }
        if(op.stage==13) {
            if(!op.bucket.entries.isEmpty()&&op.bucket.entries.get(op.bucket.entries.size()-1).validLevel>=op.resultScope) {
                dropScopedTop(action,session,op); return;
            }
            op.stage=14; return;
        }
        if(op.stage==14) {
            require(session.cache.liveEntries<MAX_DELAYED_ENTRIES,"Scoped Expr live-entry bound");
            ScopedEntry entry=new ScopedEntry(); op.newEntry=entry; entry.result=op.shared; op.shared=null;
            entry.validLevel=session.cache.scope; entry.resultScope=op.resultScope; entry.generation=session.cache.current;
            entry.reserved=true; session.cache.liveEntries++; op.bucket.entries.add(entry); op.stage=15; return;
        }
        if(op.stage==15) { op.returned=vm.exprTransforms.exprCredit(op.newEntry.result.value); vm.exprTransforms.acquireExpr(op.returned); op.stage=16; return; }
        if(op.stage==16) { op.stage=17; releaseDelayed(action,session,op.computed); return; }
        require(op.stage==17&&op.returned!=null&&op.returned.owned,"Invalid scoped insert completion");
        op.computed=null; op.newEntry=null; op.completed=true;
    }
    private void pushResolver(DelayedSession session,ResolverTask frame) {
        require(session.phase==DELAYED_RUNNING&&session.resolver.size()<MAX_DELAYED_FRAMES,"Resolvable Expr frame bound"); session.resolver.addLast(frame);
    }
    private boolean takeResolverChild(ResolverTask parent,Class<?> expected) {
        ResolverTask child=parent.child;
        require(child!=null&&child.completed&&expected.isInstance(child),"Resolvable child kind/completion differs");
        boolean result=child.result; parent.child=null; return result;
    }
    private void callResolverHelper(RuntimeAction action,DelayedSession session,ResolverTask target,int role) {
        delayedWork(session,1); require(role>=0&&role<=3,"Resolver does not call assignment setter"); requireDelayedReceiverFree(action,session);
        Function helper=vm.exprDirect.exprInstantiationHelper(session.policy,role); DelayedHelperPacket packet=new DelayedHelperPacket();
        packet.function=helper; packet.role=role; packet.target=target; packet.arguments=new Object[helper.params.length]; packet.owned=new boolean[packet.arguments.length];
        if(role<=1) {
            require(session.context.current!=null&&session.context.current.owned,"Resolvable context owner missing");
            packet.arguments[0]=session.context.current.value;
            packet.arguments[1]=role==0?((ResolvablePendingFrame)target).name:((Node)((ResolvableAppFrame)target).head).storageField(0);
            vm.nameNode(packet.arguments[1]);
        } else {
            ExprCredit record=((ResolvableAppFrame)target).recordTemporary;
            require(record!=null&&record.owned,"Resolvable accessor record temporary missing"); packet.arguments[0]=record.value;
        }
        for(Object argument:packet.arguments) vm.validateHostObject(argument);
        session.call=packet;
        for(int i=0;i<packet.arguments.length;i++) { vm.inc(packet.arguments[i],1); packet.owned[i]=true; }
        IdentityHashMap<Node,Integer> known=new IdentityHashMap<>();
        for(Object argument:packet.arguments) if(argument instanceof Node) known.merge((Node)argument,1,Integer::sum);
        for(Map.Entry<Node,Integer> entry:known.entrySet()) require(entry.getKey().refCount()==0||entry.getKey().refCount()>=entry.getValue(),"Resolvable helper alias credits differ");
        packet.started=true; vm.enterExplicit(helper,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Resolvable helper did not publish frame/CodeRequest");
    }
    private void receiveResolverHelper(RuntimeAction action,DelayedSession session) {
        DelayedHelperPacket packet=session.call; require(packet!=null&&packet.entered,"Resolver helper returned before entry");
        require(packet.target.received==null,"Resolver helper receiver occupied"); Object value=vm.objects[action.slot];
        if(packet.role<=1) vm.exprDirect.validateDirectOption(value,packet.role==0);
        else if(packet.role==2) { Node array=vm.node(value); require(array.isArray()&&array.arraySize()<=MAX_DELAYED_NAMES,"Delayed fvars accessor requires bounded object Array"); }
        else vm.nameNode(value);
        packet.target.received=new ExprCredit(value,true); vm.objects[action.slot]=null; session.call=null;
    }
    private void stepResolvablePending(RuntimeAction action,DelayedSession session,ResolvablePendingFrame frame) {
        if(frame.stage==0) {
            frame.entry=vm.pendingEntry(session,frame.name,false);
            if(frame.entry!=null) { frame.result=frame.entry.state==PENDING_YES; frame.completed=true; return; }
            frame.entry=vm.pendingEntry(session,frame.name,true); frame.stage=1; callResolverHelper(action,session,frame,0); return;
        }
        if(frame.stage==1) {
            require(frame.received!=null&&frame.received.owned,"Resolvable pending Option missing"); frame.option=frame.received; frame.received=null;
            if(ERASED.equals(frame.option.value)) { frame.result=false; frame.stage=4; }
            else {
                frame.temporary=vm.exprTransforms.exprCredit(((Node)frame.option.value).storageField(0)); vm.exprTransforms.acquireExpr(frame.temporary);
                frame.stage=2; pushResolver(session,new ResolvableExprFrame(vm.exprNode(frame.temporary.value))); return;
            }
        }
        if(frame.stage==2) { frame.result=takeResolverChild(frame,ResolvableExprFrame.class); frame.stage=3; releaseDelayed(action,session,frame.temporary); return; }
        if(frame.stage==3) { frame.temporary=null; frame.stage=4; }
        if(frame.stage==4) { frame.entry.state=frame.result?PENDING_YES:PENDING_NO; frame.stage=5; releaseDelayed(action,session,frame.option); return; }
        require(frame.stage==5,"Invalid resolvable pending continuation"); frame.option=null; frame.completed=true;
    }
    private void stepResolvableApp(RuntimeAction action,DelayedSession session,ResolvableAppFrame frame) {
        if(frame.stage==0) {
            if(frame.head==null) frame.head=frame.original;
            Node head=vm.exprNode(frame.head);
            if(head.storageTag()==5) { frame.head=head.storageField(0); return; }
            if(head.storageTag()!=2) { frame.stage=100; pushResolver(session,new ResolvableExprFrame(vm.exprNode(frame.original.storageField(0)))); return; }
            frame.stage=1; callResolverHelper(action,session,frame,1); return;
        }
        if(frame.stage==1) {
            require(frame.received!=null&&frame.received.owned,"Resolvable delayed Option missing"); frame.option=frame.received; frame.received=null;
            if(ERASED.equals(frame.option.value)) { frame.result=false; frame.stage=200; }
            else { frame.recordTemporary=vm.exprTransforms.exprCredit(((Node)frame.option.value).storageField(0)); vm.exprTransforms.acquireExpr(frame.recordTemporary);
                frame.stage=2; callResolverHelper(action,session,frame,2); return; }
        }
        if(frame.stage==2) { require(frame.received!=null&&frame.received.owned,"Resolvable fvars Array missing"); frame.fvars=frame.received; frame.received=null;
            frame.stage=3; releaseDelayed(action,session,frame.recordTemporary); return; }
        if(frame.stage==3) { frame.recordTemporary=null; frame.cursor=frame.original; frame.argumentCount=0; frame.stage=4; }
        if(frame.stage==4) {
            Node current=vm.exprNode(frame.cursor);
            if(current.storageTag()==5) { require(frame.argumentCount<ExprDirectInstantiation.MAX_DIRECT_ARGUMENTS,"Resolvable application arity bound"); frame.argumentCount++; frame.cursor=current.storageField(0); return; }
            if(((Node)frame.fvars.value).arraySize()>frame.argumentCount) { frame.result=false; frame.stage=200; }
            else { frame.recordTemporary=vm.exprTransforms.exprCredit(((Node)frame.option.value).storageField(0)); vm.exprTransforms.acquireExpr(frame.recordTemporary);
                frame.stage=5; callResolverHelper(action,session,frame,3); return; }
        }
        if(frame.stage==5) { require(frame.received!=null&&frame.received.owned,"Resolvable pending Name missing"); frame.pendingName=frame.received; frame.received=null;
            frame.stage=6; releaseDelayed(action,session,frame.recordTemporary); return; }
        if(frame.stage==6) { frame.recordTemporary=null; frame.stage=7; pushResolver(session,new ResolvablePendingFrame(frame.pendingName.value)); return; }
        if(frame.stage==7) {
            if(!takeResolverChild(frame,ResolvablePendingFrame.class)) { frame.result=false; frame.stage=200; }
            else { frame.cursor=frame.original; frame.stage=8; }
        }
        if(frame.stage==8) {
            Node current=vm.exprNode(frame.cursor);
            if(current.storageTag()!=5) { frame.result=true; frame.stage=200; }
            else { frame.stage=9; pushResolver(session,new ResolvableExprFrame(vm.exprNode(current.storageField(1)))); return; }
        }
        if(frame.stage==9) {
            if(!takeResolverChild(frame,ResolvableExprFrame.class)) { frame.result=false; frame.stage=200; }
            else { frame.cursor=vm.exprNode(frame.cursor).storageField(0); frame.stage=8; return; }
        }
        if(frame.stage==100) {
            if(!takeResolverChild(frame,ResolvableExprFrame.class)) { frame.result=false; frame.completed=true; return; }
            frame.stage=101; pushResolver(session,new ResolvableExprFrame(vm.exprNode(frame.original.storageField(1)))); return;
        }
        if(frame.stage==101) { frame.result=takeResolverChild(frame,ResolvableExprFrame.class); frame.completed=true; return; }
        require(frame.stage==200,"Invalid resolvable App continuation");
        if(frame.cleanup<3) {
            ExprCredit credit=frame.cleanup==0?frame.pendingName:frame.cleanup==1?frame.fvars:frame.option;
            frame.cleanup++; releaseDelayed(action,session,credit); return;
        }
        frame.pendingName=null; frame.fvars=null; frame.option=null; require(frame.recordTemporary==null,"Resolvable D temporary not retired"); frame.completed=true;
    }
    private void stepResolvableExpr(RuntimeAction action,DelayedSession session,ResolvableExprFrame frame) {
        Node original=frame.original;
        if(frame.stage==0) {
            if((vm.exprCachedData(original)&(1L<<41))==0) { frame.result=true; frame.completed=true; return; }
            frame.entryShared=!exclusive(original);
            Boolean cached=frame.entryShared?session.resolvableExpressions.get(original):null;
            if(cached!=null) { frame.result=cached; frame.completed=true; return; }
            if(original.storageTag()==2) { frame.result=false; frame.stage=90; }
            else if(original.storageTag()==5) { frame.stage=10; pushResolver(session,new ResolvableAppFrame(original)); return; }
            else if(original.storageTag()==6||original.storageTag()==7||original.storageTag()==8||original.storageTag()==10||original.storageTag()==11) frame.stage=1;
            else { frame.result=true; frame.stage=90; }
        }
        if(frame.stage==1) {
            if(frame.child!=null) { if(!takeResolverChild(frame,ResolvableExprFrame.class)) { frame.result=false; frame.stage=90; } else frame.cursor++; }
            if(frame.stage==1) {
                if(frame.cursor<ExprTransforms.exprChildCount(original.storageTag())) { pushResolver(session,new ResolvableExprFrame(vm.exprNode(original.storageField(ExprTransforms.exprChildField(original.storageTag(),frame.cursor))))); return; }
                frame.result=true; frame.stage=90;
            }
        }
        if(frame.stage==10) { frame.result=takeResolverChild(frame,ResolvableAppFrame.class); frame.stage=90; }
        require(frame.stage==90,"Invalid resolvable Expr continuation");
        // Native samples sharing again after analysis, not only at entry.
        if(!exclusive(original)) {
            require(session.resolvableExpressions.containsKey(original)||session.resolvableExpressions.size()<MAX_DELAYED_KEYS,"Resolvable Expr key bound");
            session.resolvableExpressions.put(original,frame.result);
        }
        frame.completed=true;
    }
    private void startResolver(DelayedSession session,Object input) {
        require(session.phase==DELAYED_IDLE&&session.resolver.isEmpty()&&session.call==null&&session.constructorCall==null,"Resolvable session is not idle");
        Node root=vm.exprNode(input); session.phase=DELAYED_RUNNING; pushResolver(session,new ResolvableExprFrame(root));
    }
    private void stepResolver(RuntimeAction action,DelayedSession session) {
        delayedWork(session,1); resumeDelayedRetiring(action,session);
        require(session.phase==DELAYED_RUNNING&&session.constructorCall==null,"No running resolver or unsupported delayed constructor packet");
        if(session.call!=null) { receiveResolverHelper(action,session); return; }
        ResolverTask frame=session.resolver.peekLast(); require(frame!=null,"Missing resolvability frame");
        if(!frame.completed) {
            if(frame instanceof ResolvableExprFrame) stepResolvableExpr(action,session,(ResolvableExprFrame)frame);
            else if(frame instanceof ResolvablePendingFrame) stepResolvablePending(action,session,(ResolvablePendingFrame)frame);
            else stepResolvableApp(action,session,(ResolvableAppFrame)frame);
            return;
        }
        Iterator<ResolverTask> ancestors=session.resolver.descendingIterator(); ancestors.next(); ResolverTask parent=ancestors.hasNext()?ancestors.next():null;
        if(parent==null) { session.booleanResult=frame.result; session.phase=DELAYED_RESULT; }
        else { require(parent.child==null,"Resolver parent receiver occupied"); parent.child=frame; }
        session.resolver.removeLast();
    }
    private boolean takeResolverResult(DelayedSession session) {
        require(session.phase==DELAYED_RESULT&&session.resolver.isEmpty()&&session.call==null&&session.retiring==null,"Resolver result not ready");
        boolean result=session.booleanResult; session.phase=DELAYED_IDLE; return result;
    }
    private SubstitutionEntry substitutionEntry(DelayedSession session,Object name) {
        int hash=delayedNameHash(session,name); ArrayList<SubstitutionEntry> bucket=session.substitutions.get(hash);
        if(bucket!=null) for(SubstitutionEntry entry:bucket) {
            delayedWork(session,1); require(entry.live&&entry.name!=null&&entry.name.owned,"Substitution key owner missing");
            if(mvarNameEqual(session.budget,name,entry.name.value)) return entry;
        }
        return null;
    }
    private void publishSubstitution(DelayedSession session,SubstitutionEntry entry) {
        require(!entry.live&&entry.name!=null&&entry.name.owned&&entry.value!=null&&entry.value.owned,"Incomplete new substitution entry");
        require(session.substitutionOwners.size()<MAX_DELAYED_NAMES,"Substitution entry allocation bound");
        session.substitutionOwners.add(entry); ArrayList<SubstitutionEntry> bucket=session.substitutions.get(entry.hash);
        if(bucket==null) { bucket=new ArrayList<>(); session.substitutions.put(entry.hash,bucket); }
        bucket.add(entry); entry.live=true;
    }
    private void detachSubstitution(DelayedSession session,SubstitutionEntry entry) {
        ArrayList<SubstitutionEntry> bucket=session.substitutions.get(entry.hash);
        require(entry.live&&bucket!=null,"Missing substitution erase entry"); delayedWork(session,bucket.size());
        require(bucket.remove(entry),"Substitution erase index differs"); if(bucket.isEmpty()) session.substitutions.remove(entry.hash); entry.live=false;
    }
    private static final int SF_PREPARE=0,SF_ENTER=1,SF_SAVE=2,SF_RELEASE_OLD=3,SF_COMMIT=4,SF_INSTALLED=5;
    private static final int SF_RESTORE_NEXT=21,SF_RESTORE_VALUE=22,SF_RESTORE_KEY=23,SF_RESTORE_COMMIT=24,SF_RESTORED=25,SF_DRAIN_SAVED=30,SF_DRAIN_ARGS=31,SF_DRAINED=32;
    private void prepareSubstitutionValue(DelayedSession session,SubstitutionFrame frame,Object name,Object value) {
        require(frame.newName==null&&frame.newValue==null&&frame.replacement==null,"Substitution replacement escrow occupied");
        frame.newValue=vm.exprTransforms.exprCredit(value); vm.exprTransforms.acquireExpr(frame.newValue);
        if(frame.existing==null) {
            require(session.substitutionOwners.size()<MAX_DELAYED_NAMES,"Substitution entry allocation bound");
            frame.replacement=new SubstitutionEntry(); frame.replacement.hash=delayedNameHash(session,name);
            frame.newName=vm.exprTransforms.exprCredit(name); vm.exprTransforms.acquireExpr(frame.newName);
        }
    }
    private void commitSubstitutionValue(DelayedSession session,SubstitutionFrame frame,int depth,int scope) {
        require(frame.newValue!=null&&frame.newValue.owned,"Substitution replacement value missing");
        SubstitutionEntry entry=frame.existing==null?frame.replacement:frame.existing;
        require(entry!=null&&entry.value==null,"Substitution old value not retired");
        if(frame.existing==null) { entry.name=frame.newName; frame.newName=null; }
        entry.value=frame.newValue; frame.newValue=null; entry.depth=depth; entry.scope=scope;
        if(frame.existing==null) publishSubstitution(session,entry);
        frame.existing=null; frame.replacement=null; frame.retiringValue=null; frame.retiringName=null;
    }
    private void stepSubstitutionInstall(RuntimeAction action,DelayedSession session,SubstitutionFrame frame) {
        delayedWork(session,1); resumeDelayedRetiring(action,session);
        require(!frame.restored&&!frame.completed,"No running substitution install");
        if(frame.stage==SF_PREPARE) {
            require(frame.ownsArguments&&frame.sourceArguments instanceof Node,"Missing research argument source");
            Node arguments=(Node)frame.sourceArguments;
            if(frame.index<arguments.arraySize()) {
                ExprCredit argument=vm.exprTransforms.exprCredit(arguments.storageField(frame.index)); frame.arguments.add(argument); frame.index++; vm.exprTransforms.acquireExpr(argument); return;
            }
            frame.index=0; frame.stage=SF_ENTER;
        }
        if(frame.stage==SF_ENTER) { scopedPush(session); frame.scopePushed=true; frame.stage=SF_SAVE; return; }
        Node fvars=vm.node(frame.fvars); int count=fvars.arraySize();
        if(frame.stage==SF_SAVE) {
            if(frame.index==count) { frame.stage=SF_INSTALLED; frame.completed=true; return; }
            require(frame.saved.size()<MAX_DELAYED_NAMES&&frame.arguments.size()>=count,"Delayed saved-substitution bound/arity");
            Node fvar=vm.exprNode(fvars.storageField(frame.index)); require(fvar.storageTag()==1,"Delayed substitution requires FVar elements"); Object name=fvar.storageField(0); vm.nameNode(name);
            frame.existing=substitutionEntry(session,name);
            SavedSubstitution saved=new SavedSubstitution(); saved.name=vm.exprTransforms.exprCredit(name); frame.saved.add(saved); vm.exprTransforms.acquireExpr(saved.name);
            saved.hadOld=frame.existing!=null;
            if(saved.hadOld) {
                require(frame.existing.value!=null&&frame.existing.value.owned,"Old substitution value missing");
                saved.oldDepth=frame.existing.depth; saved.oldScope=frame.existing.scope;
                saved.oldValue=vm.exprTransforms.exprCredit(frame.existing.value.value); vm.exprTransforms.acquireExpr(saved.oldValue);
            }
            ExprCredit argument=frame.arguments.get(frame.arguments.size()-1-frame.index); require(argument.owned,"Substitution argument backing owner missing");
            prepareSubstitutionValue(session,frame,name,argument.value); frame.stage=SF_RELEASE_OLD; return;
        }
        if(frame.stage==SF_RELEASE_OLD) {
            frame.stage=SF_COMMIT;
            if(frame.existing!=null) { frame.retiringValue=frame.existing.value; frame.existing.value=null; releaseDelayed(action,session,frame.retiringValue); }
            return;
        }
        require(frame.stage==SF_COMMIT,"Invalid substitution install continuation");
        commitSubstitutionValue(session,frame,frame.depth,session.cache.scope); frame.index++; frame.stage=SF_SAVE;
    }
    private void beginSubstitutionRestore(DelayedSession session,SubstitutionFrame frame) {
        require(frame.completed&&frame.stage==SF_INSTALLED&&frame.scopePushed&&!frame.restored,"Substitution scope is not installed");
        scopedPop(session); session.resultScope=Math.min(session.resultScope,session.cache.scope);
        frame.scopePushed=false; frame.completed=false; frame.index=0; frame.stage=SF_RESTORE_NEXT;
    }
    private void stepSubstitutionRestore(RuntimeAction action,DelayedSession session,SubstitutionFrame frame) {
        delayedWork(session,1); resumeDelayedRetiring(action,session);
        require(!frame.completed&&!frame.restored,"No running substitution restoration");
        if(frame.stage==SF_RESTORE_NEXT) {
            if(frame.index==frame.saved.size()) { frame.restored=true; frame.completed=true; frame.stage=SF_RESTORED; return; }
            SavedSubstitution saved=frame.saved.get(frame.index); require(saved.name!=null&&saved.name.owned,"Saved substitution Name owner missing");
            frame.existing=substitutionEntry(session,saved.name.value); frame.erasing=!saved.hadOld;
            if(frame.erasing) {
                if(frame.existing==null) { frame.index++; return; }
                detachSubstitution(session,frame.existing);
                frame.retiringValue=frame.existing.value; frame.existing.value=null;
                frame.retiringName=frame.existing.name; frame.existing.name=null;
            } else {
                require(saved.oldValue!=null&&saved.oldValue.owned,"Saved old substitution value missing");
                prepareSubstitutionValue(session,frame,saved.name.value,saved.oldValue.value);
                if(frame.existing!=null) { frame.retiringValue=frame.existing.value; frame.existing.value=null; }
            }
            frame.stage=SF_RESTORE_VALUE; return;
        }
        if(frame.stage==SF_RESTORE_VALUE) { frame.stage=SF_RESTORE_KEY; releaseDelayed(action,session,frame.retiringValue); return; }
        if(frame.stage==SF_RESTORE_KEY) { frame.stage=SF_RESTORE_COMMIT; releaseDelayed(action,session,frame.retiringName); return; }
        require(frame.stage==SF_RESTORE_COMMIT,"Invalid substitution restoration continuation");
        if(!frame.erasing) {
            SavedSubstitution saved=frame.saved.get(frame.index); commitSubstitutionValue(session,frame,saved.oldDepth,saved.oldScope);
        } else { frame.existing=null; frame.retiringValue=null; frame.retiringName=null; }
        frame.index++; frame.stage=SF_RESTORE_NEXT;
    }
    private void stepSubstitutionFrameDrain(RuntimeAction action,DelayedSession session,SubstitutionFrame frame) {
        delayedWork(session,1); resumeDelayedRetiring(action,session);
        require(frame.restored&&!frame.scopePushed,"Cannot drain an active substitution scope");
        if(frame.stage==SF_RESTORED) { frame.completed=false; frame.cleanup=0; frame.stage=SF_DRAIN_SAVED; }
        if(frame.stage==SF_DRAIN_SAVED) {
            if(frame.cleanup<frame.saved.size()*2) {
                SavedSubstitution saved=frame.saved.get(frame.cleanup/2); ExprCredit credit=(frame.cleanup++&1)==0?saved.oldValue:saved.name;
                releaseDelayed(action,session,credit); return;
            }
            frame.saved.clear(); frame.cleanup=0; frame.stage=SF_DRAIN_ARGS;
        }
        if(frame.stage==SF_DRAIN_ARGS) {
            if(frame.ownsArguments&&frame.cleanup<frame.arguments.size()) { ExprCredit credit=frame.arguments.get(frame.cleanup++); releaseDelayed(action,session,credit); return; }
            frame.arguments.clear(); frame.fvars=null; frame.sourceArguments=null; frame.stage=SF_DRAINED; frame.completed=true;
        }
        require(frame.stage==SF_DRAINED,"Invalid substitution frame drain");
    }
    private void stepSubstitutionLookup(RuntimeAction action,DelayedSession session,SubstitutionLookup frame) {
        delayedWork(session,1); resumeDelayedRetiring(action,session);
        if(frame.stage==0) {
            frame.entry=substitutionEntry(session,frame.name);
            if(frame.entry==null) { frame.completed=true; return; }
            require(frame.entry.value!=null&&frame.entry.value.owned&&frame.depth>=frame.entry.depth,"Delayed substitution lookup depth/owner invalid");
            int delta=frame.depth-frame.entry.depth; require(delta<=ExprTransforms.MAX_EXPR_JOB_OFFSET,"Delayed substitution lift bound");
            session.resultScope=Math.max(session.resultScope,frame.entry.scope); frame.present=true;
            if(delta==0) { frame.optional=vm.exprTransforms.exprCredit(frame.entry.value.value); vm.exprTransforms.acquireExpr(frame.optional); frame.stage=2; return; }
            require(vm.runtimeAction==action&&vm.objects[action.slot]==null&&session.call==null&&session.constructorCall==null,"Substitution lift receiver occupied");
            for(int role=0;role<9;role++) vm.exprTransforms.exprConstructor(session.policy.constructors,role);
            RuntimeAction child=vm.newAction(ACTION_EXPR_MACHINERY,null,ACTION_BODY,action.slot,ASSIGN,null);
            ExprMachineryState worker=new ExprMachineryState(); worker.policy=session.policy.constructors; worker.budget=session.budget;
            vm.exprTransforms.pushReplaceJob(worker,ExprTransforms.EXPR_LIFT_JOB,frame.entry.value.value,0,delta,new Object[0]);
            child.exprMachinery=worker; vm.objects[child.slot]=null; frame.stage=1; vm.publishAction(child); return;
        }
        if(frame.stage==1) { Object value=vm.objects[action.slot]; vm.exprNode(value); frame.optional=new ExprCredit(value,true); vm.objects[action.slot]=null; frame.stage=2; }
        if(frame.stage==2) { frame.returned=vm.exprTransforms.exprCredit(frame.optional.value); vm.exprTransforms.acquireExpr(frame.returned); frame.stage=3; return; }
        if(frame.stage==3) { frame.stage=4; releaseDelayed(action,session,frame.optional); return; }
        require(frame.stage==4,"Invalid substitution lookup completion"); frame.optional=null; frame.completed=true;
    }
    void sealDelayedSession(DelayedSession session) {
        require(session.phase==DELAYED_IDLE&&session.resolver.isEmpty()&&session.call==null&&session.constructorCall==null
                &&session.cacheOperation==null&&session.substitution==null&&session.lookup==null&&session.substitutionFrames.isEmpty()
                &&session.retiring==null&&session.result==null&&session.cache.scope==0,"Delayed session is not idle for seal");
        session.resolvableExpressions.clear(); session.pending.clear(); session.normalized.clear(); session.substitutions.clear(); session.cache.index.clear();
        for(ScopedBucket bucket:session.cache.buckets) bucket.key=null;
        session.cache.sealed=true; session.phase=DELAYED_SEALED;
    }
    void stepDelayedDrain(RuntimeAction action,DelayedSession session) {
        delayedWork(session,1); resumeDelayedRetiring(action,session); require(session.phase==DELAYED_SEALED,"Delayed member drain requires sealed session");
        if(session.drainStage==0) {
            if(session.drainCursor<session.pendingOwners.size()) { ExprCredit name=session.pendingOwners.get(session.drainCursor++).name; releaseDelayed(action,session,name); return; }
            session.pendingOwners.clear(); session.drainCursor=0; session.drainStage=1; return;
        }
        if(session.drainStage==1) {
            if(session.drainCursor<session.saved.size()) { ExprCredit credit=session.saved.get(session.saved.size()-1-session.drainCursor++); releaseDelayed(action,session,credit); return; }
            session.saved.clear(); session.drainCursor=0; session.drainStage=2; return;
        }
        if(session.drainStage==2) {
            if(session.drainCursor<session.nameOwners.size()) { ExprCredit credit=session.nameOwners.get(session.nameOwners.size()-1-session.drainCursor++).name; releaseDelayed(action,session,credit); return; }
            session.nameOwners.clear(); session.normalized.clear(); session.drainCursor=0; session.drainStage=3; return;
        }
        if(session.drainStage==3) {
            ScopedExprCache cache=session.cache;
            if(cache.retiringEntry!=null) {
                ScopedEntry entry=cache.retiringEntry; require(entry.result!=null&&!entry.result.owned,"Scoped member owner not drained");
                if(entry.reserved) { require(cache.liveEntries>0,"Scoped drain reservation underflow"); cache.liveEntries--; entry.reserved=false; }
                entry.result=null; cache.retiringEntry=null;
            }
            if(cache.drainBucket<cache.buckets.size()) {
                ScopedBucket bucket=cache.buckets.get(cache.drainBucket);
                if(bucket.entries.isEmpty()) { cache.drainBucket++; return; }
                cache.retiringEntry=bucket.entries.remove(bucket.entries.size()-1); releaseDelayed(action,session,cache.retiringEntry.result); return;
            }
            require(cache.liveEntries==0,"Scoped member drain leaked reservations"); cache.buckets.clear(); cache.current=null;
            session.drainStage=4; session.drainCursor=0; return;
        }
        if(session.drainStage==4) {
            if(session.drainCursor<session.substitutionOwners.size()*2) {
                SubstitutionEntry entry=session.substitutionOwners.get(session.drainCursor/2);
                ExprCredit credit=(session.drainCursor++&1)==0?entry.value:entry.name; releaseDelayed(action,session,credit); return;
            }
            session.substitutionOwners.clear(); session.phase=DELAYED_DRAINED; return;
        }
        throw error("Invalid delayed member drain stage");
    }
}
