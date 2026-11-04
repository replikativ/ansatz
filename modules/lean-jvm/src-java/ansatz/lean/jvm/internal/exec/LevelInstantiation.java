package ansatz.lean.jvm.internal.exec;

import java.util.*;
import ansatz.lean.jvm.internal.exec.Interpreter.*;
import ansatz.lean.jvm.internal.exec.ExprTransforms.*;
import static ansatz.lean.jvm.internal.exec.Interpreter.*;

/** Universe Level instantiation: level sessions, credits and frames, smart
 * max/imax normalisation and the resumable helper-call protocol. */
final class LevelInstantiation {
    private final Interpreter vm;

    LevelInstantiation(Interpreter vm) {
        this.vm=vm;
    }

    private static final boolean LEVEL_INSTANTIATION_READY=true;
    Function levelInstantiationHelper(LevelInstantiationPolicy policy,int role) {
        Header header=policy.helpers[role]; int id=vm.program.functionId(header); Function function=vm.program.functions[id];
        require(function.header==header&&function.intrinsic==0&&function.hostExtern==null&&vm.program.guestExports[id]==null,
                "Level instantiation helper is not the exact ordinary function");
        requireExecutableAbi(function);
        require(function.resultType==OBJ,"Level instantiation helper requires OBJ result");
        for(int lane:function.paramTypes) require(lane==OBJ,"Level instantiation helper requires OBJ parameters");
        return vm.preflightCallable(function,true);
    }
    void levelInstantiationProfile(Function function) {
        require(LEVEL_INSTANTIATION_READY,"Level instantiation traversal is not yet enabled");
        require(vm.explicit&&vm.taskRuntime!=null&&vm.levelInstantiationPolicy!=null,"Level instantiation requires active explicit runtime and configured original helpers");
        Header origin=function.header;
        require(origin!=null&&origin.source==vm.levelInstantiationPolicy.helpers[0].source
                &&origin.kind.equals("extern")&&origin.originalSha256.equals("43de9c312f7e7a4bdeb9cd3b070ca4bd245fcca722f532b05f9e3083c1847605"),
                "Level instantiation native source Header differs");
        Object name=Arrays.asList("str",Arrays.asList("str",Arrays.asList("anonymous"),"Lean"),"instantiateLevelMVarsImp");
        require(origin.exactName.equals(frozenName(name)),"Level instantiation native typed Name differs");
        for(int role=0;role<5;role++) levelInstantiationHelper(vm.levelInstantiationPolicy,role);
    }
    private static final int MAX_LEVEL_INSTANTIATION_FRAMES=100_000,
            MAX_LEVEL_INSTANTIATION_CACHE=100_000,MAX_LEVEL_INSTANTIATION_SAVED=100_000;
    /** Exactly one control-owned occurrence when owned=true; other references
     * to this credit object are aliases. Never stored in guest Node metadata. */
    static final class LevelCredit {
        Object value; boolean owned;
        LevelCredit(Object value,boolean owned) { this.value=value; this.owned=owned; }
    }
    static final class LevelFrame {
        Object original,name;
        int tag,stage,cleanup;
        boolean shared,active,cached;
        LevelCredit left,right,option,assignment,result;
        LevelFrame(Object original) { this.original=original; }
    }
    static final class LevelPacket {
        Function function; int role;
        Object[] arguments; boolean[] owned;
        boolean entryStarted,entered;
        LevelFrame frame;
    }
    static final int LS_IDLE=0,LS_RUNNING=1,LS_RESULT=2,LS_SEALED=3,LS_DRAINING=4,LS_DRAINED=5;
    /** Borrowed input/key lifetimes extend through seal; only values/saved
     * assignments own. The context cell is shared, never a second owner. */
    static final class LevelSession {
        MVarContextCell context;
        InstantiationBudget budget;
        LevelInstantiationPolicy policy;
        final ArrayDeque<LevelFrame> frames=new ArrayDeque<>();
        final IdentityHashMap<Node,LevelCredit> cache=new IdentityHashMap<>();
        // cacheValues indexes the SAME owned credit objects as cache.
        final ArrayList<LevelCredit> cacheValues=new ArrayList<>(),saved=new ArrayList<>();
        final IdentityHashMap<Node,Boolean> active=new IdentityHashMap<>();
        LevelPacket call;
        LevelCredit result,retiring;
        int phase,drainStage,drainCursor;
    }
    static final class LevelInstantiationState {
        LevelSession session;
        LevelCredit input,result,pair;
        int stage,pairFields;
    }
    void levelHelperEntry(Function function,Object[] arguments) {
        RuntimeAction action=vm.runtimeAction;
        LevelSession session=currentLevelSession(action);
        if(session==null) return;
        LevelPacket packet=session.call;
        if(packet==null||packet.entered||packet.function!=function||packet.arguments!=arguments) return;
        require(packet.entryStarted,"Level helper entered before packet publication");
        packet.entered=true; Arrays.fill(packet.owned,false);
    }
    private static final int LF_ENTER=0,LF_LEFT=1,LF_RIGHT=2,LF_GET=3,LF_ASSIGN=4,LF_ASSIGNED=5,LF_SET=6,LF_BUILD=7,LF_FINISH=8,LF_CLEAN=9;
    void levelWork(LevelSession state,long amount) {
        vm.exprTransforms.instantiationWork(state.budget,amount,"Level instantiation work outside bounded runtime profile","Level instantiation interrupted");
    }
    static boolean sameLevel(Object a,Object b) {
        return a==b||a instanceof Long&&b instanceof Long&&((Long)a)==0&&((Long)b)==0;
    }
    private long levelWord(Object value) { Node node=vm.levelNode(value); return node==null?2221:readScalar(node,0,U64); }
    private boolean levelHasMVar(Object value) { return (levelWord(value)&(1L<<32))!=0; }
    private boolean instantiatedLevelEqual(LevelSession state,Object left,Object right) {
        ExprEquality comparison=vm.new ExprEquality(false); comparison.work=state.budget.work;
        try { return comparison.applyLevel(left,right); }
        finally { state.budget.work=comparison.work; }
    }
    private static final class LevelOffset {
        final Object base; final int offset;
        LevelOffset(Object base,int offset) { this.base=base; this.offset=offset; }
    }
    private LevelOffset levelOffset(LevelSession state,Object value) {
        IdentityHashMap<Node,Boolean> seen=new IdentityHashMap<>(); int offset=0;
        while(true) {
            levelWork(state,1); Node node=vm.levelNode(value);
            if(node==null||node.storageTag()!=1) return new LevelOffset(value,offset);
            require(seen.size()<MAX_LEVEL_INSTANTIATION_FRAMES&&!seen.containsKey(node),"Level instantiation offset cycle/depth outside profile");
            seen.put(node,Boolean.TRUE); value=node.storageField(0); offset++;
        }
    }
    private boolean levelNotZero(LevelSession state,Object value) {
        ArrayDeque<Object[]> todo=new ArrayDeque<>(); IdentityHashMap<Node,Boolean> seen=new IdentityHashMap<>();
        todo.push(new Object[]{value,Boolean.FALSE});
        while(!todo.isEmpty()) {
            levelWork(state,1); Object[] item=todo.pop(); Node node=vm.levelNode(item[0]);
            if(node==null) continue;
            if(item[1]==Boolean.TRUE) { seen.put(node,Boolean.TRUE); continue; }
            if(node.storageTag()==1) return true;
            if(node.storageTag()==4||node.storageTag()==5) continue;
            Boolean prior=seen.get(node);
            require(prior!=Boolean.FALSE,"Level instantiation nonzero cycle outside profile");
            if(prior==Boolean.TRUE) continue;
            require(seen.size()<MAX_LEVEL_INSTANTIATION_FRAMES&&todo.size()<MAX_LEVEL_INSTANTIATION_FRAMES-3,
                    "Level instantiation nonzero stack outside profile");
            seen.put(node,Boolean.FALSE); todo.push(new Object[]{node,Boolean.TRUE});
            if(node.storageTag()==2) todo.push(new Object[]{node.storageField(1),Boolean.FALSE});
            todo.push(new Object[]{node.storageField(node.storageTag()==3?1:0),Boolean.FALSE});
        }
        return false;
    }
    private boolean levelOne(LevelSession state,Object value) {
        levelWork(state,1); Node node=vm.levelNode(value);
        return node!=null&&node.storageTag()==1&&sameLevel(node.storageField(0),ERASED)
                &&(int)readScalar(node,0,U64)==(int)mixHash(2243,2221)&&(readScalar(node,0,U64)>>>40)==1;
    }
    /** Null means call the raw constructor. Every nonnull selection is borrowed. */
    private Object smartLevelMax(LevelSession state,Object left,Object right) {
        LevelOffset x=levelOffset(state,left),y=null;
        if(sameLevel(x.base,ERASED)) {
            y=levelOffset(state,right);
            if(sameLevel(y.base,ERASED)) return (levelWord(left)>>>40)>=(levelWord(right)>>>40)?left:right;
        }
        if(instantiatedLevelEqual(state,left,right)) return left;
        if(sameLevel(left,ERASED)) return right;
        if(sameLevel(right,ERASED)) return left;
        Node a=vm.levelNode(left),b=vm.levelNode(right);
        if(b.storageTag()==2&&(instantiatedLevelEqual(state,b.storageField(0),left)||instantiatedLevelEqual(state,b.storageField(1),left))) return right;
        if(a.storageTag()==2&&(instantiatedLevelEqual(state,a.storageField(0),right)||instantiatedLevelEqual(state,a.storageField(1),right))) return left;
        if(y==null) y=levelOffset(state,right);
        if(instantiatedLevelEqual(state,x.base,y.base)) {
            require(x.offset!=y.offset,"Level instantiation inconsistent equal offsets outside profile");
            return x.offset>y.offset?left:right;
        }
        return null;
    }
    private Object smartLevelIMax(LevelSession state,Object left,Object right,boolean nonzero) {
        if(nonzero) return smartLevelMax(state,left,right);
        if(sameLevel(right,ERASED)||sameLevel(left,ERASED)||levelOne(state,left)) return right;
        if(instantiatedLevelEqual(state,left,right)) return left;
        return null;
    }
    private LevelCredit retainedLevel(LevelSession state,Object value) {
        levelWork(state,1); LevelCredit credit=new LevelCredit(value,false);
        // Caller must publish the credit BEFORE invoking inc; this routine is
        // used only where the resulting credit is immediately stored below.
        return credit;
    }
    void ownLevelCredit(LevelCredit credit) { vm.inc(credit.value,1); credit.owned=true; }
    private void pushLevelFrame(LevelSession state,Object original) {
        require(state.frames.size()<MAX_LEVEL_INSTANTIATION_FRAMES,"Level instantiation frame limit");
        state.frames.addLast(new LevelFrame(original));
    }
    void validateLevelArguments(Function function,Object[] args) {
        levelInstantiationProfile(function);
        require(args!=null&&args.length==2,"Level instantiation native arity mismatch");
        vm.validateHostObject(args[0]); vm.levelNode(args[1]);
        if(args[0]==args[1]&&args[0] instanceof Node) {
            Node node=(Node)args[0]; require(node.refCount()==0||node.refCount()>=2,"Insufficient aliased Level instantiation input credits");
        }
    }
    private void checkLevelPacket(LevelPacket packet) {
        IdentityHashMap<Node,Integer> credits=new IdentityHashMap<>();
        for(int i=0;i<packet.arguments.length;i++) {
            require(packet.owned[i],"Level helper packet argument is not owned"); vm.validateHostObject(packet.arguments[i]);
            if(packet.arguments[i] instanceof Node) credits.merge((Node)packet.arguments[i],1,Integer::sum);
        }
        for(Map.Entry<Node,Integer> item:credits.entrySet())
            require(item.getKey().refCount()==0||item.getKey().refCount()>=item.getValue(),"Insufficient Level helper packet alias credits");
    }
    private void callLevelHelper(RuntimeAction action,LevelSession state,LevelFrame frame,int role) {
        levelWork(state,1); require(state.call==null&&vm.objects[action.slot]==null,"Level helper receiver already occupied");
        Function helper=levelInstantiationHelper(state.policy,role);
        int arity=role==0||role>=3?2:role==1?3:1;
        LevelPacket packet=new LevelPacket(); packet.function=helper; packet.role=role; packet.frame=frame;
        packet.arguments=new Object[arity]; packet.owned=new boolean[arity]; state.call=packet;
        if(role==0||role==1) {
            require(state.context.current!=null&&state.context.current.owned,"Level helper lacks current context owner");
            packet.arguments[0]=state.context.current.value;
            if(role==1) { packet.owned[0]=true; state.context.current.owned=false; state.context.current=null; }
            else { vm.inc(packet.arguments[0],1); packet.owned[0]=true; }
            vm.nameNode(frame.name); packet.arguments[1]=frame.name; vm.inc(frame.name,1); packet.owned[1]=true;
            if(role==1) { packet.arguments[2]=frame.result.value; vm.inc(packet.arguments[2],1); packet.owned[2]=true; }
        } else {
            packet.arguments[0]=frame.left.value; vm.inc(packet.arguments[0],1); packet.owned[0]=true;
            if(arity==2) { packet.arguments[1]=frame.right.value; vm.inc(packet.arguments[1],1); packet.owned[1]=true; }
        }
        checkLevelPacket(packet); packet.entryStarted=true;
        vm.enterExplicit(helper,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Level helper did not publish a frame or CodeRequest");
    }
    private void receiveLevelHelper(RuntimeAction action,LevelSession state) {
        LevelPacket packet=state.call; require(packet.entered,"Level helper has not committed entry");
        Object value=vm.objects[action.slot]; LevelFrame frame=packet.frame;
        // The existing receiver slot owns VALUE already, even before any local
        // flag is set. Invalid results remain there on terminal failure.
        if(packet.role==0) {
            if(!sameLevel(value,ERASED)) {
                Node option=vm.constructorNode(value);
                require(option.closureFunction()==null&&option.storageTag()==1&&option.fieldCount()==1&&option.scalarCount()==0,"Level getter returned malformed Option");
                vm.levelNode(option.storageField(0));
            }
            frame.option=new LevelCredit(value,true); vm.objects[action.slot]=null; state.call=null;
            if(sameLevel(value,ERASED)) {
                frame.result=retainedLevel(state,frame.original); ownLevelCredit(frame.result); frame.stage=LF_FINISH;
            } else {
                Object assigned=((Node)value).storageField(0);
                frame.assignment=retainedLevel(state,assigned); ownLevelCredit(frame.assignment);
                if(!levelHasMVar(assigned)) { frame.result=frame.assignment; frame.assignment=null; frame.stage=LF_FINISH; }
                else { frame.stage=LF_ASSIGN; pushLevelFrame(state,assigned); }
            }
        } else if(packet.role==1) {
            vm.validateHostObject(value); require(state.context.current==null,"Level setter would replace a live context owner");
            state.context.current=new LevelCredit(value,true); vm.objects[action.slot]=null; state.call=null; frame.stage=LF_FINISH;
        } else {
            Node level=vm.levelNode(value); int tag=packet.role==2?1:packet.role==3?2:3;
            require(level!=null&&level.storageTag()==tag&&sameLevel(level.storageField(0),packet.arguments[0])
                    &&(tag==1||sameLevel(level.storageField(1),packet.arguments[1])),"Original Level constructor returned unexpected head/children");
            frame.result=new LevelCredit(value,true); vm.objects[action.slot]=null; state.call=null; frame.stage=LF_FINISH;
        }
    }
    boolean releaseLevelCredit(RuntimeAction action,LevelSession state,LevelCredit credit) {
        if(credit==null||!credit.owned) return false;
        state.retiring=credit; action.retiring=credit.value; action.releaseClaimed=false;
        boolean dispatch;
        try { dispatch=vm.beginRelease(credit.value,1,ACTION_BODY); credit.owned=false; }
        finally { if(action.releaseClaimed) credit.owned=false; }
        if(!dispatch) { state.retiring=null; action.retiring=null; action.releaseClaimed=false; }
        return dispatch;
    }
    private void completeLevelFrame(LevelSession state,LevelFrame frame) {
        require(frame.result!=null&&frame.result.owned,"Level frame has no owned result");
        if(frame.active) state.active.remove((Node)frame.original);
        require(state.frames.removeLast()==frame,"Level frame stack differs");
        LevelCredit result=frame.result; frame.result=null;
        frame.original=null; frame.name=null; frame.left=null; frame.right=null; frame.assignment=null; frame.option=null;
        if(state.frames.isEmpty()) { state.result=result; state.phase=LS_RESULT; return; }
        LevelFrame parent=state.frames.peekLast();
        if(parent.stage==LF_LEFT) parent.left=result;
        else if(parent.stage==LF_RIGHT) parent.right=result;
        else if(parent.stage==LF_ASSIGN) { parent.result=result; parent.stage=LF_ASSIGNED; }
        else throw error("Level instantiation child continuation differs");
    }
    void stepLevelJob(RuntimeAction action,LevelSession state) {
        require(state.phase==LS_RUNNING,"Level session has no running job"); levelWork(state,1);
        if(state.retiring!=null) {
            require(!state.retiring.owned,"Level cleanup returned without claiming retiring owner");
            state.retiring=null; action.retiring=null; action.releaseClaimed=false;
        }
        if(state.call!=null) { receiveLevelHelper(action,state); return; }
        {
            LevelFrame frame=state.frames.peekLast(); require(frame!=null,"Missing Level traversal frame");
            if(frame.stage==LF_ENTER) {
                Node node=vm.levelNode(frame.original); frame.tag=node==null?0:node.storageTag();
                if(!levelHasMVar(frame.original)) {
                    frame.result=retainedLevel(state,frame.original); ownLevelCredit(frame.result); frame.stage=LF_FINISH; return;
                }
                require(node!=null&&node.storageTag()!=4,"Inconsistent Level hasMVar cache on Zero/Param");
                frame.shared=!exclusive(node);
                LevelCredit cached=frame.shared?state.cache.get(node):null;
                if(cached!=null) {
                    require(cached.owned,"Level cache value owner is missing");
                    frame.result=retainedLevel(state,cached.value); ownLevelCredit(frame.result); frame.cached=true; frame.stage=LF_FINISH; return;
                }
                require(!state.active.containsKey(node),"Level instantiation assignment/structural cycle outside profile");
                state.active.put(node,Boolean.TRUE); frame.active=true;
                if(node.storageTag()==5) { frame.name=node.storageField(0); frame.stage=LF_GET; callLevelHelper(action,state,frame,0); }
                else { frame.stage=LF_LEFT; pushLevelFrame(state,node.storageField(0)); }
                return;
            }
            if(frame.stage==LF_LEFT) {
                require(frame.left!=null&&frame.left.owned,"Level left result missing");
                if(frame.tag==1) frame.stage=LF_BUILD;
                else { frame.stage=LF_RIGHT; pushLevelFrame(state,((Node)frame.original).storageField(1)); }
                return;
            }
            if(frame.stage==LF_RIGHT) frame.stage=LF_BUILD;
            if(frame.stage==LF_BUILD) {
                Node original=(Node)frame.original; Object selected; int role=frame.tag==1?2:frame.tag==2?3:4;
                if(sameLevel(frame.left.value,original.storageField(0))&&(frame.tag==1||sameLevel(frame.right.value,original.storageField(1)))) selected=original;
                else if(frame.tag==1) selected=null;
                else if(frame.tag==2) selected=smartLevelMax(state,frame.left.value,frame.right.value);
                else {
                    boolean nonzero=levelNotZero(state,frame.right.value); if(nonzero) role=3;
                    selected=smartLevelIMax(state,frame.left.value,frame.right.value,nonzero);
                }
                if(selected!=null) { frame.result=retainedLevel(state,selected); ownLevelCredit(frame.result); frame.stage=LF_FINISH; }
                else callLevelHelper(action,state,frame,role);
                return;
            }
            if(frame.stage==LF_ASSIGNED) {
                if(sameLevel(frame.assignment.value,frame.result.value)) frame.stage=LF_FINISH;
                else {
                    require(state.saved.size()<MAX_LEVEL_INSTANTIATION_SAVED,"Level instantiation saved-assignment limit");
                    LevelCredit saved=retainedLevel(state,frame.assignment.value); state.saved.add(saved); ownLevelCredit(saved);
                    frame.stage=LF_SET; callLevelHelper(action,state,frame,1);
                }
                return;
            }
            if(frame.stage==LF_FINISH) {
                if(frame.tag>=1&&frame.tag<=3&&frame.shared&&!frame.cached) {
                    require(state.cache.size()<MAX_LEVEL_INSTANTIATION_CACHE&&!state.cache.containsKey((Node)frame.original),"Level instantiation cache limit/duplicate");
                    LevelCredit cached=retainedLevel(state,frame.result.value);
                    state.cache.put((Node)frame.original,cached); state.cacheValues.add(cached); ownLevelCredit(cached); frame.cached=true;
                }
                frame.stage=LF_CLEAN; frame.cleanup=0;
            }
            if(frame.stage==LF_CLEAN) {
                if(frame.cleanup<4) {
                    LevelCredit credit=frame.cleanup==0?frame.right:frame.cleanup==1?frame.left:frame.cleanup==2?frame.assignment:frame.option;
                    frame.cleanup++; releaseLevelCredit(action,state,credit); return;
                }
                completeLevelFrame(state,frame); return;
            }
            throw error("Level instantiation helper continuation did not return");
        }
    }
    LevelSession newLevelSession(MVarContextCell context,InstantiationBudget budget,LevelInstantiationPolicy policy) {
        require(context!=null&&context.current!=null&&context.current.owned&&budget!=null&&policy!=null,"Level session requires current context owner, budget and policy");
        for(int role=0;role<5;role++) levelInstantiationHelper(policy,role);
        LevelSession session=new LevelSession(); session.context=context; session.budget=budget; session.policy=policy; return session;
    }
    private LevelSession currentLevelSession(RuntimeAction action) {
        return action==null?null:action.levelMvars!=null?action.levelMvars.session:
                vm.exprDelayed.currentDirectSession(action)!=null?vm.exprDelayed.currentDirectSession(action).levels:null;
    }
    /** Caller anchors all original cache keys through seal. No input retain. */
    void startLevelJob(LevelSession session,Object borrowedInput) {
        require(session.phase==LS_IDLE&&session.result==null&&session.call==null&&session.retiring==null
                &&session.frames.isEmpty()&&session.active.isEmpty(),"Level session is not idle for a new job");
        require(session.context.current!=null&&session.context.current.owned,"Level session context owner is absent");
        vm.levelNode(borrowedInput);
        for(int role=0;role<5;role++) levelInstantiationHelper(session.policy,role);
        pushLevelFrame(session,borrowedInput); session.phase=LS_RUNNING;
    }
    LevelCredit takeLevelJobResult(LevelSession session) {
        require(session.phase==LS_RESULT&&session.result!=null&&session.result.owned&&session.call==null&&session.retiring==null
                &&session.frames.isEmpty()&&session.active.isEmpty(),"Level session has no completed owned result");
        LevelCredit result=session.result; session.result=null; session.phase=LS_IDLE; return result;
    }
    void sealLevelSession(LevelSession session) {
        require(session.phase==LS_IDLE&&session.result==null&&session.call==null&&session.retiring==null
                &&session.frames.isEmpty()&&session.active.isEmpty(),"Level session must be idle with result taken before seal");
        session.cache.clear(); session.active.clear(); session.phase=LS_SEALED;
    }
    void resumeLevelRetiring(RuntimeAction action,LevelSession session) {
        if(session.retiring!=null) {
            require(!session.retiring.owned,"Level cleanup returned without claiming retiring owner");
            session.retiring=null; action.retiring=null; action.releaseClaimed=false;
        }
    }
    /** Drain only this worker's saved/cache owners; never consume its shared cell. */
    void stepLevelSessionDrain(RuntimeAction action,LevelSession session) {
        require(session.phase==LS_SEALED||session.phase==LS_DRAINING,"Level session is not sealed for drain");
        levelWork(session,1); resumeLevelRetiring(action,session);
        session.phase=LS_DRAINING;
        if(session.drainStage==0) {
            if(session.drainCursor<session.saved.size()) {
                LevelCredit credit=session.saved.get(session.saved.size()-1-session.drainCursor++);
                releaseLevelCredit(action,session,credit); return;
            }
            session.drainStage=1; session.drainCursor=0;
        }
        if(session.drainStage==1) {
            if(session.drainCursor<session.cacheValues.size()) {
                LevelCredit credit=session.cacheValues.get(session.cacheValues.size()-1-session.drainCursor++);
                releaseLevelCredit(action,session,credit); return;
            }
            session.drainStage=2;
        }
        require(session.retiring==null&&session.cache.isEmpty()&&session.active.isEmpty(),"Level session drain retains a pending cursor");
        session.saved.clear(); session.cacheValues.clear(); session.phase=LS_DRAINED;
    }
}
