package ansatz.lean.jvm.internal.exec;

import java.util.*;
import ansatz.lean.jvm.internal.exec.ExprTransforms.*;
import ansatz.lean.jvm.internal.exec.LevelInstantiation.*;
import static ansatz.lean.jvm.internal.exec.Interpreter.*;

/** Direct instantiateMVars session: an explicit frame stack that walks an Expr,
 * resolves assigned metavariables and delayed assignments through guest helpers,
 * beta-reduces instantiated heads and rebuilds changed nodes. */
final class ExprDirectInstantiation {
    private final Interpreter vm;

    ExprDirectInstantiation(Interpreter vm) {
        this.vm=vm;
    }

    Function exprInstantiationHelper(ExprInstantiationPolicy policy,int role) {
        Header header=policy.helpers[role]; int id=vm.program.functionId(header); Function f=vm.program.functions[id];
        require(f.header==header&&f.intrinsic==0&&f.hostExtern==null&&vm.program.guestExports[id]==null,
                "Expr helper is not the current exact ordinary Function");
        requireExecutableAbi(f); require(f.resultType==OBJ,"Expr helper requires OBJ result");
        for(int lane:f.paramTypes) require(lane==OBJ,"Expr helper requires OBJ parameters");
        return vm.preflightCallable(f,true);
    }
    static final int DS_IDLE=0,DS_RUNNING=1,DS_RESULT=2,DS_SEALED=3,DS_DRAINING=4,DS_DRAINED=5;
    static final int MAX_DIRECT_FRAMES=100_000,MAX_DIRECT_CACHE=100_000,MAX_DIRECT_SAVED=100_000,
            MAX_DIRECT_NAMES=100_000,MAX_DIRECT_ARGUMENTS=100_000,MAX_DIRECT_LEVELS=100_000;
    abstract static class ExprDirectTask {
        ExprDirectTask child;
        ExprCredit result,received;
        int stage,cleanup;
        boolean completed,helperDone;
    }
    static final class DirectVisitFrame extends ExprDirectTask {
        Node original; boolean shared; int cursor;
        ExprCredit cacheTemporary;
        final ExprCredit[] children=new ExprCredit[3];
        LevelCredit level; ExprCredit levels;
        DirectVisitFrame(Node original) { this.original=original; }
    }
    static final class DirectMVarFrame extends ExprDirectTask {
        Node original; Object name; ExprCredit assigned,delayed;
        DirectMVarFrame(Node original) { this.original=original; }
    }
    static final class DirectAssignmentFrame extends ExprDirectTask {
        Object name; ExprCredit option,assigned,newValue;
        boolean present;
        DirectAssignmentFrame(Object name) { this.name=name; }
    }
    static final class DirectDelayedFrame extends ExprDirectTask {
        Object name; ExprCredit option,recordTemporary,pendingName,conditionResult;
        DirectDelayedFrame(Object name) { this.name=name; }
    }
    static final class DirectAppFrame extends ExprDirectTask {
        Node original; Object cursor,name; ExprCredit assigned,delayed;
        DirectAppFrame(Node original) { this.original=original; }
    }
    static final class DirectNonMvarAppFrame extends ExprDirectTask {
        Node original; ExprCredit argument,function;
        DirectNonMvarAppFrame(Node original) { this.original=original; }
    }
    static final class DirectAppBetaFrame extends ExprDirectTask {
        Object cursor; ExprCredit functionOptional,betaParameter,argumentTemporary;
        final ArrayList<ExprCredit> arguments=new ArrayList<>();
        DirectAppBetaFrame(Object input,ExprCredit function) { this.cursor=input; this.functionOptional=function; }
    }
    static final class DirectLevelFrame extends ExprDirectTask {
        Object input; LevelCredit levelResult;
        DirectLevelFrame(Object input) { this.input=input; }
    }
    static final class DirectLevelsFrame extends ExprDirectTask {
        Object original,cursor; final ArrayList<Node> cells=new ArrayList<>();
        LevelCredit firstChanged,currentHead,headLoan;
        ExprCredit list,replacement,tailLoan,consCredit;
        Node building; int index,builtFields;
        DirectLevelsFrame(Object original) { this.original=original; }
    }
    static final class DirectNameEntry {
        int hash; ExprCredit name;
        DirectNameEntry(int hash,ExprCredit name) { this.hash=hash; this.name=name; }
    }
    static final class DirectHelperPacket {
        Function function; int role; Object[] arguments; boolean[] owned;
        boolean started,entered;
        ExprDirectTask target;
    }
    static final class ExprDirectSession {
        MVarContextCell context; InstantiationBudget budget; LevelSession levels; ExprInstantiationPolicy policy;
        final ArrayDeque<ExprDirectTask> tasks=new ArrayDeque<>();
        final IdentityHashMap<Node,ExprCredit> cache=new IdentityHashMap<>();
        final ArrayList<ExprCredit> cacheValues=new ArrayList<>(),saved=new ArrayList<>();
        final HashMap<Integer,ArrayList<DirectNameEntry>> normalized=new HashMap<>();
        final ArrayList<DirectNameEntry> nameOwners=new ArrayList<>();
        DirectHelperPacket call; ExprPacket constructorCall;
        ExprCredit result,retiring;
        boolean hasUpdateableDelayed; int phase,drainStage,drainCursor;
    }
    void directHelperEntry(Function function,Object[] arguments) {
        RuntimeAction action=vm.runtimeAction;
        ExprDirectSession session=vm.exprDelayed.currentDirectSession(action);
        if(session==null||session.phase!=DS_RUNNING) return;
        DirectHelperPacket packet=session.call;
        if(packet==null||packet.entered||packet.function!=function||packet.arguments!=arguments) return;
        require(packet.started,"Direct Expr helper entered before packet publication");
        packet.entered=true; Arrays.fill(packet.owned,false);
    }
    void directWork(ExprDirectSession session,long amount) {
        vm.exprTransforms.instantiationWork(session.budget,amount,"Direct Expr work outside bounded profile","Direct Expr interrupted");
    }
    private void pushDirect(ExprDirectSession session,ExprDirectTask task) {
        require(session.phase==DS_RUNNING&&session.tasks.size()<MAX_DIRECT_FRAMES,"Direct Expr task/frame limit outside profile");
        session.tasks.addLast(task);
    }
    private void directSelect(ExprDirectTask task,Object value) { task.result=vm.exprTransforms.exprCredit(value); vm.exprTransforms.acquireExpr(task.result); }
    boolean releaseDirect(RuntimeAction action,ExprDirectSession session,ExprCredit credit) {
        if(credit==null||!credit.owned) return false;
        require(session.levels.retiring==null,"Simultaneous direct/Level retiring owners");
        session.retiring=credit; action.retiring=credit.value; action.releaseClaimed=false;
        boolean dispatch;
        try { dispatch=vm.beginRelease(credit.value,1,ACTION_BODY); credit.owned=false; }
        finally { if(action.releaseClaimed) credit.owned=false; }
        if(!dispatch) { session.retiring=null; action.retiring=null; action.releaseClaimed=false; }
        return dispatch;
    }
    void resumeDirectRetiring(RuntimeAction action,ExprDirectSession session) {
        require(session.retiring==null||session.levels.retiring==null,"Simultaneous direct/Level retiring owners");
        if(session.retiring!=null) {
            require(!session.retiring.owned,"Direct Expr retiring owner was not claimed");
            session.retiring=null; action.retiring=null; action.releaseClaimed=false;
        }
        vm.levels.resumeLevelRetiring(action,session.levels);
    }
    private ExprDirectTask takeDirectChild(ExprDirectTask parent,Class<?> expected) {
        require(parent.child!=null&&parent.child.completed&&expected.isInstance(parent.child),"Direct Expr child completion kind differs");
        return parent.child;
    }
    private ExprCredit takeDirectExprChild(ExprDirectTask parent,Class<?> expected) {
        ExprDirectTask child=takeDirectChild(parent,expected);
        require(child.result!=null&&child.result.owned,"Direct Expr child result owner missing");
        ExprCredit result=child.result; child.result=null; parent.child=null; return result;
    }
    private boolean directNameEqual(ExprDirectSession session,Object left,Object right) {
        return vm.exprDelayed.mvarNameEqual(session.budget,left,right);
    }
    private int directNameHash(ExprDirectSession session,Object value) {
        directWork(session,1); Node node=vm.nameNode(value); return (int)(node==null?1723:readScalar(node,0,U64));
    }
    private boolean directNameContains(ExprDirectSession session,Object value) {
        int hash=directNameHash(session,value); ArrayList<DirectNameEntry> bucket=session.normalized.get(hash);
        if(bucket==null) return false;
        for(DirectNameEntry entry:bucket) {
            directWork(session,1); require(entry.name.owned,"Normalized Name key owner missing");
            if(directNameEqual(session,value,entry.name.value)) return true;
        }
        return false;
    }
    private void directNameInsert(ExprDirectSession session,Object value) {
        int hash=directNameHash(session,value); ArrayList<DirectNameEntry> bucket=session.normalized.get(hash);
        if(bucket!=null) for(DirectNameEntry entry:bucket) {
            directWork(session,1); if(directNameEqual(session,value,entry.name.value)) return;
        }
        require(session.nameOwners.size()<MAX_DIRECT_NAMES,"Direct Expr normalized Name limit");
        DirectNameEntry entry=new DirectNameEntry(hash,vm.exprTransforms.exprCredit(value)); session.nameOwners.add(entry);
        if(bucket==null) { bucket=new ArrayList<>(); session.normalized.put(hash,bucket); }
        bucket.add(entry); vm.exprTransforms.acquireExpr(entry.name);
    }
    private static boolean exprHasMVars(long word) { return (word&((1L<<41)|(1L<<42)))!=0; }
    private void requireDirectReceiverFree(RuntimeAction action,ExprDirectSession session) {
        require(session.call==null&&session.constructorCall==null&&session.levels.call==null&&vm.objects[action.slot]==null,
                "Multiple outstanding direct/constructor/Level packets");
    }
    private void callDirectHelper(RuntimeAction action,ExprDirectSession session,ExprDirectTask target,int role) {
        directWork(session,1); require(role!=2,"Pass one does not call delayed fvars accessor"); requireDirectReceiverFree(action,session);
        Function helper=exprInstantiationHelper(session.policy,role);
        DirectHelperPacket packet=new DirectHelperPacket(); packet.function=helper; packet.role=role; packet.target=target;
        packet.arguments=new Object[helper.params.length]; packet.owned=new boolean[packet.arguments.length]; session.call=packet;
        if(role==3) {
            DirectDelayedFrame frame=(DirectDelayedFrame)target;
            require(frame.recordTemporary!=null&&frame.recordTemporary.owned,"Delayed accessor temporary owner missing");
            packet.arguments[0]=frame.recordTemporary.value; vm.validateHostObject(packet.arguments[0]); vm.inc(packet.arguments[0],1); packet.owned[0]=true;
        } else {
            LevelCredit context=session.context.current;
            require(context!=null&&context.owned,"Direct Expr current context owner missing"); packet.arguments[0]=context.value;
            if(role==4) { packet.owned[0]=true; context.owned=false; session.context.current=null; }
            else { vm.inc(packet.arguments[0],1); packet.owned[0]=true; }
            Object name=role==1?((DirectDelayedFrame)target).name:((DirectAssignmentFrame)target).name;
            packet.arguments[1]=name; vm.nameNode(name); vm.inc(name,1); packet.owned[1]=true;
            if(role==4) {
                DirectAssignmentFrame frame=(DirectAssignmentFrame)target; require(frame.newValue!=null&&frame.newValue.owned,"Direct assignment result missing");
                packet.arguments[2]=frame.newValue.value; vm.exprNode(packet.arguments[2]); vm.inc(packet.arguments[2],1); packet.owned[2]=true;
            }
        }
        IdentityHashMap<Node,Integer> known=new IdentityHashMap<>();
        for(int i=0;i<packet.arguments.length;i++) {
            require(packet.owned[i],"Direct Expr helper argument not owned"); vm.validateHostObject(packet.arguments[i]);
            if(packet.arguments[i] instanceof Node) known.merge((Node)packet.arguments[i],1,Integer::sum);
        }
        for(Map.Entry<Node,Integer> entry:known.entrySet()) require(entry.getKey().refCount()==0||entry.getKey().refCount()>=entry.getValue(),"Direct Expr helper alias credits differ");
        packet.started=true; vm.enterExplicit(helper,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Direct Expr helper did not publish frame or CodeRequest");
    }
    void validateDirectOption(Object value,boolean expression) {
        if(ERASED.equals(value)) return;
        Node option=vm.constructorNode(value);
        require(option.storageTag()==1&&option.fieldCount()==1&&option.scalarCount()==0,"Direct Expr helper returned malformed Option");
        if(expression) vm.exprNode(option.storageField(0)); else vm.validateHostObject(option.storageField(0));
    }
    private void receiveDirectHelper(RuntimeAction action,ExprDirectSession session) {
        DirectHelperPacket packet=session.call; require(packet.entered,"Direct Expr helper returned before entry");
        Object value=vm.objects[action.slot]; ExprDirectTask target=packet.target;
        if(packet.role==4) {
            vm.validateHostObject(value); require(session.context.current==null,"Direct Expr setter replaces a live context owner");
            session.context.current=new LevelCredit(value,true); vm.objects[action.slot]=null; target.helperDone=true;
        } else {
            require(target.received==null,"Direct Expr helper result receiver occupied");
            if(packet.role==0||packet.role==1) validateDirectOption(value,packet.role==0);
            else if(packet.role==3) vm.nameNode(value); else throw error("Unsupported direct Expr helper role");
            target.received=new ExprCredit(value,true); vm.objects[action.slot]=null;
        }
        session.call=null;
    }
    private void callDirectConstructor(RuntimeAction action,ExprDirectSession session,ExprDirectTask target,int role,Object[] values) {
        directWork(session,1); requireDirectReceiverFree(action,session);
        ExprPacket packet=vm.exprTransforms.prepareExprConstructorPacket(session.policy.constructors,role,values); packet.directTarget=target;
        session.constructorCall=packet; vm.exprTransforms.acquireExprConstructorPacket(packet); packet.started=true;
        vm.enterExplicit(packet.function,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Direct Expr constructor did not publish frame or CodeRequest");
    }
    private void receiveDirectConstructor(RuntimeAction action,ExprDirectSession session) {
        ExprPacket packet=session.constructorCall;
        require(packet.entered&&packet.directTarget!=null&&packet.directTarget.received==null,"Direct Expr constructor completion differs");
        ExprCredit result=vm.exprTransforms.takeExprConstructorResult(action,packet);
        packet.directTarget.received=result; session.constructorCall=null;
    }
    private void stepDirectAssignment(RuntimeAction action,ExprDirectSession session,DirectAssignmentFrame frame) {
        if(frame.stage==0) { frame.stage=1; callDirectHelper(action,session,frame,0); return; }
        if(frame.stage==1) {
            require(frame.received!=null&&frame.received.owned,"Direct getter Option missing"); frame.option=frame.received; frame.received=null;
            if(ERASED.equals(frame.option.value)) { frame.present=false; frame.stage=10; return; }
            frame.assigned=vm.exprTransforms.exprCredit(((Node)frame.option.value).storageField(0)); vm.exprTransforms.acquireExpr(frame.assigned);
            if(!exprHasMVars(vm.exprCachedData(frame.assigned.value))||directNameContains(session,frame.name)) {
                directSelect(frame,frame.assigned.value); frame.present=true; frame.stage=10; return;
            }
            directNameInsert(session,frame.name); frame.stage=2; pushDirect(session,new DirectVisitFrame(vm.exprNode(frame.assigned.value))); return;
        }
        if(frame.stage==2) {
            frame.newValue=takeDirectExprChild(frame,DirectVisitFrame.class);
            if(frame.newValue.value!=frame.assigned.value) {
                require(session.saved.size()<MAX_DIRECT_SAVED,"Direct Expr saved assignment limit");
                ExprCredit saved=vm.exprTransforms.exprCredit(frame.assigned.value); session.saved.add(saved); vm.exprTransforms.acquireExpr(saved);
                frame.stage=3; callDirectHelper(action,session,frame,4); return;
            }
            frame.stage=4;
        }
        if(frame.stage==3) { require(frame.helperDone,"Direct setter has no completed return"); frame.helperDone=false; frame.stage=4; }
        if(frame.stage==4) { directSelect(frame,frame.newValue.value); frame.present=true; frame.stage=10; }
        require(frame.stage==10,"Invalid direct assignment continuation");
        if(frame.cleanup<3) {
            ExprCredit credit=frame.cleanup==0?frame.newValue:frame.cleanup==1?frame.assigned:frame.option;
            frame.cleanup++; releaseDirect(action,session,credit); return;
        }
        frame.option=null; frame.assigned=null; frame.newValue=null; frame.completed=true;
    }
    private void stepDirectDelayed(RuntimeAction action,ExprDirectSession session,DirectDelayedFrame frame) {
        if(frame.stage==0) { frame.stage=1; callDirectHelper(action,session,frame,1); return; }
        if(frame.stage==1) {
            require(frame.received!=null&&frame.received.owned,"Delayed getter Option missing"); frame.option=frame.received; frame.received=null;
            if(ERASED.equals(frame.option.value)) { frame.result=frame.option; frame.option=null; frame.completed=true; return; }
            // option_ref::get_val returns by value; accessor then receives its own copy.
            frame.recordTemporary=vm.exprTransforms.exprCredit(((Node)frame.option.value).storageField(0)); vm.exprTransforms.acquireExpr(frame.recordTemporary);
            frame.stage=2; callDirectHelper(action,session,frame,3); return;
        }
        if(frame.stage==2) {
            require(frame.received!=null&&frame.received.owned,"Delayed pending Name missing"); frame.pendingName=frame.received; frame.received=null;
            frame.stage=3; releaseDirect(action,session,frame.recordTemporary); return;
        }
        if(frame.stage==3) { frame.stage=4; pushDirect(session,new DirectAssignmentFrame(frame.pendingName.value)); return; }
        if(frame.stage==4) {
            DirectAssignmentFrame assignment=(DirectAssignmentFrame)takeDirectChild(frame,DirectAssignmentFrame.class);
            if(assignment.present) { require(assignment.result!=null&&assignment.result.owned,"Pending optional Expr owner missing");
                frame.conditionResult=assignment.result; assignment.result=null; session.hasUpdateableDelayed=true; }
            frame.child=null; frame.stage=5; releaseDirect(action,session,frame.conditionResult); return;
        }
        if(frame.stage==5) { frame.stage=6; releaseDirect(action,session,frame.pendingName); return; }
        require(frame.stage==6&&frame.option!=null&&frame.option.owned,"Delayed probe Option lifetime differs");
        frame.result=frame.option; frame.option=null; frame.recordTemporary=null; frame.pendingName=null; frame.conditionResult=null; frame.completed=true;
    }
    private void stepDirectMVar(RuntimeAction action,ExprDirectSession session,DirectMVarFrame frame) {
        if(frame.stage==0) { frame.name=frame.original.storageField(0); frame.stage=1; pushDirect(session,new DirectAssignmentFrame(frame.name)); return; }
        if(frame.stage==1) {
            DirectAssignmentFrame assignment=(DirectAssignmentFrame)takeDirectChild(frame,DirectAssignmentFrame.class);
            if(assignment.present) {
                require(assignment.result!=null&&assignment.result.owned,"Direct optional Expr missing"); frame.assigned=assignment.result; assignment.result=null;
                frame.child=null; directSelect(frame,frame.assigned.value); frame.stage=10;
            } else { frame.child=null; frame.stage=2; pushDirect(session,new DirectDelayedFrame(frame.name)); return; }
        }
        if(frame.stage==2) {
            frame.delayed=takeDirectExprChild(frame,DirectDelayedFrame.class); directSelect(frame,frame.original); frame.stage=10;
        }
        require(frame.stage==10,"Invalid direct MVar continuation");
        if(frame.cleanup<2) { ExprCredit credit=frame.cleanup++==0?frame.assigned:frame.delayed; releaseDirect(action,session,credit); return; }
        frame.assigned=null; frame.delayed=null; frame.completed=true;
    }
    private void stepDirectApp(RuntimeAction action,ExprDirectSession session,DirectAppFrame frame) {
        if(frame.stage==0) {
            if(frame.cursor==null) frame.cursor=frame.original;
            Node head=vm.exprNode(frame.cursor);
            if(head.storageTag()==5) { frame.cursor=head.storageField(0); return; }
            if(head.storageTag()!=2) { frame.stage=5; pushDirect(session,new DirectNonMvarAppFrame(frame.original)); return; }
            frame.name=head.storageField(0); frame.stage=1; pushDirect(session,new DirectAssignmentFrame(frame.name)); return;
        }
        if(frame.stage==1) {
            DirectAssignmentFrame assignment=(DirectAssignmentFrame)takeDirectChild(frame,DirectAssignmentFrame.class);
            if(assignment.present) {
                require(assignment.result!=null&&assignment.result.owned,"Assigned function optional owner missing");
                ExprCredit function=assignment.result;
                DirectAppBetaFrame beta=new DirectAppBetaFrame(frame.original,function);
                pushDirect(session,beta); assignment.result=null; frame.child=null; frame.stage=4; return;
            }
            frame.child=null; frame.stage=2; pushDirect(session,new DirectDelayedFrame(frame.name)); return;
        }
        if(frame.stage==2) {
            frame.delayed=takeDirectExprChild(frame,DirectDelayedFrame.class);
            frame.stage=5; pushDirect(session,new DirectNonMvarAppFrame(frame.original)); return;
        }
        if(frame.stage==4) { frame.result=takeDirectExprChild(frame,DirectAppBetaFrame.class); frame.completed=true; return; }
        if(frame.stage==5) { frame.result=takeDirectExprChild(frame,DirectNonMvarAppFrame.class); frame.stage=6; releaseDirect(action,session,frame.delayed); return; }
        require(frame.stage==6,"Invalid direct App continuation"); frame.delayed=null; frame.completed=true;
    }
    private void stepDirectNonMvarApp(RuntimeAction action,ExprDirectSession session,DirectNonMvarAppFrame frame) {
        if(frame.stage==0) { frame.stage=1; pushDirect(session,new DirectVisitFrame(vm.exprNode(frame.original.storageField(1)))); return; }
        if(frame.stage==1) {
            frame.argument=takeDirectExprChild(frame,DirectVisitFrame.class); Node function=vm.exprNode(frame.original.storageField(0)); frame.stage=2;
            pushDirect(session,function.storageTag()==5?new DirectNonMvarAppFrame(function):new DirectVisitFrame(function)); return;
        }
        if(frame.stage==2) {
            frame.function=takeDirectExprChild(frame,vm.exprNode(frame.original.storageField(0)).storageTag()==5?DirectNonMvarAppFrame.class:DirectVisitFrame.class);
            if(frame.function.value==frame.original.storageField(0)&&frame.argument.value==frame.original.storageField(1)) { directSelect(frame,frame.original); frame.stage=4; }
            else { frame.stage=3; callDirectConstructor(action,session,frame,3,new Object[]{frame.function.value,frame.argument.value}); return; }
        }
        if(frame.stage==3) { require(frame.received!=null&&frame.received.owned,"App constructor result missing"); frame.result=frame.received; frame.received=null; frame.stage=4; }
        if(frame.stage==4) {
            if(frame.cleanup<2) { ExprCredit credit=frame.cleanup++==0?frame.function:frame.argument; releaseDirect(action,session,credit); return; }
            frame.function=null; frame.argument=null; frame.completed=true; return;
        }
        throw error("Invalid non-MVar App continuation");
    }
    private void enterDirectBetaChild(RuntimeAction parent,ExprDirectSession session,DirectAppBetaFrame frame) {
        require(vm.runtimeAction==parent&&frame.stage==3&&vm.objects[parent.slot]==null&&session.call==null&&session.constructorCall==null
                &&session.levels.call==null&&session.levels.retiring==null&&session.retiring==null,"Direct beta parent is not ready");
        require(frame.betaParameter!=null&&frame.betaParameter.owned,"Direct beta parameter owner missing");
        for(int role=0;role<9;role++) vm.exprTransforms.exprConstructor(session.policy.constructors,role);
        RuntimeAction child=vm.newAction(ACTION_EXPR_MACHINERY,null,ACTION_BODY,parent.slot,ASSIGN,null);
        ExprMachineryState worker=new ExprMachineryState(); worker.policy=session.policy.constructors; worker.budget=session.budget;
        BetaJob beta=new BetaJob(); beta.function=frame.betaParameter; beta.reverseArgs=new Object[frame.arguments.size()];
        for(int i=0;i<beta.reverseArgs.length;i++) { require(frame.arguments.get(i).owned,"Direct reverse argument owner missing"); beta.reverseArgs[i]=frame.arguments.get(i).value; }
        worker.jobs.addLast(beta); child.exprMachinery=worker; vm.objects[child.slot]=null;
        vm.publishAction(child); frame.betaParameter=null;
    }
    private void stepDirectAppBeta(RuntimeAction action,ExprDirectSession session,DirectAppBetaFrame frame) {
        if(frame.stage==0) {
            Node cursor=vm.exprNode(frame.cursor);
            if(cursor.storageTag()==5) { frame.stage=1; pushDirect(session,new DirectVisitFrame(vm.exprNode(cursor.storageField(1)))); return; }
            require(frame.functionOptional!=null&&frame.functionOptional.owned,"Assigned optional function owner missing");
            frame.betaParameter=vm.exprTransforms.exprCredit(frame.functionOptional.value); vm.exprTransforms.acquireExpr(frame.betaParameter);
            frame.stage=3; enterDirectBetaChild(action,session,frame); return;
        }
        if(frame.stage==1) {
            frame.argumentTemporary=takeDirectExprChild(frame,DirectVisitFrame.class);
            require(frame.arguments.size()<MAX_DIRECT_ARGUMENTS,"Direct Expr argument buffer limit");
            ExprCredit entry=vm.exprTransforms.exprCredit(frame.argumentTemporary.value); frame.arguments.add(entry); vm.exprTransforms.acquireExpr(entry);
            frame.stage=2; releaseDirect(action,session,frame.argumentTemporary); return;
        }
        if(frame.stage==2) { frame.argumentTemporary=null; frame.cursor=vm.exprNode(frame.cursor).storageField(0); frame.stage=0; return; }
        if(frame.stage==3) {
            Object result=vm.objects[action.slot]; vm.exprNode(result); frame.result=new ExprCredit(result,true); vm.objects[action.slot]=null;
            frame.stage=4; frame.cleanup=0;
        }
        if(frame.stage==4) {
            // runtime::buffer destroys forward, including its outermost-first args.
            if(frame.cleanup<frame.arguments.size()) { ExprCredit entry=frame.arguments.get(frame.cleanup++); releaseDirect(action,session,entry); return; }
            frame.stage=5; releaseDirect(action,session,frame.functionOptional); return;
        }
        require(frame.stage==5,"Invalid assigned App beta continuation"); frame.arguments.clear(); frame.functionOptional=null; frame.completed=true;
    }
    private void stepDirectLevel(RuntimeAction action,ExprDirectSession session,DirectLevelFrame frame) {
        if(frame.stage==0) { requireDirectReceiverFree(action,session); vm.levels.startLevelJob(session.levels,frame.input); frame.stage=1; return; }
        vm.levels.stepLevelJob(action,session.levels);
        if(session.levels.phase==LevelInstantiation.LS_RESULT) { frame.levelResult=vm.levels.takeLevelJobResult(session.levels); frame.completed=true; }
    }
    private void stepDirectLevels(RuntimeAction action,ExprDirectSession session,DirectLevelsFrame frame) {
        if(frame.stage==0) {
            if(frame.cursor==null) frame.cursor=frame.original;
            if(ERASED.equals(frame.cursor)) { frame.index=frame.cells.size()-1; frame.stage=1; return; }
            Node cell=vm.constructorNode(frame.cursor);
            require(cell.storageTag()==1&&cell.fieldCount()==2&&cell.scalarCount()==0,"Invalid Const Level list layout");
            require(frame.cells.size()<MAX_DIRECT_LEVELS,"Direct Const Level list length/cycle outside profile");
            vm.levelNode(cell.storageField(0)); frame.cells.add(cell); frame.cursor=cell.storageField(1); return;
        }
        if(frame.stage==1) {
            if(frame.index<0) {
                if(frame.list==null) directSelect(frame,frame.original);
                else { frame.result=frame.list; frame.list=null; }
                frame.stage=8; vm.levels.releaseLevelCredit(action,session.levels,frame.firstChanged); return;
            }
            frame.stage=2; pushDirect(session,new DirectLevelFrame(frame.cells.get(frame.index).storageField(0))); return;
        }
        if(frame.stage==2) {
            DirectLevelFrame child=(DirectLevelFrame)takeDirectChild(frame,DirectLevelFrame.class);
            require(child.levelResult!=null&&child.levelResult.owned,"Const Level result missing");
            frame.currentHead=child.levelResult; child.levelResult=null; frame.child=null;
            Node cell=frame.cells.get(frame.index);
            if(frame.list==null) {
                if(LevelInstantiation.sameLevel(frame.currentHead.value,cell.storageField(0))) {
                    frame.stage=3; vm.levels.releaseLevelCredit(action,session.levels,frame.currentHead); return;
                }
                frame.firstChanged=frame.currentHead; frame.currentHead=null;
                frame.list=vm.buildDirectCons(session,frame,frame.firstChanged.value,cell.storageField(1));
                frame.index--; frame.stage=1; return;
            }
            frame.replacement=vm.buildDirectCons(session,frame,frame.currentHead.value,frame.list.value);
            frame.stage=4; releaseDirect(action,session,frame.list); return;
        }
        if(frame.stage==3) { frame.currentHead=null; frame.index--; frame.stage=1; return; }
        if(frame.stage==4) {
            require(frame.replacement!=null&&frame.replacement.owned,"Const prefix replacement list missing");
            frame.list=frame.replacement; frame.replacement=null; frame.stage=5;
            vm.levels.releaseLevelCredit(action,session.levels,frame.currentHead); return;
        }
        if(frame.stage==5) { frame.currentHead=null; frame.index--; frame.stage=1; return; }
        require(frame.stage==8&&frame.result!=null&&frame.result.owned,"Invalid Const Level list completion");
        frame.firstChanged=null; frame.currentHead=null; frame.cells.clear(); frame.cursor=null; frame.original=null; frame.completed=true;
    }
    private void stepDirectVisit(RuntimeAction action,ExprDirectSession session,DirectVisitFrame frame) {
        Node original=frame.original;
        if(frame.stage==0) {
            if(!exprHasMVars(vm.exprCachedData(original))) { directSelect(frame,original); frame.stage=91; return; }
            frame.shared=!exclusive(original);
            ExprCredit cached=frame.shared?session.cache.get(original):null;
            if(cached!=null) { require(cached.owned,"Direct Expr cache owner missing"); directSelect(frame,cached.value); frame.shared=false; frame.stage=91; return; }
            switch(original.storageTag()) {
                case 2: frame.shared=false; frame.stage=10; pushDirect(session,new DirectMVarFrame(original)); return;
                case 3: frame.stage=11; pushDirect(session,new DirectLevelFrame(original.storageField(0))); return;
                case 4: frame.stage=12; pushDirect(session,new DirectLevelsFrame(original.storageField(1))); return;
                case 5: frame.stage=10; pushDirect(session,new DirectAppFrame(original)); return;
                case 6: case 7: case 8: case 10: case 11: frame.stage=1; break;
                default: throw error("Inconsistent cached mvars on atomic Expr outside profile");
            }
        }
        if(frame.stage==1) {
            if(frame.child!=null) {
                require(frame.cursor<frame.children.length,"Direct Expr child cursor exceeds profile layout");
                frame.children[frame.cursor]=takeDirectExprChild(frame,DirectVisitFrame.class); frame.cursor++;
            }
            int count=ExprTransforms.exprChildCount(original.storageTag());
            if(frame.cursor<count) { pushDirect(session,new DirectVisitFrame(vm.exprNode(original.storageField(ExprTransforms.exprChildField(original.storageTag(),frame.cursor))))); return; }
            Object[] values=original.copyFields(); boolean changed=false;
            for(int i=0;i<count;i++) {
                require(frame.children[i]!=null&&frame.children[i].owned,"Direct Expr child result missing");
                int at=ExprTransforms.exprChildField(original.storageTag(),i); values[at]=frame.children[i].value; changed|=values[at]!=original.storageField(at);
            }
            if(!changed) { directSelect(frame,original); frame.stage=90; }
            else {
                if(original.storageTag()>=6&&original.storageTag()<=8) { values=Arrays.copyOf(values,values.length+1); values[values.length-1]=Long.valueOf(original.storageByte(8)); }
                frame.stage=3; callDirectConstructor(action,session,frame,ExprTransforms.exprCtorRole(original.storageTag()),values); return;
            }
        }
        if(frame.stage==3) {
            require(frame.received!=null&&frame.received.owned,"Direct Expr constructor result missing"); frame.result=frame.received; frame.received=null; frame.stage=90;
        }
        if(frame.stage==10) { frame.result=takeDirectExprChild(frame,original.storageTag()==2?DirectMVarFrame.class:DirectAppFrame.class); frame.stage=90; }
        if(frame.stage==11) {
            DirectLevelFrame child=(DirectLevelFrame)takeDirectChild(frame,DirectLevelFrame.class);
            require(child.levelResult!=null&&child.levelResult.owned,"Sort Level result missing"); frame.level=child.levelResult; child.levelResult=null; frame.child=null;
            if(LevelInstantiation.sameLevel(frame.level.value,original.storageField(0))) { directSelect(frame,original); frame.stage=90; }
            else { frame.stage=3; callDirectConstructor(action,session,frame,1,new Object[]{frame.level.value}); return; }
        }
        if(frame.stage==12) {
            frame.levels=takeDirectExprChild(frame,DirectLevelsFrame.class);
            if(ExprTransforms.sameExprField(frame.levels.value,original.storageField(1))) { directSelect(frame,original); frame.stage=90; }
            else { frame.stage=3; callDirectConstructor(action,session,frame,2,new Object[]{original.storageField(0),frame.levels.value}); return; }
        }
        if(frame.stage==90) {
            require(frame.result!=null&&frame.result.owned,"Direct Expr computed result missing"); frame.stage=91;
            if(frame.shared) {
                // Reentrant assignment normalization may already have inserted
                // this key: native insert keeps the first value, returns our r.
                ExprCredit copy=vm.exprTransforms.exprCredit(frame.result.value);
                if(session.cache.containsKey(original)) {
                    frame.cacheTemporary=copy; vm.exprTransforms.acquireExpr(copy); releaseDirect(action,session,copy); return;
                }
                require(session.cacheValues.size()<MAX_DIRECT_CACHE,"Direct Expr cache limit");
                session.cacheValues.add(copy); session.cache.put(original,copy); vm.exprTransforms.acquireExpr(copy);
            }
        }
        require(frame.stage==91,"Invalid direct Expr visit continuation");
        if(frame.cleanup<5) {
            int at=frame.cleanup++;
            if(at<3) releaseDirect(action,session,frame.children[2-at]);
            else if(at==3) vm.levels.releaseLevelCredit(action,session.levels,frame.level);
            else releaseDirect(action,session,frame.levels);
            return;
        }
        Arrays.fill(frame.children,null); frame.level=null; frame.levels=null; frame.cacheTemporary=null; frame.completed=true;
    }
    void stepExprDirectJob(RuntimeAction action,ExprDirectSession session) {
        require(session.phase==DS_RUNNING,"Direct Expr session has no running job"); directWork(session,1); resumeDirectRetiring(action,session);
        int packets=(session.call==null?0:1)+(session.constructorCall==null?0:1)+(session.levels.call==null?0:1);
        require(packets<=1,"Multiple outstanding direct/constructor/Level packets");
        if(session.call!=null) { receiveDirectHelper(action,session); return; }
        if(session.constructorCall!=null) { receiveDirectConstructor(action,session); return; }
        ExprDirectTask task=session.tasks.peekLast(); require(task!=null,"Missing direct Expr task");
        if(!task.completed) {
            if(task instanceof DirectVisitFrame) stepDirectVisit(action,session,(DirectVisitFrame)task);
            else if(task instanceof DirectAssignmentFrame) stepDirectAssignment(action,session,(DirectAssignmentFrame)task);
            else if(task instanceof DirectDelayedFrame) stepDirectDelayed(action,session,(DirectDelayedFrame)task);
            else if(task instanceof DirectMVarFrame) stepDirectMVar(action,session,(DirectMVarFrame)task);
            else if(task instanceof DirectAppFrame) stepDirectApp(action,session,(DirectAppFrame)task);
            else if(task instanceof DirectNonMvarAppFrame) stepDirectNonMvarApp(action,session,(DirectNonMvarAppFrame)task);
            else if(task instanceof DirectAppBetaFrame) stepDirectAppBeta(action,session,(DirectAppBetaFrame)task);
            else if(task instanceof DirectLevelFrame) stepDirectLevel(action,session,(DirectLevelFrame)task);
            else stepDirectLevels(action,session,(DirectLevelsFrame)task);
            return;
        }
        Iterator<ExprDirectTask> ancestors=session.tasks.descendingIterator(); ancestors.next();
        ExprDirectTask parent=ancestors.hasNext()?ancestors.next():null;
        if(parent==null) {
            require(task instanceof DirectVisitFrame&&task.result!=null&&task.result.owned&&session.result==null
                    &&session.context.current!=null&&session.context.current.owned&&session.levels.phase==LevelInstantiation.LS_IDLE,
                    "Direct root completion ownership differs");
            session.result=task.result; task.result=null; session.phase=DS_RESULT;
        } else { require(parent.child==null,"Direct Expr child receiver occupied"); parent.child=task; }
        session.tasks.removeLast();
    }
    ExprCredit takeExprDirectResult(ExprDirectSession session) {
        require(session.phase==DS_RESULT&&session.tasks.isEmpty()&&session.result!=null&&session.result.owned
                &&session.call==null&&session.constructorCall==null&&session.retiring==null&&session.levels.retiring==null,
                "Direct Expr result is not ready");
        ExprCredit result=session.result; session.result=null; session.phase=DS_IDLE; return result;
    }
    void sealExprDirectSession(ExprDirectSession session) {
        require(session.phase==DS_IDLE&&session.result==null&&session.tasks.isEmpty()&&session.call==null
                &&session.constructorCall==null&&session.retiring==null&&session.levels.retiring==null,
                "Direct Expr session is not idle with result taken");
        vm.levels.sealLevelSession(session.levels); session.cache.clear(); session.phase=DS_SEALED;
    }
    void stepExprDirectDrain(RuntimeAction action,ExprDirectSession session) {
        require(session.phase==DS_SEALED||session.phase==DS_DRAINING,"Direct Expr session is not sealed for drain");
        directWork(session,1); resumeDirectRetiring(action,session); session.phase=DS_DRAINING;
        if(session.drainStage<3) {
            int size=session.drainStage==0?session.saved.size():session.drainStage==1?session.cacheValues.size():session.nameOwners.size();
            if(session.drainStage==2) session.normalized.clear();
            if(session.drainCursor<size) {
                int at=size-1-session.drainCursor++;
                ExprCredit credit=session.drainStage==0?session.saved.get(at):session.drainStage==1?session.cacheValues.get(at):session.nameOwners.get(at).name;
                releaseDirect(action,session,credit); return;
            }
            session.drainStage++; session.drainCursor=0; return;
        }
        vm.levels.stepLevelSessionDrain(action,session.levels);
        if(session.levels.phase!=LevelInstantiation.LS_DRAINED) return;
        session.saved.clear(); session.cacheValues.clear(); session.nameOwners.clear(); session.normalized.clear(); session.phase=DS_DRAINED;
    }
}
