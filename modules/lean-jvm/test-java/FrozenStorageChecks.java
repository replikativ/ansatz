import ansatz.lean.jvm.internal.exec.Interpreter;
import ansatz.lean.jvm.internal.exec.Interpreter.Node;
import ansatz.lean.jvm.internal.exec.Interpreter.DataCtor;
import ansatz.lean.jvm.internal.exec.Interpreter.DataRef;
import java.lang.reflect.*;
import java.math.BigInteger;
import java.util.*;
import java.util.concurrent.atomic.AtomicReference;

/** Private fixed-plan storage proof, not native authority or public admission. */
public final class FrozenStorageChecks {
    static int checks;
    static final Class<?> PLAN=frozenPlanClass();
    static Class<?> frozenPlanClass() {
        try { return Class.forName("ansatz.lean.jvm.internal.exec.FrozenValues$FrozenPlan"); }
        catch(Exception failure) { throw new AssertionError(failure); }
    }
    static final Class<?> PLAN_ARRAY=Array.newInstance(PLAN,0).getClass();
    static Class<?> nested(String name) {
        try { return Class.forName(Interpreter.class.getName()+"$"+name); }
        catch(Exception failure) { throw new AssertionError(failure); }
    }
    static Field field(Class<?> type,String name) throws Exception { Field f=type.getDeclaredField(name);f.setAccessible(true);return f; }
    static Object get(Object value,String name) throws Exception { return field(value.getClass(),name).get(value); }
    static void set(Object value,String name,Object next) throws Exception { field(value.getClass(),name).set(value,next); }
    static Object call(Interpreter engine,String name,Class<?>[] types,Object... args) throws Exception {
        Method method=Interpreter.class.getDeclaredMethod(name,types);method.setAccessible(true);
        try { return method.invoke(engine,args); }
        catch(InvocationTargetException failure) {
            Throwable cause=failure.getCause();if(cause instanceof Exception) throw (Exception)cause;
            throw (Error)cause;
        }
    }
    static Object plan(int kind,int tag,int scalarBytes,int[] widths,Object... children) throws Exception {
        Constructor<?> ctor=PLAN.getDeclaredConstructor(int.class,int.class,int.class,PLAN_ARRAY,int[].class);ctor.setAccessible(true);
        Object array=Array.newInstance(PLAN,children.length);for(int i=0;i<children.length;i++) Array.set(array,i,children[i]);
        return ctor.newInstance(kind,tag,scalarBytes,array,widths);
    }
    static Object leaf(int kind) throws Exception { return plan(kind,0,0,new int[0]); }
    static Object record(Object... children) throws Exception { return plan(3,0,0,new int[0],children); }
    static Object freeze(Interpreter e,Object value,Object plan) throws Exception { return call(e,"freezeData",new Class<?>[]{Object.class,PLAN},value,plan); }
    static Node ctor(Interpreter e,Object... children) { return (Node)e.constructDataArguments(new DataCtor[]{new DataCtor(0,children)},new Object[]{new DataRef(0)})[0]; }
    static Interpreter engine() { return new Interpreter(Interpreter.prepare(Collections.emptyList()),true); }
    static Object[] fields(Node n) throws Exception { return (Object[])get(n,"fields"); }
    static byte[] scalars(Node n) throws Exception { return (byte[])get(n,"scalars"); }
    static int rc(Node n) throws Exception { return (Integer)get(n,"rc"); }
    static void check(boolean result) { checks++;if(!result) throw new AssertionError("Frozen storage check "+checks); }
    interface Attempt { void run() throws Exception; }
    static void refuse(Attempt attempt) throws Exception {
        try { attempt.run();throw new AssertionError("Missing frozen refusal"); }
        catch(IllegalArgumentException|IllegalStateException expected) { checks++; }
    }
    static void release(Interpreter e,Object value) { e.startRelease(value,1);while(!e.advance(1000)) {}e.takeResult(); }
    static final class MutableInteger extends BigInteger { MutableInteger() { super("1"); } }
    static Map<String,Object> map(Object... pairs) {
        Map<String,Object> out=new LinkedHashMap<>();for(int i=0;i<pairs.length;i+=2) out.put((String)pairs[i],pairs[i+1]);return out;
    }
    static Object name(String text) { return List.of("str",List.of("anonymous"),text); }
    static Object bytePushExtern() {
        String symbol="lean_byte_array_push";
        return map("kind","decl","name",name(symbol),"ir",map("extern",map("f",name(symbol),
                "xs",List.of(map("x",map("idx",1),"ty","object","borrow",false),map("x",map("idx",2),"ty","uint8","borrow",false)),
                "type","object","ext",map("entries",List.of(map("standard",map("backend",name("all"),"fn",symbol)))))));
    }
    static DataCtor[] chain(int count,Object leaf) {
        DataCtor[] recipes=new DataCtor[count];
        for(int i=0;i<count;i++) recipes[i]=new DataCtor(0,new Object[]{i==0?leaf:new DataRef(i-1)});
        return recipes;
    }
    static void refuseWithoutAllocation(Interpreter engine,Attempt attempt) throws Exception {
        long allocations=engine.allocations,retains=engine.retains,releases=engine.releases,stores=engine.stores;
        refuse(attempt);
        check(engine.allocations==allocations&&engine.retains==retains&&engine.releases==releases&&engine.stores==stores);
    }
    static Object[] mixedStrings(Object frozen,String shared,int tailUnits) {
        Object[] fields=new Object[9];fields[0]=frozen;
        Arrays.fill(fields,1,8,shared);fields[8]="t".repeat(tailUnits);return fields;
    }
    public static void main(String[] args) throws Exception {
        Object nat=leaf(0),string=leaf(1),bytes=leaf(5),row=record(nat,string);
        for(String name:new String[]{"fields","scalars","tag","rc"}) check(Modifier.isPrivate(field(Node.class,name).getModifiers()));
        Interpreter e=engine();Node n=ctor(e,7L,"text");e.inc(n,1);
        Interpreter globalEngine=new Interpreter(Interpreter.prepare(List.of(bytePushExtern())),true);
        set(globalEngine,"constants",new Object[]{n});set(globalEngine,"constantReady",new boolean[]{true});
        Object[] original=fields(n);Object cert=freeze(e,n,row);Object stamp=get(n,"frozen");
        check(rc(n)==0&&fields(n)==original&&stamp!=null&&(Boolean)get(cert,"published"));
        check(get(cert,"value")==n);release(e,n);check(!(Boolean)get(n,"dead")&&fields(n)[0].equals(7L));
        check(get(freeze(e,n,row),"cert")==get(cert,"cert"));
        Object erased=plan(6,0,0,new int[0],row);Object erasedValue=freeze(e,n,erased);
        check(get(n,"frozen")==stamp&&get(erasedValue,"value")==n); // immutable initial stamp
        refuse(()->freeze(e,n,record(string,string)));check(get(n,"frozen")==stamp);
        refuse(()->call(e,"pointerWord",new Class<?>[]{Object.class},n));check(get(n,"metadata")==null);
        // Exact immutable leaves, no inspecting attacker-controlled subclass methods.
        refuse(()->freeze(e,new MutableInteger(),nat));refuse(()->freeze(e,"\ud800",string));
        refuse(()->freeze(e,-1L,nat));refuse(()->freeze(e,3L,plan(2,3,0,new int[0])));
        check(get(freeze(e,2L,plan(2,3,0,new int[0])),"value").equals(2L));
        // An rc0 marker is never an immutable certificate; inspect all descendants.
        Node invalid=ctor(e,1L);set(invalid,"rc",0);set(invalid,"ref",true);
        Node parent=ctor(e,0L);fields(parent)[0]=invalid;
        refuse(()->freeze(e,parent,record(record(nat))));check(rc(parent)==1&&get(parent,"frozen")==null);
        set(invalid,"ref",false);set(invalid,"dead",true);
        refuse(()->freeze(e,parent,record(record(nat))));check(rc(parent)==1);
        // Actual owning cycles differ from erased wrappers of the same Node.
        Node cycle=ctor(e,0L);fields(cycle)[0]=cycle;
        refuse(()->freeze(e,cycle,record(record(nat))));check(rc(cycle)==1&&get(cycle,"frozen")==null);
        // Spare object slots are physical custody, even outside the logical view.
        Node array=(Node)call(e,"newArray",new Class<?>[]{int.class,int.class},1,3);fields(array)[0]=n;fields(array)[2]=invalid;
        Object arrayPlan=plan(4,0,0,new int[0],row);
        refuse(()->freeze(e,array,arrayPlan));check(rc(array)==1&&get(array,"frozen")==null);
        fields(array)[2]=null;Object arrayInput=freeze(e,array,arrayPlan);Object[] arrayBacking=fields(array);
        Node copied=(Node)call(e,"exclusiveArray",new Class<?>[]{Node.class,boolean.class},array,false);
        check(copied!=array&&fields(array)==arrayBacking&&fields(copied)[0]==n);
        fields(copied)[0]=0L;check(fields(array)[0]==n&&array.arraySize()==1);
        refuse(()->call(e,"setArraySize",new Class<?>[]{Node.class,int.class},array,0));
        Node buffer=(Node)e.constructDataArguments(new DataCtor[]{DataCtor.bytes(new byte[]{1,2,3})},new Object[]{new DataRef(0)})[0];
        byte[] backing=scalars(buffer);Object byteInput=freeze(e,buffer,bytes);
        check(scalars(buffer)==backing&&buffer.byteArraySize()==3);release(e,buffer);check(backing[0]==1);
        refuse(()->call(e,"setByteArraySize",new Class<?>[]{Node.class,int.class},buffer,0));
        try(Interpreter updater=new Interpreter(Interpreter.prepare(List.of(bytePushExtern())),true)) {
            Node imported=(Node)updater.constructDataArguments(new DataCtor[0],new Object[]{byteInput})[0];
            updater.start(0,new Object[]{imported,4L});while(!updater.advance(1000)) { }
            Node updated=(Node)updater.takeResult();check(updated!=buffer&&updated.byteArraySize()==4&&scalars(updated)[3]==4);
            check(scalars(buffer)==backing&&buffer.byteArraySize()==3&&Arrays.equals(backing,new byte[]{1,2,3}));release(updater,updated);
        }
        // Exact scalar storage preserves all raw bits; equality semantics are a later public layer.
        for(long raw:new long[]{0L,Long.MIN_VALUE,0x7ff8000000000001L,0x7ff8000000000002L}) {
            Node scalar=(Node)e.constructDataArguments(new DataCtor[]{DataCtor.boxedScalar("float",raw)},new Object[]{new DataRef(0)})[0];
            byte[] scalarBacking=scalars(scalar);freeze(e,scalar,plan(3,0,8,new int[]{8}));
            long read=0;for(int i=0;i<8;i++) read|=(scalarBacking[i]&255L)<<(8*i);
            check(read==raw&&scalars(scalar)==scalarBacking);
        }
        // New single-parent frontier charges a previously certified large child in constant work.
        Node large=(Node)e.constructDataArguments(new DataCtor[]{DataCtor.bytes(new byte[600_000])},new Object[]{new DataRef(0)})[0];
        Object largeInput=freeze(e,large,bytes);Node wrapped=ctor(e,largeInput);Object wrappedPlan=record(bytes);
        Object wrappedInput=freeze(e,wrapped,wrappedPlan);
        check((Long)get(get(wrappedInput,"cert"),"payloadCost")==600_000L&&fields(wrapped)[0]==large);
        Object wrappedAgain=freeze(e,wrapped,wrappedPlan);check(get(wrappedAgain,"cert")==get(wrappedInput,"cert"));
        Node otherLarge=(Node)e.constructDataArguments(new DataCtor[]{DataCtor.bytes(new byte[600_000])},new Object[]{new DataRef(0)})[0];
        Object otherLargeInput=freeze(e,otherLarge,bytes);
        refuse(()->e.constructDataArguments(new DataCtor[0],new Object[]{largeInput,otherLargeInput}));
        Node oversized=ctor(e,0L,0L);fields(oversized)[0]=large;fields(oversized)[1]=otherLarge;
        refuse(()->freeze(e,oversized,record(bytes,bytes)));check(rc(oversized)==1&&get(oversized,"frozen")==null);
        Node repeated=(Node)e.constructDataArguments(new DataCtor[]{DataCtor.bytes(new byte[600_000])},new Object[]{new DataRef(0)})[0];
        Node firstDiamond=ctor(e,0L,0L);fields(firstDiamond)[0]=repeated;fields(firstDiamond)[1]=repeated;
        Object firstDiamondInput=freeze(e,firstDiamond,record(bytes,bytes));
        check((Long)get(get(firstDiamondInput,"cert"),"payloadCost")==600_000L&&rc(repeated)==0);
        // String limits count logical UTF-16 occurrences separately from scalar/buffer bytes.
        String sharedText="s".repeat(60_000);Object[] stringFields=new Object[10];Arrays.fill(stringFields,sharedText);
        Object[] stringPlans=new Object[10];Arrays.fill(stringPlans,string);Object stringsPlan=record(stringPlans);
        Node stringsNode=ctor(e,stringFields);Object stringsInput=freeze(e,stringsNode,stringsPlan);
        check((Long)get(get(stringsInput,"cert"),"stringUnits")==600_000L);
        check((Long)get(get(stringsInput,"cert"),"payloadCost")==0L&&fields(stringsNode)[0]==fields(stringsNode)[9]);
        Object[] mixedPlans=new Object[9];mixedPlans[0]=stringsPlan;Arrays.fill(mixedPlans,1,9,string);Object mixedStringsPlan=record(mixedPlans);
        Node underStrings=ctor(e,mixedStrings(stringsInput,sharedText,28_575));
        Object underInput=freeze(e,underStrings,mixedStringsPlan);
        check((Long)get(get(underInput,"cert"),"stringUnits")==1_048_575L);
        Node atStrings=ctor(e,mixedStrings(stringsInput,sharedText,28_576));Object atStringsInput=freeze(e,atStrings,mixedStringsPlan);
        check((Long)get(get(atStringsInput,"cert"),"stringUnits")==1_048_576L);
        check(e.constructDataArguments(new DataCtor[0],new Object[]{atStringsInput})[0]==atStrings);
        refuseWithoutAllocation(e,()->ctor(e,mixedStrings(stringsInput,sharedText,28_577)));
        Object[] twice600k=new Object[11];twice600k[0]=stringsInput;Arrays.fill(twice600k,1,11,sharedText);
        refuseWithoutAllocation(e,()->ctor(e,twice600k));
        // Reusing exactly the same capability still counts every logical String occurrence.
        refuseWithoutAllocation(e,()->e.constructDataArguments(new DataCtor[0],new Object[]{stringsInput,stringsInput}));
        Node cachedStringDiamond=ctor(e,0L,0L);Arrays.fill(fields(cachedStringDiamond),stringsNode);
        refuseWithoutAllocation(e,()->freeze(e,cachedStringDiamond,record(stringsPlan,stringsPlan)));
        check(rc(cachedStringDiamond)==1&&get(cachedStringDiamond,"frozen")==null);
        Object[] repeatedTextPlans=new Object[18];Arrays.fill(repeatedTextPlans,string);Object repeatedTextPlan=record(repeatedTextPlans);
        Object[] placeholders=new Object[18];Arrays.fill(placeholders,0L);Node repeatedText=ctor(e,placeholders);Arrays.fill(fields(repeatedText),sharedText);
        refuseWithoutAllocation(e,()->freeze(e,repeatedText,repeatedTextPlan));
        check(rc(repeatedText)==1&&get(repeatedText,"frozen")==null);
        Object[] independentBudgets=e.constructDataArguments(new DataCtor[]{DataCtor.bytes(new byte[1_048_576]),
                new DataCtor(0,new Object[]{new DataRef(0),stringsInput})},new Object[]{new DataRef(1)});
        Node independent=(Node)independentBudgets[0];Object independentInput=freeze(e,independent,record(bytes,stringsPlan));
        check((Long)get(get(independentInput,"cert"),"payloadCost")==1_048_576L
                &&(Long)get(get(independentInput,"cert"),"stringUnits")==600_000L);
        // Deep bounded traversal uses an explicit stack, with no expanded descendant sets.
        Node deep=ctor(e,1L);Object deepPlan=record(nat);
        for(int i=0;i<1000;i++) { Node next=ctor(e,0L);fields(next)[0]=deep;deep=next;deepPlan=record(deepPlan); }
        freeze(e,deep,deepPlan);check(rc(deep)==0);
        // Combined fresh/certified input depth is checked before guest allocation.
        Object certifiedLeaf=freeze(e,1L,nat);
        Node atBound=(Node)e.constructDataArguments(chain(1023,certifiedLeaf),new Object[]{new DataRef(1022)})[0];
        Object atBoundPlan=nat;for(int i=0;i<1023;i++) atBoundPlan=record(atBoundPlan);
        Object atBoundInput=freeze(e,atBound,atBoundPlan);
        check((Integer)get(get(atBoundInput,"cert"),"depth")==1024);
        check(e.constructDataArguments(new DataCtor[0],new Object[]{atBoundInput})[0]==atBound);
        refuseWithoutAllocation(e,()->e.constructDataArguments(chain(1024,certifiedLeaf),new Object[]{new DataRef(1023)}));
        refuseWithoutAllocation(e,()->e.constructDataArguments(chain(1,atBoundInput),new Object[]{new DataRef(0)}));
        refuseWithoutAllocation(e,()->e.constructDataArguments(chain(1024,1L),new Object[]{new DataRef(1023),certifiedLeaf}));
        Node legacyDeep=(Node)e.constructDataArguments(chain(1024,1L),new Object[]{new DataRef(1023)})[0];
        check(rc(legacyDeep)==1);release(e,legacyDeep);
        // Shared frozen child has no fresh owner count; DataRef still requires exactly one.
        Object[] mixed=e.constructDataArguments(new DataCtor[]{new DataCtor(0,new Object[]{byteInput}),new DataCtor(0,new Object[]{new DataRef(0),cert})},new Object[]{new DataRef(1)});
        Node outer=(Node)mixed[0],fresh=(Node)fields(outer)[0];check(rc(outer)==1&&rc(fresh)==1&&fields(fresh)[0]==buffer);
        refuse(()->e.constructDataArguments(new DataCtor[]{new DataCtor(0,new Object[]{cert})},new Object[]{new DataRef(0),new DataRef(0)}));
        release(e,outer);check((Boolean)get(outer,"dead")&&(Boolean)get(fresh,"dead")&&!(Boolean)get(n,"dead"));
        refuse(()->e.constructDataArguments(new DataCtor[0],new Object[]{n}));
        Interpreter.Fork fork=e.eagerFork(new Object[]{n,array,buffer,invalid});
        check(fork.roots[0]==n&&fork.roots[1]==array&&fork.roots[2]==buffer&&fork.roots[3]!=invalid);
        check(get(fork.roots[3],"frozen")==null);fork.engine.close();
        // IO success freezes only payload. Ordinary positive envelope releases once.
        Node io=ctor(e,cert);Object payload=fields(io)[0];check(payload==n&&rc(io)==1);
        freeze(e,payload,row);release(e,io);check((Boolean)get(io,"dead")&&fields(io)[0]==null&&!(Boolean)get(n,"dead"));
        Node interrupted=ctor(e,1L);Thread.currentThread().interrupt();
        try { refuse(()->freeze(e,interrupted,record(nat))); } finally { Thread.interrupted(); }
        check(rc(interrupted)==1&&get(interrupted,"frozen")==null);
        // Compact DAG doubles logical occurrences; saturation refuses without an exponential walk/partial commit.
        Node diamond=ctor(e,1L);Object diamondPlan=record(nat);List<Node> diamondNodes=new ArrayList<>();diamondNodes.add(diamond);
        for(int i=0;i<17;i++) { Node next=ctor(e,0L,0L);fields(next)[0]=diamond;fields(next)[1]=diamond;diamond=next;diamondPlan=record(diamondPlan,diamondPlan);diamondNodes.add(diamond); }
        Node diamondRoot=diamond;Object diamondType=diamondPlan;refuse(()->freeze(e,diamondRoot,diamondType));
        for(Node item:diamondNodes) check(get(item,"frozen")==null&&rc(item)==1);
        // Two independent confined engines import the published graph concurrently and close.
        AtomicReference<Throwable> failure=new AtomicReference<>();List<Thread> threads=new ArrayList<>();
        for(int i=0;i<2;i++) { Thread thread=new Thread(()->{ try(Interpreter other=engine()) {
            for(int j=0;j<100;j++) {
                Object imported=other.constructDataArguments(new DataCtor[0],new Object[]{cert,arrayInput,byteInput})[0];
                if(imported!=n||rc(n)!=0||fields(n)!=original) throw new AssertionError("Shared import changed storage");
            }
        } catch(Throwable problem) { failure.set(problem); } });threads.add(thread);thread.start(); }
        for(Thread thread:threads) thread.join();if(failure.get()!=null) throw new AssertionError(failure.get());
        // Simulate an existing retained global slot; close drops it without touching frozen payload.
        globalEngine.close();check(rc(n)==0&&fields(n)==original);
        e.close();check(fields(n)==original&&fields(n)[1].equals("text")&&scalars(buffer)==backing);
        System.out.println("FrozenStorageChecks: "+checks+" checks passed");
    }
}
