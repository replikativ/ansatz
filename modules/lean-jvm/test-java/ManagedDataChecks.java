import ansatz.lean.jvm.internal.exec.Interpreter;
import ansatz.lean.jvm.internal.exec.Interpreter.DataCtor;
import ansatz.lean.jvm.internal.exec.Interpreter.DataRef;
import ansatz.lean.jvm.internal.exec.Interpreter.Node;
import java.lang.reflect.Field;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collections;

/** Standalone actual-runtime ownership checks. Reflection below only injects boundary states,
 * inspects custody, and does not construct guest Nodes or confer native type authority. */
public final class ManagedDataChecks {
    private static int checks;
    private static void check(boolean ok) { checks++; if(!ok) throw new AssertionError("check "+checks); }
    private static Field field(String name) throws Exception {
        Field f=Interpreter.class.getDeclaredField(name); f.setAccessible(true); return f;
    }
    private static Interpreter engine() { return new Interpreter(Interpreter.prepare(Collections.emptyList()),true); }
    private static DataCtor ctor(int tag,Object... fields) { return new DataCtor(tag,fields); }
    private static DataRef ref(int index) { return new DataRef(index); }
    private interface Attempt { void run() throws Exception; }
    private static void refuse(Interpreter e,Attempt attempt) throws Exception {
        long a=e.allocations,r=e.retains,d=e.releases,s=e.stores;
        Object program=field("program").get(e),constants=field("constants").get(e);
        Object ready=field("constantReady").get(e),source=field("preparedModuleSource").get(e);
        Object installed=field("graphInstalled").get(e),module=field("moduleGraphInstalled").get(e);
        try { attempt.run(); throw new AssertionError("missing refusal"); }
        catch(IllegalArgumentException|IllegalStateException|ArithmeticException expected) { checks++; }
        check(e.allocations==a&&e.retains==r&&e.releases==d&&e.stores==s);
        check(field("program").get(e)==program&&field("constants").get(e)==constants&&field("constantReady").get(e)==ready);
        check(field("preparedModuleSource").get(e)==source&&field("graphInstalled").get(e).equals(installed)
                &&field("moduleGraphInstalled").get(e).equals(module));
    }
    private static void release(Interpreter e,Object root) {
        e.startRelease(root,1); while(!e.advance(1000)) {} check(e.takeResult().equals(0L));
    }
    private static boolean dead(Node node) throws Exception {
        Field f=Node.class.getDeclaredField("dead"); f.setAccessible(true); return f.getBoolean(node);
    }
    private static final class MutableInteger extends BigInteger {
        MutableInteger() { super("1"); }
        @Override public int bitLength() { throw new AssertionError("mutable subclass inspected"); }
    }
    public static void main(String[] args) throws Exception {
        Interpreter e=engine();
        Object[] roots=e.constructDataArguments(new DataCtor[0],new Object[]{0L,1L,"λ😀\u0000",BigInteger.ONE.shiftLeft(80)});
        check(roots.length==4&&roots[0].equals(0L)&&roots[2].equals("λ😀\u0000")&&e.allocations==0);
        Object[] callerFields={7L,0L}; Object[] callerRoots={ref(1)};
        DataCtor[] recipes={new DataCtor(1,callerFields),ctor(0,ref(0),"tail")};
        roots=e.constructDataArguments(recipes,callerRoots);
        Node outer=(Node)roots[0],inner=(Node)outer.fields[0];
        check(outer.rc==1&&inner.rc==1&&outer.tag==0&&inner.tag==1&&e.allocations==2);
        check(outer.scalars.length==0&&inner.scalars.length==0&&inner.fields!=callerFields&&roots!=callerRoots);
        callerFields[0]=99L; callerRoots[0]=0L; recipes[0]=null;
        check(inner.fields[0].equals(7L)&&outer.fields[1].equals("tail"));
        refuse(e,()->e.constructDataArguments(new DataCtor[0],new Object[]{outer}));
        check(outer.rc==1&&inner.rc==1&&!dead(inner));
        release(e,outer); check(dead(outer)&&dead(inner));
        refuse(e,()->e.constructDataArguments(null,new Object[0]));
        refuse(e,()->e.constructDataArguments(new DataCtor[0],null));
        refuse(e,()->e.constructDataArguments(new DataCtor[]{null},new Object[]{ref(0)}));
        refuse(e,()->e.constructDataArguments(new DataCtor[]{ctor(-1,0L)},new Object[]{ref(0)}));
        refuse(e,()->e.constructDataArguments(new DataCtor[]{ctor(244,0L)},new Object[]{ref(0)}));
        refuse(e,()->e.constructDataArguments(new DataCtor[]{ctor(0)},new Object[]{ref(0)}));
        refuse(e,()->e.constructDataArguments(new DataCtor[]{new DataCtor(0,null)},new Object[]{ref(0)}));
        refuse(e,()->e.constructDataArguments(new DataCtor[]{ctor(0,ref(0))},new Object[]{ref(0)}));
        refuse(e,()->e.constructDataArguments(new DataCtor[]{ctor(0,ref(1)),ctor(1,0L)},new Object[]{ref(0)}));
        refuse(e,()->e.constructDataArguments(new DataCtor[0],new Object[]{ref(-1)}));
        refuse(e,()->e.constructDataArguments(new DataCtor[0],new Object[]{ref(0)}));
        refuse(e,()->e.constructDataArguments(new DataCtor[]{ctor(0,0L)},new Object[0]));
        refuse(e,()->e.constructDataArguments(new DataCtor[]{ctor(0,0L)},new Object[]{ref(0),ref(0)}));
        refuse(e,()->e.constructDataArguments(new DataCtor[]{ctor(0,0L),ctor(0,ref(0),ref(0))},new Object[]{ref(1)}));
        for(Object invalid:new Object[]{null,Integer.valueOf(1),Boolean.TRUE,new Object(),new MutableInteger(),new Object[0],"\ud800","\udc00"}) {
            refuse(e,()->e.constructDataArguments(new DataCtor[0],new Object[]{invalid}));
        }
        refuse(e,()->e.constructDataArguments(new DataCtor[0],new Object[]{BigInteger.ONE.shiftLeft(4096)}));
        refuse(e,()->e.constructDataArguments(new DataCtor[0],new Object[]{BigInteger.ONE.shiftLeft(4096).negate()}));
        refuse(e,()->e.constructDataArguments(new DataCtor[0],new Object[]{"x".repeat(65537)}));
        Object[] texts=new Object[17]; Arrays.fill(texts,"x".repeat(65536));
        refuse(e,()->e.constructDataArguments(new DataCtor[0],texts));
        Object[] integers=new Object[1025]; Arrays.fill(integers,BigInteger.ONE.shiftLeft(4095));
        refuse(e,()->e.constructDataArguments(new DataCtor[0],integers));
        Object[] tooMany=new Object[100001]; Arrays.fill(tooMany,0L);
        refuse(e,()->e.constructDataArguments(new DataCtor[0],tooMany));
        Object[] full=new Object[100000]; Arrays.fill(full,0L);
        refuse(e,()->e.constructDataArguments(new DataCtor[]{new DataCtor(0,full)},new Object[]{ref(0)}));
        Object[] exact=new Object[100000]; Arrays.fill(exact,"");
        check(e.constructDataArguments(new DataCtor[0],exact).length==100000);
        e.allocations=Long.MAX_VALUE;
        refuse(e,()->e.constructDataArguments(new DataCtor[]{ctor(0,0L)},new Object[]{ref(0)}));
        e.allocations=2;
        for(String name:new String[]{"pendingOwnedResult","advancing","disposed","untrackedFailure","initializerFailed","releaseRoot"}) {
            field(name).setBoolean(e,true);
            refuse(e,()->e.constructDataArguments(new DataCtor[0],new Object[]{0L}));
            field(name).setBoolean(e,false);
        }
        field("phase").setInt(e,1);
        refuse(e,()->e.constructDataArguments(new DataCtor[0],new Object[]{0L})); field("phase").setInt(e,0);
        Interpreter synchronous=new Interpreter(Interpreter.prepare(Collections.emptyList()));
        refuse(synchronous,()->synchronous.constructDataArguments(new DataCtor[0],new Object[]{0L})); synchronous.close();
        Interpreter tasked=new Interpreter(Interpreter.prepare(Collections.emptyList()),true,false,null,Interpreter.TaskRuntime.logicalSynchronous());
        refuse(tasked,()->tasked.constructDataArguments(new DataCtor[0],new Object[]{0L}));
        tasked.startDispose(); while(!tasked.advance(1000)) {} check(tasked.takeResult().equals(0L)); tasked.close();
        int count=2000; DataCtor[] chain=new DataCtor[count];
        chain[0]=ctor(1,0L,0L);
        for(int i=1;i<count;i++) chain[i]=ctor(1,(long)i,ref(i-1));
        roots=e.constructDataArguments(chain,new Object[]{ref(count-1)});
        Node last=(Node)roots[0],first=last;
        for(int i=1;i<count;i++) first=(Node)first.fields[1];
        check(e.allocations==2002&&last.rc==1&&first.rc==1);
        release(e,last); check(dead(last)&&dead(first));
        e.close(); refuse(e,()->e.constructDataArguments(new DataCtor[0],new Object[]{0L}));
        System.out.println("ManagedDataChecks checks="+checks);
    }
}
