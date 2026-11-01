import ansatz.research.ir.Interpreter;
import java.lang.reflect.*;
import java.math.BigInteger;
import java.util.Collections;

/** Source-local standalone regression; compile/run against the actual reviewed runtime. */
public final class RuntimeResourceChecks {
    static int checks;
    static void check(boolean value) { checks++; if(!value) throw new AssertionError("check "+checks); }
    static Object invoke(Interpreter engine,String name,Class<?>[] types,Object... values) throws Exception {
        Method m=Interpreter.class.getDeclaredMethod(name,types); m.setAccessible(true);
        try { return m.invoke(engine,values); }
        catch(InvocationTargetException e) { if(e.getCause() instanceof Exception) throw (Exception)e.getCause(); throw e; }
    }
    static void stringPrimitive(Interpreter e,int operation,Object left,Object right) throws Exception {
        Class<?> function=Class.forName("ansatz.research.ir.Interpreter$Function");
        Constructor<?> constructor=function.getDeclaredConstructor(String.class,int.class,int[].class,
            int[].class,int.class,int.class,Class.forName("ansatz.research.ir.Interpreter$HostExtern"),Object.class);
        constructor.setAccessible(true);
        Object f=constructor.newInstance("resource-check",-1,new int[0],new int[0],0,operation,null,null);
        invoke(e,"runtimeIntrinsic",new Class<?>[]{function,Object.class,Object.class,Object.class},f,left,right,0L);
    }
    static final Class<?>[] NATS={BigInteger.class,BigInteger.class};
    static final Class<?>[] TEXT={Object.class};
    static void limited(Checked action,String code) throws Exception {
        try { action.run(); throw new AssertionError("missing refusal"); }
        catch(Interpreter.RuntimeLimitException expected) { check(expected.code().equals(code)); }
    }
    interface Checked { void run() throws Exception; }
    static String repeated(int length) { return "x".repeat(length); }
    // A private-method model only: actual guest codecs must never admit this subclass.
    static final class InterruptOnMultiply extends BigInteger {
        int multiplies;
        InterruptOnMultiply() { super("2"); }
        @Override public BigInteger multiply(BigInteger other) {
            multiplies++; BigInteger answer=super.multiply(other);
            Thread.currentThread().interrupt(); return answer;
        }
    }
    public static void main(String[] args) throws Exception {
        Interpreter e=new Interpreter(Interpreter.prepare(Collections.emptyList()),true);
        BigInteger one=BigInteger.ONE,two=BigInteger.valueOf(2),maxExponent=one.shiftLeft(32).subtract(one);
        check(invoke(e,"natPow",NATS,BigInteger.ZERO,BigInteger.ZERO).equals(1L));
        check(invoke(e,"natPow",NATS,BigInteger.ZERO,maxExponent).equals(0L));
        check(invoke(e,"natPow",NATS,one,maxExponent).equals(1L));
        check(invoke(e,"natPow",NATS,two,BigInteger.valueOf(200)).equals(one.shiftLeft(200)));
        try { invoke(e,"natPow",NATS,one,one.shiftLeft(32)); throw new AssertionError(); }
        catch(RuntimeException expected) { check(expected.getMessage().contains("exponent is too big")); }
        limited(()->invoke(e,"natPow",NATS,two,maxExponent),"ResourceLimit");
        Method estimate=Interpreter.class.getDeclaredMethod("natMultiplyEstimate",long.class,long.class);
        estimate.setAccessible(true);
        check(estimate.invoke(null,1L<<20,1L<<20).equals(1L<<40));
        try { estimate.invoke(null,Long.MAX_VALUE,Long.MAX_VALUE); throw new AssertionError(); }
        catch(InvocationTargetException expected) { check(expected.getCause() instanceof Interpreter.RuntimeLimitException); }
        limited(()->invoke(e,"natMultiply",NATS,one.shiftLeft(1<<20),one.shiftLeft(1<<20)),"ResourceLimit");
        // A cooperative deadline or interrupt refuses before publishing the result slot.
        Field result=Interpreter.class.getDeclaredField("result"); result.setAccessible(true);
        Object sentinel=new Object(); result.set(e,sentinel);
        e.configureAtomicDeadlineAfterNanos(1);
        limited(()->invoke(e,"natPow",NATS,two,BigInteger.valueOf(400)),"ResourceLimit");
        check(result.get(e)==sentinel); e.clearAtomicDeadline();
        Thread.currentThread().interrupt();
        try { limited(()->invoke(e,"natPow",NATS,two,BigInteger.valueOf(400)),"Cancelled"); check(Thread.currentThread().isInterrupted()); }
        finally { Thread.interrupted(); }
        InterruptOnMultiply interruptedBase=new InterruptOnMultiply();
        try {
            limited(()->invoke(e,"natPow",NATS,interruptedBase,BigInteger.valueOf(4)),"Cancelled");
            check(interruptedBase.multiplies==1); check(Thread.currentThread().isInterrupted());
            check(result.get(e)==sentinel);
        } finally { Thread.interrupted(); }
        try { invoke(e,"utf8",TEXT,"\ud800"); throw new AssertionError(); }
        catch(RuntimeException expected) { check(expected.getMessage().contains("Unicode")); }
        check(((byte[])invoke(e,"utf8",TEXT,"\u0000λ😀")).length==7);
        int cap=16*1024*1024; String full=repeated(cap);
        stringPrimitive(e,19,full,""); check(((String)result.get(e)).length()==cap);
        limited(()->stringPrimitive(e,19,full,"x"),"ResourceLimit");
        limited(()->stringPrimitive(e,15,full,0x1f600L),"ResourceLimit");
        stringPrimitive(e,15,repeated(cap-4),0x1f600L);
        check(((String)result.get(e)).getBytes(java.nio.charset.StandardCharsets.UTF_8).length==cap);
        result.set(e,null);
        limited(()->invoke(e,"utf8",TEXT,full+"x"),"ResourceLimit");
        invoke(e,"appendCaptured",new Class<?>[]{Object.class,boolean.class},full,false);
        limited(()->invoke(e,"appendCaptured",new Class<?>[]{Object.class,boolean.class},"λ",false),"ResourceLimit");
        Interpreter child=e.eagerFork().engine;
        limited(()->invoke(child,"appendCaptured",new Class<?>[]{Object.class,boolean.class},"x",false),"ResourceLimit");
        String[] drained=e.drainCapturedOutput(); check(drained[0].equals(full)&&drained[1].isEmpty());
        invoke(e,"appendCaptured",new Class<?>[]{Object.class,boolean.class},"λ",false);
        check(e.drainCapturedOutput()[0].equals("λ")); check(drained[0].length()==cap);
        check(child.drainCapturedOutput()[0].length()==cap);
        check(e.drainCapturedOutput()[0].isEmpty());
        System.out.println("RuntimeResourceChecks checks="+checks);
    }
}
