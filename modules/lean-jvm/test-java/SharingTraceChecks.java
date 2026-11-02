import ansatz.lean.jvm.internal.exec.Interpreter;
import ansatz.lean.jvm.internal.exec.Interpreter.Node;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;

/** Actual engine operations; synthetic IR exercises both invocation drivers.
 * Reflection injects output budget/MT boundary states, never admission evidence. */
public final class SharingTraceChecks {
    private static int checks;
    private static void check(boolean value) { checks++; if(!value) throw new AssertionError("check "+checks); }
    private static List<Object> name(String name) { return List.of("str",List.of("anonymous"),name); }
    private static Map<String,Object> param(int i,String ty,boolean borrow) {
        return Map.of("x",Map.of("idx",i),"ty",ty,"borrow",borrow);
    }
    private static Map<String,Object> arg(int i) { return Map.of("var",Map.of("id",Map.of("idx",i))); }
    private static Map<String,Object> traceRow() {
        return Map.of("kind","decl","name",name("trace"),"ir",Map.of("extern",
          Map.of("f",name("trace"),"type","tobject","xs",List.of(param(1,"erased",false),param(2,"object",true),param(3,"tobject",false)),
            "ext",Map.of("entries",List.of(Map.of("standard",Map.of("backend",name("all"),"fn","lean_dbg_trace_if_shared")))))));
    }
    private static Map<String,Object> wrapper() {
        return Map.of("kind","decl","name",name("wrapped"),"ir",Map.of("fdecl",
          Map.of("f",name("wrapped"),"type","tobject","xs",List.of(param(1,"object",true),param(2,"tobject",false)),
            "body",List.of("vdecl",Map.of("idx",3),"tobject",Map.of("fap",Map.of("c",name("trace"),"ys",List.of("erased",arg(1),arg(2)))),
                         List.of("ret",arg(3))))));
    }
    private static Map<String,Object> freshRow() {
        return Map.of("kind","decl","name",name("fresh"),"ir",Map.of("fdecl",
          Map.of("f",name("fresh"),"type","object","xs",List.of(param(1,"tobject",false)),
            "body",List.of("vdecl",Map.of("idx",2),"object",Map.of("ctor",Map.of(
              "i",Map.of("cidx",0,"size",1,"usize",0,"ssize",0,"name",name("Fixture")),"ys",List.of(arg(1)))),
              List.of("ret",arg(2))))));
    }
    private static Map<String,Object> appliedRow() {
        return Map.of("kind","decl","name",name("applied"),"ir",Map.of("fdecl",
          Map.of("f",name("applied"),"type","tobject","xs",List.of(param(1,"object",true),param(2,"tobject",false)),
            "body",List.of("vdecl",Map.of("idx",3),"object",
              Map.of("pap",Map.of("c",name("trace"),"ys",List.of("erased",arg(1)))),
              List.of("vdecl",Map.of("idx",4),"tobject",
                Map.of("ap",Map.of("x",Map.of("idx",3),"ys",List.of(arg(2)))),List.of("ret",arg(4)))))));
    }
    private interface Attempt { void run(); }
    private static void refuse(Attempt attempt) {
        try { attempt.run(); throw new AssertionError("missing refusal"); }
        catch(RuntimeException expected) { checks++; }
    }
    private static Field field(String name) throws Exception {
        Field f=Interpreter.class.getDeclaredField(name); f.setAccessible(true); return f;
    }
    private static Node fresh(Interpreter e) {
        return (Node)e.invoke(2,new Object[]{2L});
    }
    public static void main(String[] args) throws Exception {
        Interpreter.Program p=Interpreter.prepare(List.of(traceRow(),wrapper(),freshRow(),appliedRow()));
        int trace=p.functionId("trace"),wrapped=p.functionId("wrapped");
        for(boolean explicit:new boolean[]{false,true}) {
            Interpreter e=new Interpreter(p,explicit);
            Node value=fresh(e);
            long retains=e.retains,releases=e.releases;
            check(e.invoke(trace,new Object[]{0L,"array",value})==value);
            check(value.rc==1&&e.retains==retains&&e.releases==releases);
            check(e.drainCapturedOutput()[1].isEmpty());
            e.inc(value,1);
            check(e.invoke(trace,new Object[]{0L,"λ😀\u0000ignored",value})==value);
            check(e.drainCapturedOutput()[1].equals("shared RC λ😀\n"));
            check(value.rc==2&&e.releases==releases);
            check(e.invoke(wrapped,new Object[]{"via IR",value})==value);
            check(e.drainCapturedOutput()[1].equals("shared RC via IR\n"));
            check(e.invoke(trace,new Object[]{0L,"scalar",7L}).equals(7L));
            check(e.drainCapturedOutput()[1].isEmpty());
            if(explicit) {
                refuse(()->e.invoke(trace,new Object[]{1L,"bad",value}));
                refuse(()->e.invoke(trace,new Object[]{0L,"bad","untracked"}));
                refuse(()->e.invoke(trace,new Object[]{0L,"bad",BigInteger.ONE.shiftLeft(80)}));
                refuse(()->e.invoke(trace,new Object[]{0L,"\ud800",value}));
                check(value.rc==2&&e.drainCapturedOutput()[1].isEmpty());
            }
            e.dec(value,1); // unique again
            Method mt=Interpreter.class.getDeclaredMethod("markLogicalMT",Object.class); mt.setAccessible(true); mt.invoke(e,value);
            check(e.invoke(trace,new Object[]{0L,"MT",value})==value);
            check(e.drainCapturedOutput()[1].equals("shared RC MT\n"));
            value.rc=0; // persistent fixture boundary
            check(e.invoke(trace,new Object[]{0L,"persistent",value})==value);
            check(e.drainCapturedOutput()[1].equals("shared RC persistent\n"));
            e.close();
        }
        Interpreter e=new Interpreter(p,true); Node shared=fresh(e); e.inc(shared,1);
        field("stderrOutputBytes").setInt(e,16*1024*1024-12);
        check(e.invoke(trace,new Object[]{0L,"x",shared})==shared);
        check(e.drainCapturedOutput()[1].equals("shared RC x\n"));
        field("stderrOutputBytes").setInt(e,16*1024*1024-11);
        refuse(()->e.invoke(trace,new Object[]{0L,"x",shared}));
        check(e.capturedStderr().isEmpty()&&shared.rc==2);
        e.close();
        // Each failure has its own stopped, resource-free fixture engine. Check
        // both drivers and direct/FAP/PAP+AP paths: no unsupported leaf becomes
        // an invented RC observation, diagnostic, or owning result.
        for(boolean explicit:new boolean[]{false,true}) {
            for(String entry:new String[]{"trace","wrapped","applied"}) {
                for(Object leaf:new Object[]{"untracked",BigInteger.ONE.shiftLeft(80)}) {
                    Interpreter failed=new Interpreter(p,explicit);
                    long beforeRetains=failed.retains,beforeReleases=failed.releases;
                    Object[] arguments=entry.equals("trace")?new Object[]{0L,"leaf",leaf}:new Object[]{"leaf",leaf};
                    try {
                        failed.invoke(p.functionId(entry),arguments);
                        throw new AssertionError("missing leaf refusal");
                    } catch(RuntimeException expected) {
                        check(expected.getMessage().contains("heap-leaf ownership is unavailable"));
                    }
                    check(failed.capturedStderr().isEmpty());
                    // PAP/AP owns a closure, so only the direct call has no
                    // surrounding interpreter retain/release work to perform.
                    if(entry.equals("trace")) check(failed.retains==beforeRetains&&failed.releases==beforeReleases);
                }
            }
        }
        System.out.println("SHARING_TRACE_CHECKS "+checks);
    }
}
