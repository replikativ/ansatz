import ansatz.lean.jvm.internal.exec.Interpreter;
import ansatz.lean.jvm.internal.exec.Interpreter.Node;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/** Synthetic IR exercises actual runtime ports, not source admission evidence. */
public final class StringSearchChecks {
    private static int checks;
    private static void check(boolean ok) { checks++; if(!ok) throw new AssertionError("check "+checks); }
    private static Object name(String value) { return List.of("str",List.of("anonymous"),value); }
    private static Map<String,Object> variable(int i) { return Map.of("idx",i); }
    private static Object arg(int i) { return Map.of("var",Map.of("id",variable(i))); }
    private static Object param(int i,String type) { return Map.of("x",variable(i),"ty",type,"borrow",false); }
    private static Object ret(int i) { return List.of("ret",arg(i)); }
    private static Object decl(int i,String type,Object expr,Object next) { return List.of("vdecl",variable(i),type,expr,next); }
    private static Object unbox(int i) { return Map.of("unbox",Map.of("x",variable(i))); }
    private static Object call(String target,Object... args) { return Map.of("fap",Map.of("c",name(target),"ys",List.of(args))); }
    private static Object literal(long value) { return Map.of("lit",Map.of("v",Map.of("num",Map.of("v",value)))); }
    private static Object dec(int i,Object next) { return List.of("dec",variable(i),1,false,false,next); }
    private static Map<String,Object> row(String label,String result,List<?> params,Object body) {
        return Map.of("kind","decl","name",name(label),"ir",Map.of("fdecl",
            Map.of("f",name(label),"type",result,"xs",params,"body",body)));
    }
    private static Map<String,Object> external(String label,String symbol,String result,String... types) {
        List<Object> params=new ArrayList<>(); for(int i=0;i<types.length;i++) params.add(param(i+1,types[i]));
        return Map.of("kind","decl","name",name(label),"ir",Map.of("extern",
            Map.of("f",name(label),"type",result,"xs",params,"ext",Map.of("entries",
                List.of(Map.of("standard",Map.of("backend",name("all"),"fn",symbol)))))));
    }
    private static Interpreter.Program program() {
        List<Object> rows=new ArrayList<>();
        rows.add(external("any","lean_string_any","uint8","object","object"));
        rows.add(external("prefix","lean_string_isprefixof","uint8","object","object"));
        for(String type:new String[]{"tagged","tobject"})
            rows.add(Map.of("kind","decl","name",name("length_"+type),"ir",Map.of("extern",
                Map.of("f",name("length_"+type),"type",type,
                    "xs",List.of(Map.of("x",variable(1),"ty","object","borrow",true)),
                    "ext",Map.of("entries",List.of(Map.of("standard",
                        Map.of("backend",name("all"),"fn","lean_string_length"))))))));
        rows.add(external("eq","lean_uint32_dec_eq","uint8","uint32","uint32"));
        // Capture marker owns a tracked constructor. AP copies its captured
        // owner for each invocation; this DEC balances exactly that copy.
        rows.add(row("predicate","uint8",List.of(param(1,"object"),param(2,"object"),param(3,"object")),
            dec(1,decl(4,"uint32",unbox(2),decl(5,"uint32",unbox(3),
                decl(6,"uint8",call("eq",arg(4),arg(5)),ret(6)))))));
        rows.add(row("make","object",List.of(param(1,"object"),param(2,"object")),
            decl(3,"object",Map.of("pap",Map.of("c",name("predicate"),"ys",List.of(arg(1),arg(2)))),ret(3))));
        rows.add(row("wrapped","uint8",List.of(param(1,"object"),param(2,"object")),
            decl(3,"uint8",call("any",arg(1),arg(2)),ret(3))));
        rows.add(row("applied","object",List.of(param(1,"object"),param(2,"object")),
            decl(3,"object",Map.of("pap",Map.of("c",name("any"),"ys",List.of(arg(1)))),
                decl(4,"object",Map.of("ap",Map.of("x",variable(3),"ys",List.of(arg(2)))),ret(4)))));
        rows.add(row("makeAny","object",List.of(param(1,"object")),
            decl(2,"object",Map.of("pap",Map.of("c",name("any"),"ys",List.of(arg(1)))),ret(2))));
        rows.add(row("applyOuter","object",List.of(param(1,"object"),param(2,"object")),
            decl(3,"object",Map.of("ap",Map.of("x",variable(1),"ys",List.of(arg(2)))),ret(3))));
        rows.add(row("bad","uint8",List.of(param(1,"object")),decl(2,"uint8",literal(2),ret(2))));
        rows.add(row("makeBad","object",List.of(),decl(1,"object",Map.of("pap",Map.of("c",name("bad"),"ys",List.of())),ret(1))));
        // A true result must short-circuit before the following NUL or Unicode
        // scalar; invalid Bool makes any extra invocation observable.
        rows.add(row("firstOnly","uint8",List.of(param(1,"object")),
            decl(2,"uint32",unbox(1),List.of("case",name("UInt32"),variable(2),"uint32",
                List.of(List.of("alt",Map.of("cidx",65),decl(3,"uint8",literal(1),ret(3))),
                        List.of("default",decl(4,"uint8",literal(2),ret(4))))))));
        rows.add(row("makeFirst","object",List.of(),decl(1,"object",Map.of("pap",Map.of("c",name("firstOnly"),"ys",List.of())),ret(1))));
        return Interpreter.prepare(rows);
    }
    private static Node marker() throws Exception {
        Constructor<Node> constructor=Node.class.getDeclaredConstructor(int.class,int.class,int.class);
        constructor.setAccessible(true); return constructor.newInstance(0,0,0);
    }
    private static boolean dead(Node node) throws Exception {
        Field field=Node.class.getDeclaredField("dead"); field.setAccessible(true); return field.getBoolean(node);
    }
    private static Node predicate(Interpreter e,Interpreter.Program p,Node marker,long wanted) {
        return (Node)e.invoke(p.functionId("make"),new Object[]{marker,wanted});
    }
    private static Object complete(Interpreter e) {
        while(e.phase().equals("running")) e.advance(1);
        check(e.phase().equals("complete")); return e.takeResult();
    }
    private static void invalidApplicationPreservesOwners(Interpreter.Program p,boolean explicit,boolean malformed,boolean shared) throws Exception {
        Interpreter e=new Interpreter(p,explicit); Node marker=marker();
        Node predicate=predicate(e,p,marker,65L);
        String input=malformed?"\ud800":"valid";
        Node outer=(Node)e.invoke(p.functionId("makeAny"),new Object[]{input});
        if(shared) e.inc(outer,1);
        Object[] outerFields=outer.fields.clone(),predicateFields=predicate.fields.clone();
        int outerRC=outer.rc,predicateRC=predicate.rc,markerRC=marker.rc;
        long retains=e.retains,releases=e.releases,deletes=e.shellDeletes;
        try {
            e.invoke(p.functionId("applyOuter"),new Object[]{outer,malformed?predicate:marker});
            throw new AssertionError("Invalid String.any application accepted");
        } catch(RuntimeException expected) {
            check(expected.getMessage().contains(malformed?"Invalid Unicode String":"Expected closure"));
        }
        check(outer.rc==outerRC&&predicate.rc==predicateRC&&marker.rc==markerRC);
        check(!dead(outer)&&!dead(predicate)&&!dead(marker));
        check(java.util.Arrays.equals(outerFields,outer.fields)&&java.util.Arrays.equals(predicateFields,predicate.fields));
        check(outer.fields[0]==input&&predicate.fields[0]==marker);
        check(e.retains==retains&&e.releases==releases&&e.shellDeletes==deletes);
        // The failed engine remains terminal; these assertions inspect the
        // original owned packet and do not invent a post-failure DEC path.
    }
    public static void main(String[] ignored) throws Exception {
        Interpreter.Program p=program();
        for(boolean explicit:new boolean[]{false,true}) {
            for(String type:new String[]{"tagged","tobject"}) {
                try(Interpreter length=new Interpreter(p,explicit)) {
                    check(length.invoke(p.functionId("length_"+type),new Object[]{"λ😀\u0000z"}).equals(4L));
                    check(length.invoke(p.functionId("length_"+type),new Object[]{""}).equals(0L));
                }
            }
            for(boolean malformed:new boolean[]{false,true}) for(boolean shared:new boolean[]{false,true})
                invalidApplicationPreservesOwners(p,explicit,malformed,shared);
            for(String entry:new String[]{"any","wrapped","applied"}) {
                for(Object[] sample:new Object[][]{{"",65L,0L},{"λ😀\u0000z",0L,1L},
                        {"λ😀\u0000z",0x1f600L,1L},{"λ😀\u0000z",65L,0L},{"A\u0000😀",65L,1L}}) {
                    Interpreter e=new Interpreter(p,explicit); Node marker=marker();
                    Node predicate=predicate(e,p,marker,(Long)sample[1]);
                    check(e.invoke(p.functionId(entry),new Object[]{sample[0],predicate}).equals(sample[2]));
                    check(dead(predicate)&&dead(marker)); e.close();
                }
            }
            Interpreter e=new Interpreter(p,explicit);
            for(Object[] sample:new Object[][]{{"","abc",1L},{"λ😀\u0000","λ😀\u0000tail",1L},
                    {"λ😀x","λ😀\u0000tail",0L},{"abcd","abc",0L},{"abc","abc",1L},{"x","abc",0L}})
                check(e.invoke(p.functionId("prefix"),new Object[]{sample[0],sample[1]}).equals(sample[2]));
            Node first=(Node)e.invoke(p.functionId("makeFirst"),new Object[0]);
            int firstRC=first.rc; // a zero-capture PAP may retain an engine cache owner
            check(e.invoke(p.functionId("any"),new Object[]{"A\u0000😀",first}).equals(1L));
            check(first.rc==(firstRC==0?0:firstRC-1)); e.close();
            Interpreter invalid=new Interpreter(p,explicit);
            Node bad=(Node)invalid.invoke(p.functionId("makeBad"),new Object[0]);
            try { invalid.invoke(p.functionId("any"),new Object[]{"x",bad}); throw new AssertionError("bad Bool accepted"); }
            catch(RuntimeException expected) { check(expected.getMessage().contains("canonical boxed Bool")); }
        }
        Interpreter parent=new Interpreter(p,true); Node marker=marker(); Node predicate=predicate(parent,p,marker,0x1f600L);
        parent.start(p.functionId("any"),new Object[]{"aλ😀z",predicate});
        parent.advance(1); // callback AP is now paused, original predicate retained
        check(parent.phase().equals("running")&&!dead(marker));
        Interpreter.Fork fork=parent.eagerFork(new Object[]{marker,predicate});
        check(complete(parent).equals(1L)); check(complete(fork.engine).equals(1L));
        check(dead(marker)&&dead(predicate));
        check(dead((Node)fork.roots[0])&&dead((Node)fork.roots[1])); parent.close(); fork.engine.close();
        Interpreter cancelled=new Interpreter(p,true); Node retainedMarker=marker();
        Node retainedPredicate=predicate(cancelled,p,retainedMarker,65L);
        cancelled.start(p.functionId("any"),new Object[]{"x".repeat(100),retainedPredicate});
        cancelled.advance(1); long before=cancelled.instructionCount();
        check(cancelled.phase().equals("running")&&before==1);
        try {
            Thread.currentThread().interrupt();
            try { while(cancelled.phase().equals("running")) cancelled.advance(1); throw new AssertionError("cancellation ignored"); }
            catch(Interpreter.RuntimeLimitException expected) { check(expected.code().equals("Cancelled")); }
        } finally { Thread.interrupted(); }
        check(cancelled.phase().equals("failed"));
        System.out.println("STRING_SEARCH_CHECKS "+checks);
    }
}
