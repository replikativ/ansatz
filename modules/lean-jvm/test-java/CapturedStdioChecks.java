import ansatz.lean.jvm.internal.exec.Interpreter;
import ansatz.lean.jvm.internal.exec.Interpreter.Node;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

/** Actual engine getter/closure/AP calls using synthetic IR. These checks are
 * not native-source or public-admission evidence. */
public final class CapturedStdioChecks {
    private static Object nodeMember(Interpreter.Node value,String name) {
        try { java.lang.reflect.Field field=Interpreter.Node.class.getDeclaredField(name);
            field.setAccessible(true); return field.get(value);
        } catch(ReflectiveOperationException failure) { throw new AssertionError(failure); }
    }
    private static Object[] nodeFields(Interpreter.Node value) { return (Object[])nodeMember(value,"fields"); }
    private static byte[] nodeScalars(Interpreter.Node value) { return (byte[])nodeMember(value,"scalars"); }
    private static int nodeTag(Interpreter.Node value) { return (Integer)nodeMember(value,"tag"); }
    private static int nodeRC(Interpreter.Node value) { return (Integer)nodeMember(value,"rc"); }

    private static int checks;
    private static void check(boolean value) { checks++; if(!value) throw new AssertionError("check "+checks); }
    private static List<Object> name(String n) { return List.of("str",List.of("anonymous"),n); }
    private static Map<String,Object> p(int i,String type) { return Map.of("x",Map.of("idx",i),"ty",type,"borrow",false); }
    private static Map<String,Object> a(int i) { return Map.of("var",Map.of("id",Map.of("idx",i))); }
    private static Map<String,Object> getter(String n,String symbol) {
        return Map.of("kind","decl","name",name(n),"ir",Map.of("extern",Map.of(
          "f",name(n),"type","object","xs",List.of(p(1,"void")),
          "ext",Map.of("entries",List.of(Map.of("standard",Map.of("backend",name("all"),"fn",symbol)))))));
    }
    private static Map<String,Object> apply(String n,boolean argument) {
        List<Object> xs=argument?List.of(p(1,"object"),p(2,"object")):List.of(p(1,"object"));
        List<Object> args=argument?List.of(a(2),"erased"):List.of("erased");
        return Map.of("kind","decl","name",name(n),"ir",Map.of("fdecl",Map.of(
          "f",name(n),"type","object","xs",xs,"body",List.of("vdecl",Map.of("idx",3),"object",
          Map.of("ap",Map.of("x",Map.of("idx",1),"ys",args)),List.of("ret",a(3))))));
    }
    private static final Interpreter.Program PROGRAM=Interpreter.prepare(List.of(
      getter("stdin","lean_get_stdin"),getter("stdout","lean_get_stdout"),getter("stderr","lean_get_stderr"),
      apply("apply0",false),apply("apply1",true)));
    private static Object privateCall(Interpreter e,String n,Class<?>[] types,Object... args) throws Exception {
        Method m=Interpreter.class.getDeclaredMethod(n,types); m.setAccessible(true); return m.invoke(e,args);
    }
    private static Node bytes(Interpreter e,byte[] data) throws Exception {
        Node n=(Node)privateCall(e,"newByteArray",new Class<?>[]{int.class,int.class},data.length,data.length);
        System.arraycopy(data,0,nodeScalars(n),0,data.length); return n;
    }
    private static Object usize(Interpreter e,long n) throws Exception {
        return privateCall(e,"boxScalar",new Class<?>[]{long.class,int.class},n,3);
    }
    private static Node stream(Interpreter e,String n) { return (Node)e.invoke(PROGRAM.functionId(n),new Object[]{0L}); }
    private static Object op(Interpreter e,Node stream,int slot,Object argument) {
        Node method=(Node)nodeFields(stream)[slot]; e.inc(method,1);
        return e.invoke(PROGRAM.functionId(argument==null?"apply0":"apply1"),
                argument==null?new Object[]{method}:new Object[]{method,argument});
    }
    private static String line(Interpreter e,Node stream) {
        Node result=(Node)op(e,stream,3,null); check(nodeTag(result)==0);
        String text=(String)nodeFields(result)[0]; e.dec(result,1); return text;
    }
    private static byte[] read(Interpreter e,Node stream,long count) throws Exception {
        Node result=(Node)op(e,stream,1,usize(e,count)); check(nodeTag(result)==0);
        Node data=(Node)nodeFields(result)[0]; byte[] out=Arrays.copyOf(nodeScalars(data),data.byteArraySize()); e.dec(result,1); return out;
    }
    private static void ok(Interpreter e,Object value) {
        Node result=(Node)value; check(nodeTag(result)==0&&nodeFields(result)[0].equals(0L)); e.dec(result,1);
    }
    private static void error(Interpreter e,Object value) {
        Node result=(Node)value; check(nodeTag(result)==1&&nodeTag(((Node)nodeFields(result)[0]))==18); e.dec(result,1);
    }
    private interface Attempt { void run() throws Exception; }
    private static void refuse(Attempt a) throws Exception {
        try { a.run(); throw new AssertionError("missing refusal"); } catch(RuntimeException expected) { checks++; }
    }
    public static void main(String[] args) throws Exception {
        for(boolean explicit:new boolean[]{false,true}) {
            Interpreter e=new Interpreter(PROGRAM,explicit);
            Node empty=stream(e,"stdin"); check(line(e,empty).isEmpty()); check(read(e,empty,0).length==0); e.dec(empty,1);
            byte[] input="a\u0000β\r\nb\nlast".getBytes(StandardCharsets.UTF_8);
            e.beginInvocation(input,1024,1024); input[0]='X';
            Node in=stream(e,"stdin"),out=stream(e,"stdout"),err=stream(e,"stderr");
            check(line(e,in).equals("a\u0000β\r\n")); check(line(e,in).equals("b\n"));
            check(Arrays.equals(read(e,in,2),new byte[]{'l','a'})); check(line(e,in).equals("st"));
            check(line(e,in).isEmpty()&&read(e,in,10).length==0);
            check(op(e,in,5,null).equals(0L));
            ok(e,op(e,out,4,"hello\u0000"));
            ok(e,op(e,out,2,bytes(e,new byte[]{(byte)0xce}))); ok(e,op(e,out,2,bytes(e,new byte[]{(byte)0xb2})));
            ok(e,op(e,err,2,bytes(e,new byte[]{(byte)0xc0,(byte)0x80,'!',(byte)0xff,(byte)0x80})));
            check(e.capturedStdout().equals("hello\u0000β")); check(e.capturedStderr().equals("�!�"));
            ok(e,op(e,out,0,null)); error(e,op(e,out,3,null)); error(e,op(e,in,4,"no"));
            Node wrongBytes=bytes(e,new byte[]{1}); error(e,op(e,in,2,wrongBytes)); check(nodeRC(wrongBytes)==0);
            byte[][] captured=e.drainCapturedBytes(); check(captured[0].length==8&&captured[1].length==5);
            captured[0][0]=0; check(e.capturedStdout().isEmpty());
            e.endInvocation(); error(e,op(e,in,3,null));
            e.beginInvocation("new\n".getBytes(StandardCharsets.UTF_8),5,5);
            error(e,op(e,in,3,null)); // escaped method never consumes new input
            Node next=stream(e,"stdin"); check(line(e,next).equals("new\n"));
            e.dec(next,1); e.endInvocation(); e.dec(in,1); e.dec(out,1); e.dec(err,1); e.close();
        }
        Interpreter e=new Interpreter(PROGRAM,true);
        e.beginInvocation(new byte[]{(byte)0xed,(byte)0xa0,(byte)0x80,10,'x'},16,16);
        Node in=stream(e,"stdin"); check(line(e,in).equals("�\n"));
        Interpreter.Fork fork=e.eagerFork(new Object[]{in}); Interpreter child=fork.engine; Node childIn=(Node)fork.roots[0];
        check(line(e,in).equals("x")); check(line(child,childIn).equals("x"));
        child.dec(childIn,1); child.endInvocation(); child.close(); e.dec(in,1); e.endInvocation(); e.close();
        // A pre-invocation GET_STDIN root must not be overwritten by the legacy installer.
        Interpreter configured=new Interpreter(PROGRAM,true);
        Node existing=stream(configured,"stdin"); configured.dec(existing,1);
        check(nodeRC(existing)==1);
        long retained=configured.retains,released=configured.releases;
        try {
            configured.installStdioDefaults(null,null);
            throw new AssertionError("missing configured-stdin refusal");
        } catch(IllegalArgumentException expected) {
            check(expected.getMessage().contains("Default stdin is already configured"));
        }
        check(nodeRC(existing)==1&&configured.retains==retained&&configured.releases==released);
        Node same=stream(configured,"stdin"); check(same==existing); configured.dec(same,1);
        configured.close(); check(nodeRC(existing)==0);
        Interpreter invalid=new Interpreter(PROGRAM,true);
        refuse(()->invalid.beginInvocation(new byte[1024*1024+1],1,1));
        refuse(()->invalid.beginInvocation(new byte[0],16*1024*1024+1,1));
        invalid.beginInvocation(new byte[0],1,1); refuse(()->invalid.beginInvocation(new byte[0],1,1));
        invalid.endInvocation(); refuse(invalid::endInvocation); invalid.close();
        Interpreter bounded=new Interpreter(PROGRAM,false); bounded.beginInvocation(new byte[0],1,1);
        Node out=stream(bounded,"stdout"); ok(bounded,op(bounded,out,4,"x"));
        refuse(()->op(bounded,out,4,"y")); check(bounded.capturedStdout().equals("x"));
        bounded.dec(out,1); bounded.close();
        Interpreter interrupted=new Interpreter(PROGRAM,true);
        Thread.currentThread().interrupt();
        try { refuse(()->interrupted.beginInvocation(new byte[0],1,1)); }
        finally { Thread.interrupted(); }
        interrupted.beginInvocation(new byte[0],1,1); interrupted.endInvocation(); interrupted.close();
        System.out.println("CAPTURED_STDIO_CHECKS "+checks);
    }
}
