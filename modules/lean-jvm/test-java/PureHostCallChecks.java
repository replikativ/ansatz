package ansatz.lean.jvm;

import ansatz.lean.jvm.internal.exec.Interpreter;
import java.lang.reflect.Method;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CancellationException;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;

/** Synthetic original-IR calls exercise the private adapter, not native import
 * admission. No source/producer manifest authority is inferred from this test. */
public final class PureHostCallChecks {
    private static int checks;
    private static void check(boolean ok) {
        checks++;
        if (!ok) throw new AssertionError("Pure host check " + checks);
    }
    private static LeanType packet() throws Exception {
        Method method = PublicDatatypeChecks.class.getDeclaredMethod("fixture");
        method.setAccessible(true);
        return ((LeanType.Registry) method.invoke(null)).roots.get(0);
    }
    private static LeanType field(LeanType packet, int index) {
        return packet.constructors().get(0).fields().get(index).type();
    }
    private static LeanType scalar(boolean floating) throws Exception {
        Map<String,Object> type = floating ? Map.of("kind", "float", "bits", 64)
            : Map.of("kind", "machine-int", "bits", 64, "signed", false);
        String lane = floating ? "float" : "uint64";
        Map<String,Object> logical = Map.of("schema", "lean-jvm-type-graph/3", "roots", List.of(type), "definitions", List.of());
        Method digest = PublicDatatypeChecks.class.getDeclaredMethod("digest", Object.class); digest.setAccessible(true);
        Map<String,Object> normalized = Map.of("schema", "lean-jvm-typed-storage/1", "logicalDigest", digest.invoke(null, logical),
            "target", Map.of("wordBits", 64, "byteOrder", "little", "storageAbi", "node-pure-data/1"), "roots", List.of(0),
            "plans", List.of(Map.of("id", 0, "type", type, "closedIR", lane,
                "encoding", Map.of("kind", "scalar", "lane", lane, "boxed", "box64"))));
        return ValueBridge.compileTrusted(Interpreter.class, logical, normalized).roots.get(0);
    }
    private static List<Object> name(String text) { return List.of("str", List.of("anonymous"), text); }
    private static Interpreter engine(Interpreter.HostExtern descriptor) {
        ArrayList<Object> parameters = new ArrayList<>();
        String[] lanes = descriptor.paramTypes(); boolean[] borrowed = descriptor.borrowed();
        for (int i = 0; i < lanes.length; i++)
            parameters.add(Map.of("x", Map.of("idx", i + 1), "ty", lanes[i], "borrow", borrowed[i]));
        Map<String,Object> declaration = Map.of("f", name("host"), "type", descriptor.resultType(), "xs", parameters,
            "ext", Map.of("entries", List.of(Map.of("standard", Map.of("backend", name("all"), "fn", descriptor.symbol())))));
        return new Interpreter(Interpreter.prepare(List.of(Map.of("kind", "decl", "name", name("host"),
            "ir", Map.of("extern", declaration))), new Interpreter.HostExtern[]{descriptor}), true);
    }
    private static Interpreter.HostRequest start(Interpreter engine, Object... arguments) {
        engine.start(0, arguments);
        for (int i = 0; i < 100 && engine.pendingHostRequest() == null; i++) engine.advance(1);
        check(engine.pendingHostRequest() != null);
        return engine.pendingHostRequest();
    }
    private static Interpreter.HostExtern descriptor(String[] lanes, boolean[] borrowed, String result) {
        return new Interpreter.HostExtern("app_pure", lanes, borrowed, result);
    }
    private static Object arg(int id) { return Map.of("var", Map.of("id", Map.of("idx", id))); }
    private static Map<String,Object> definition(String label, Object body) {
        return Map.of("kind", "decl", "name", name(label), "ir", Map.of("fdecl", Map.of(
            "f", name(label), "type", "tobject", "xs", List.of(Map.of("x", Map.of("idx", 1), "ty", "tobject", "borrow", false)),
            "body", body)));
    }
    private static void originalDefinitions(LeanType nat) {
        Map<String,Object> fallback = definition("fallback", List.of("ret", arg(1)));
        Map<String,Object> caller = definition("caller", List.of("vdecl", Map.of("idx", 2), "tobject",
            Map.of("fap", Map.of("c", name("fallback"), "ys", List.of(arg(1)))), List.of("ret", arg(2))));
        Interpreter.SourceBinding source = new Interpreter.SourceBinding("synthetic-only");
        Interpreter.Header target = source.header(fallback, "a".repeat(64)), root = source.header(caller, "b".repeat(64));
        Interpreter.Program original = Interpreter.Program.registerHeaders(Interpreter.prepare(List.of()), new Interpreter.Header[]{target, root});
        Interpreter.HostBinding binding = new Interpreter.HostBinding(target);
        Interpreter.Program selected = Interpreter.Program.bindHostDefinitions(original, new Interpreter.HostBinding[]{binding});
        try {
            Interpreter.Program.bindHostDefinitions(original, new Interpreter.HostBinding[]{binding, binding});
            throw new AssertionError("Duplicate binding accepted");
        } catch (IllegalArgumentException expected) { check(true); }
        for (boolean host : new boolean[]{false, true}) {
            Interpreter.Program program = host ? selected : original;
            program = Interpreter.Program.materialize(program, target, fallback, new Interpreter.Header[0]);
            program = Interpreter.Program.materialize(program, root, caller, new Interpreter.Header[]{target});
            try {
                Interpreter.Program.bindHostDefinitions(program, new Interpreter.HostBinding[]{binding});
                throw new AssertionError("Late binding accepted");
            } catch (IllegalArgumentException expected) { check(true); }
            Interpreter engine = new Interpreter(program, true);
            try {
                engine.start(program.functionId(root), new Object[]{7L});
                for (int i = 0; i < 100 && engine.phase().equals("running"); i++) engine.advance(1);
                if (host) {
                    check(engine.pendingHostRequest() != null);
                    check(engine.pendingHostRequest().descriptor() == binding.descriptor());
                    new HostCall(binding.descriptor(), List.of(nat), nat,
                        xs -> ((BigInteger) xs.get(0)).add(BigInteger.ONE)).complete(engine, engine.pendingHostRequest());
                    for (int i = 0; i < 100 && engine.phase().equals("running"); i++) engine.advance(1);
                }
                check(engine.phase().equals("complete"));
                check(engine.takeResult().equals(host ? 8L : 7L));
            } finally { retire(engine); }
        }
        check(original.functionId(target) == selected.functionId(target));
        // Different source identity with the same textual name grants nothing.
        Interpreter.Header foreign = new Interpreter.SourceBinding("other").header(fallback, "a".repeat(64));
        try {
            Interpreter.Program.bindHostDefinitions(original, new Interpreter.HostBinding[]{new Interpreter.HostBinding(foreign)});
            throw new AssertionError("Foreign Header accepted");
        } catch (IllegalArgumentException expected) { check(true); }
    }
    private static void retire(Interpreter engine) {
        // These synthetic programs contain pure data and one fake extern only:
        // no resources, tasks or finalizers. Stopped test heaps are dropped for
        // Java GC, never incorrectly claimed to have completed guest disposal.
        if (engine.phase().equals("idle") || engine.phase().equals("complete")) engine.close();
    }
    private static Object invoke(LeanType type, String lane, Object raw,
                                 Function<List<Object>,Object> implementation) {
        Interpreter.HostExtern descriptor = descriptor(new String[]{lane}, new boolean[]{false}, lane);
        Interpreter engine = engine(descriptor);
        try {
            Interpreter.HostRequest request = start(engine, raw);
            new HostCall(descriptor, List.of(type), type, implementation).complete(engine, request);
            check(engine.phase().equals("complete"));
            Object result = engine.takeResult();
            check(engine.phase().equals("idle"));
            Object exported = ValueBridge.exportValue(type,
                result instanceof BigInteger && (lane.equals("uint64") || lane.equals("usize"))
                    ? Long.valueOf(((BigInteger) result).longValue()) : result, lane);
            engine.dec(result, 1);
            return exported;
        } finally { retire(engine); }
    }
    public static Object clojureRoundTrip(Function<List<Object>,Object> implementation) throws Exception {
        return invoke(field(packet(), 0), "tobject", 41L, implementation);
    }
    public static List<LeanType> clojureSignature() throws Exception { return List.of(field(packet(), 0)); }
    public static LeanType nominalType() throws Exception { return packet(); }
    public static Object nominalRoundTrip(Function<List<Object>,Object> implementation) throws Exception {
        LeanType type = packet(), box = field(type, 5);
        LeanData value = type.constructors().get(0).create(List.of(BigInteger.valueOf(42), BigInteger.ONE,
            new byte[]{1, 2}, java.util.Optional.empty(), List.of(BigInteger.TEN),
            box.constructors().get(0).create(List.of(BigInteger.ONE)), true, 1.0f, (int) 'x', -1));
        Interpreter.HostExtern descriptor = descriptor(new String[]{"object"}, new boolean[]{false}, "object");
        Interpreter engine = engine(descriptor);
        try {
            Object[] arguments = engine.constructDataArguments(new Interpreter.DataCtor[0],
                new Object[]{ValueBridge.prepareValue(type, value, "object")});
            new HostCall(descriptor, List.of(type), type, implementation).complete(engine, start(engine, arguments));
            Object raw = engine.takeResult(); Object result = ValueBridge.exportValue(type, raw, "object");
            engine.dec(raw, 1); return result;
        } finally { retire(engine); }
    }
    public static int run() throws Exception {
        checks = 0;
        LeanType packet = packet(), nat = field(packet, 0), bool = field(packet, 6);
        originalDefinitions(nat);
        check(invoke(nat, "tobject", 41L, xs -> ((BigInteger) xs.get(0)).add(BigInteger.ONE)).equals(BigInteger.valueOf(42)));
        check(invoke(bool, "uint8", 1L, xs -> !((Boolean) xs.get(0))).equals(false));
        check(invoke(field(packet, 1), "uint32", 0xffffffffL, xs -> xs.get(0)).equals(new BigInteger("4294967295")));
        check(invoke(field(packet, 9), "uint8", 255L, xs -> xs.get(0)).equals(BigInteger.valueOf(-1)));
        for (int bits : new int[]{0, Integer.MIN_VALUE, 0x7fc01234, 0xffc01234, 1}) {
            Object value = invoke(field(packet, 7), "float32", Float.intBitsToFloat(bits), xs -> xs.get(0));
            check(Float.floatToRawIntBits((Float) value) == bits);
        }
        for (long bits : new long[]{0, Long.MIN_VALUE, 0x7ff8000000001234L, 0xfff8000000001234L, 1}) {
            Object value = invoke(scalar(true), "float", Double.longBitsToDouble(bits), xs -> xs.get(0));
            check(Double.doubleToRawLongBits((Double) value) == bits);
        }
        BigInteger max64 = BigInteger.ONE.shiftLeft(64).subtract(BigInteger.ONE);
        check(invoke(scalar(false), "uint64", max64, xs -> xs.get(0)).equals(max64));
        check(invoke(field(packet, 8), "uint32", 0x1f600L, xs -> xs.get(0)).equals(0x1f600));
        // Fresh mutable guest Array storage, exported to a detached view and
        // returned by identity. The same root survives engine closure.
        LeanType array = field(packet, 4);
        Interpreter.HostExtern d = descriptor(new String[]{"object", "object"}, new boolean[]{false, true}, "object");
        Interpreter e = engine(d);
        Object saved;
        try {
            Object[] args = e.constructDataArguments(new Interpreter.DataCtor[]{Interpreter.DataCtor.array(new Object[]{4L, 5L})},
                new Object[]{new Interpreter.DataRef(0)});
            // The root facade owns both root occurrences, including the
            // borrowed parameter's adapter credit.
            e.inc(args[0], 1);
            Interpreter.HostRequest r = start(e, args[0], args[0]);
            Object safeReply = ValueBridge.prepareReply(array, List.of(1, 2), "object");
            try { e.resumeFrozenHost(r, safeReply); throw new AssertionError("Unfrozen input accepted"); }
            catch (IllegalArgumentException expected) { check(e.pendingHostRequest() == r); }
            new HostCall(d, List.of(array, array), array, xs -> {
                check(xs.get(0).equals(List.of(BigInteger.valueOf(4), BigInteger.valueOf(5))));
                check(xs.get(0).equals(xs.get(1)));
                try { xs.clear(); throw new AssertionError("Mutable argument list"); }
                catch (UnsupportedOperationException expected) { check(true); }
                return xs.get(0);
            }).complete(e, r);
            Object raw = e.takeResult(); saved = ValueBridge.exportValue(array, raw, "object"); e.dec(raw, 1);
            check(e.phase().equals("idle"));
            try {
                new HostCall(d, List.of(array, array), array, xs -> { throw new AssertionError("Stale callback ran"); }).complete(e, r);
                throw new AssertionError("Stale request accepted");
            } catch (IllegalStateException expected) { check(e.phase().equals("idle")); }
        } finally { retire(e); }
        check(saved.equals(List.of(BigInteger.valueOf(4), BigInteger.valueOf(5))));
        // A same-ABI descriptor is not authority for another binding's request.
        d = descriptor(new String[]{"tobject"}, new boolean[]{false}, "tobject"); e = engine(d);
        try {
            Interpreter.HostRequest r = start(e, 9L); AtomicInteger calls = new AtomicInteger();
            Interpreter foreign = engine(d);
            try {
                Interpreter.HostRequest foreignRequest = start(foreign, 8L);
                HostCall adapter = new HostCall(d, List.of(nat), nat, xs -> {
                    calls.incrementAndGet(); return xs.get(0);
                });
                try { adapter.complete(e, foreignRequest); throw new AssertionError("Foreign request accepted"); }
                catch (IllegalStateException expected) {
                    check(calls.get() == 0 && e.pendingHostRequest() == r && foreign.pendingHostRequest() == foreignRequest);
                }
                adapter.complete(foreign, foreignRequest); check(foreign.takeResult().equals(8L));
                calls.set(0);
            } finally { retire(foreign); }
            Interpreter.HostExtern other = descriptor(new String[]{"tobject"}, new boolean[]{false}, "tobject");
            try {
                new HostCall(other, List.of(nat), nat, xs -> { calls.incrementAndGet(); return xs.get(0); }).complete(e, r);
                throw new AssertionError("Wrong binding accepted");
            } catch (IllegalStateException expected) { check(calls.get() == 0 && e.pendingHostRequest() == r); }
            try { e.resumeFrozenHost(r, 1L); throw new AssertionError("Forged reply accepted"); }
            catch (IllegalArgumentException expected) { check(e.pendingHostRequest() == r); }
            new HostCall(d, List.of(nat), nat, xs -> xs.get(0)).complete(e, r);
            check(e.takeResult().equals(9L));
        } finally { retire(e); }
        // Nullary calls, a legitimate pure constant rather than hidden IO.
        d = descriptor(new String[0], new boolean[0], "tobject"); e = engine(d);
        try {
            new HostCall(d, List.of(), nat, xs -> { check(xs.isEmpty()); return BigInteger.TEN; }).complete(e, start(e));
            check(e.takeResult().equals(10L));
        } finally { retire(e); }
        for (int mode = 0; mode < 3; mode++) {
            d = descriptor(new String[]{"tobject"}, new boolean[]{false}, "tobject"); e = engine(d);
            final int which = mode;
            try {
                Interpreter.HostRequest r = start(e, 1L); AtomicInteger calls = new AtomicInteger();
                HostCall adapter = new HostCall(d, List.of(nat), nat, xs -> {
                    calls.incrementAndGet();
                    if (which == 0) throw new IllegalArgumentException("host error");
                    if (which == 1) return "wrong type";
                    throw new AssertionError("fatal host error");
                });
                try { adapter.complete(e, r); throw new AssertionError("Host failure accepted"); }
                catch (LeanException expected) { check(mode < 2 && expected.code().equals("HostFailure")); }
                catch (AssertionError expected) { check(mode == 2 && expected.getMessage().equals("fatal host error")); }
                check(calls.get() == 1 && e.phase().equals("failed") && e.failureRequest() == r);
                try { adapter.complete(e, r); throw new AssertionError("Replayed callback"); }
                catch (IllegalStateException expected) { check(calls.get() == 1); }
            } finally { retire(e); }
        }
        d = descriptor(new String[]{"tobject"}, new boolean[]{false}, "tobject"); e = engine(d);
        try {
            Interpreter.HostRequest r = start(e, 1L); AtomicInteger calls = new AtomicInteger();
            HostCall adapter = new HostCall(d, List.of(nat), nat, xs -> { calls.incrementAndGet(); return xs.get(0); });
            Thread.currentThread().interrupt();
            try { adapter.complete(e, r); throw new AssertionError("Ignored cancellation"); }
            catch (CancellationException expected) { check(Thread.currentThread().isInterrupted() && calls.get() == 0); }
            finally { Thread.interrupted(); }
            check(e.phase().equals("failed"));
        } finally { retire(e); }
        d = descriptor(new String[]{"tobject"}, new boolean[]{false}, "tobject"); e = engine(d);
        try {
            Interpreter.HostRequest r = start(e, 1L); AtomicInteger calls = new AtomicInteger();
            HostCall adapter = new HostCall(d, List.of(nat), nat, xs -> {
                calls.incrementAndGet(); Thread.currentThread().interrupt(); return xs.get(0);
            });
            try { adapter.complete(e, r); throw new AssertionError("Ignored callback cancellation"); }
            catch (CancellationException expected) { check(Thread.currentThread().isInterrupted() && calls.get() == 1); }
            finally { Thread.interrupted(); }
            check(e.phase().equals("failed"));
        } finally { retire(e); }
        return checks;
    }
    private static Map<String,Object> ioCtor(Object family,String label,int tag,int objects,List<Object> fields) {
        Object name=List.of("str",family,label);
        return Map.of("constructor",name,"ctorInfo",Map.of("name",name,"cidx",tag,"size",objects,"usize",0,"ssize",0),"fields",fields);
    }
    private static Map<String,Object> ioWitness() {
        Object out=List.of("str",name("EST"),"Out"),error=List.of("str",name("IO"),"Error");
        List<Object> fields=List.of(Map.of("kind","object","index",0,"irType","tobject"),Map.of("kind","void"));
        ArrayList<Object> errors=new ArrayList<>();
        for(int i=0;i<17;i++) errors.add(Map.of());
        errors.add(ioCtor(error,"unexpectedEof",17,0,List.of()));
        errors.add(ioCtor(error,"userError",18,1,List.of(Map.of("kind","object","index",0,"irType","object"))));
        return Map.of("world","canonical-erased-zero","ioFamilies",List.of(
            Map.of("typeName",out,"irType","object","constructors",List.of(ioCtor(out,"ok",0,1,fields),ioCtor(out,"error",1,1,fields))),
            Map.of("typeName",error,"irType","tobject","constructors",errors)));
    }
    private static Object nodeField(Object node,String field) throws Exception {
        java.lang.reflect.Field f=node.getClass().getDeclaredField(field);f.setAccessible(true);return f.get(node);
    }
    private static int ioChecks() throws Exception {
        int before=checks;LeanType nat=field(packet(),0);
        Map<String,Object> foreign=Map.of("kind","decl","name",name("foreign"),"ir",Map.of("extern",Map.of(
            "f",name("foreign"),"type","tobject","xs",List.of(Map.of("x",Map.of("idx",1),"ty","tobject","borrow",false)),
            "ext",Map.of("entries",List.of(Map.of("standard",Map.of("backend",name("all"),"fn","app_foreign")))))));
        Interpreter.Header foreignHeader=new Interpreter.SourceBinding("synthetic-foreign").header(foreign,"c".repeat(64));
        Interpreter.Program foreignProgram=Interpreter.Program.registerHeaders(Interpreter.prepare(List.of()),new Interpreter.Header[]{foreignHeader});
        Interpreter.HostBinding foreignBinding=new Interpreter.HostBinding(foreignHeader);
        foreignProgram=Interpreter.Program.bindHostDefinitions(foreignProgram,new Interpreter.HostBinding[]{foreignBinding});
        Interpreter foreignEngine=new Interpreter(foreignProgram,true);
        try {
            foreignEngine.start(foreignProgram.functionId(foreignHeader),new Object[]{3L});
            while(foreignEngine.phase().equals("running")) foreignEngine.advance(1);
            new HostCall(foreignBinding.descriptor(),List.of(nat),nat,xs->BigInteger.TEN).complete(foreignEngine,foreignEngine.pendingHostRequest());
            check(foreignEngine.takeResult().equals(10L));
        } finally {retire(foreignEngine);}

        Object authority=ValueBridge.compileIOLayouts(Interpreter.class,ioWitness());
        for(String worldLane:new String[]{"void","tagged"}) for(int mode=0;mode<5;mode++) {
            Interpreter.HostExtern d=descriptor(new String[]{"tobject",worldLane},new boolean[]{false,false},"object");
            Interpreter e=engine(d);final int which=mode;AtomicInteger calls=new AtomicInteger();
            try {
                Interpreter.HostRequest request=start(e,7L,0L);
                HostCall adapter=new HostCall(d,List.of(nat),nat,xs->{
                    check(xs.size()==1&&xs.get(0).equals(BigInteger.valueOf(7)));calls.incrementAndGet();
                    if(which==1) throw LeanIOError.userError("explicit IO failure");
                    if(which==2) throw LeanIOError.unexpectedEof();
                    if(which==3) throw new IllegalStateException("unexpected host failure");
                    if(which==4) return "invalid Nat";
                    return BigInteger.TEN;
                },authority);
                if(mode>=3) {
                    try {adapter.complete(e,request);throw new AssertionError("Host failure accepted");}
                    catch(LeanException failure) {check(failure.code().equals("HostFailure"));}
                    check(e.phase().equals("failed")&&e.failureRequest()==request&&calls.get()==1);
                } else {
                    adapter.complete(e,request);check(calls.get()==1&&e.phase().equals("complete"));
                    Object envelope=e.takeResult();check(((Integer)nodeField(envelope,"tag"))==(mode==0?0:1));
                    Object payload=((Object[])nodeField(envelope,"fields"))[0];
                    if(mode==0) check(payload.equals(10L));
                    else if(mode==1) {check(((Integer)nodeField(payload,"tag"))==18);check(((Object[])nodeField(payload,"fields"))[0].equals("explicit IO failure"));}
                    else check(payload.equals(17L));
                    e.dec(envelope,1);check(e.phase().equals("idle"));
                }
            } finally {retire(e);}
        }
        Interpreter.HostExtern invalid=descriptor(new String[]{"void"},new boolean[]{false},"object");
        try {new HostCall(invalid,List.of(),nat,xs->BigInteger.ONE,new Object());throw new AssertionError("Forged IO authority accepted");}
        catch(IllegalArgumentException expected) {check(true);}
        Interpreter wrongWorld=engine(invalid);AtomicInteger wrongCalls=new AtomicInteger();
        try {
            Interpreter.HostRequest request=start(wrongWorld,1L);
            try {new HostCall(invalid,List.of(),nat,xs->{wrongCalls.incrementAndGet();return BigInteger.ONE;},authority).complete(wrongWorld,request);throw new AssertionError("Nonzero world accepted");}
            catch(LeanException expected) {check(expected.code().equals("HostFailure")&&wrongCalls.get()==0&&wrongWorld.phase().equals("failed"));}
        } finally {retire(wrongWorld);}
        try {ValueBridge.compileIOLayouts(Interpreter.class,Map.of());throw new AssertionError("Missing IO witnesses accepted");}
        catch(IllegalArgumentException expected) {check(true);}
        try {LeanIOError.userError("\ud800");throw new AssertionError("Malformed IO error accepted");}
        catch(IllegalArgumentException expected) {check(true);}
        return checks-before;
    }
    public static void main(String[] args) throws Exception {
        int pure=run(); int io=ioChecks(); System.out.println("HostCallChecks: " + pure + " pure, " + io + " IO checks passed");
    }
}
