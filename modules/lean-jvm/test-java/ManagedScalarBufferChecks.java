import ansatz.lean.jvm.internal.exec.Interpreter;
import ansatz.lean.jvm.internal.exec.Interpreter.DataCtor;
import ansatz.lean.jvm.internal.exec.Interpreter.DataRef;
import ansatz.lean.jvm.internal.exec.Interpreter.Node;
import java.lang.reflect.Field;
import java.math.BigInteger;
import java.util.*;

/** Synthetic engine contract checks; native source/cohort acceptance is separate. */
public final class ManagedScalarBufferChecks {
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
    private static void check(boolean ok,String message) { checks++; if(!ok) throw new AssertionError(message); }
    private static Object field(Object value,String name) throws Exception {
        Field f=value.getClass().getDeclaredField(name); f.setAccessible(true); return f.get(value);
    }
    private static void rejected(Interpreter engine,Runnable action) {
        long before=engine.allocations;
        try { action.run(); throw new AssertionError("Expected rejected recipe"); }
        catch(IllegalArgumentException expected) { check(engine.allocations==before,"Validation allocated guest data"); }
    }
    private static void release(Interpreter engine,Object value) {
        engine.startRelease(value,1);
        for(int i=0;i<1000&&!engine.advance(1000);i++) { }
        check("complete".equals(engine.phase()),"Release did not finish"); engine.takeResult();
    }
    private static Map<String,Object> map(Object... pairs) {
        Map<String,Object> out=new LinkedHashMap<>();
        for(int i=0;i<pairs.length;i+=2) out.put((String)pairs[i],pairs[i+1]); return out;
    }
    private static Object name(String text) { return List.of("str",List.of("anonymous"),text); }
    private static Map<String,Object> externABI(String symbol,String result,String... lanes) {
        List<Object> xs=new ArrayList<>();
        for(int i=0;i<lanes.length;i++) xs.add(map("x",map("idx",i+1),"ty",lanes[i],"borrow",false));
        return map("kind","decl","name",name(symbol),"ir",map("extern",map("f",name(symbol),"xs",xs,"type",result,
                "ext",map("entries",List.of(map("standard",map("backend",name("all"),"fn",symbol)))))));
    }
    private static Object callABI(String symbol,String result,String[] lanes,Object... arguments) {
        return callRow(externABI(symbol,result,lanes),arguments);
    }
    private static Object callRow(Map<String,Object> row,Object... arguments) {
        try(Interpreter engine=new Interpreter(Interpreter.prepare(List.of(row)),true)) {
            engine.start(0,arguments);
            for(int i=0;i<1000&&!engine.advance(1000);i++) { }
            check("complete".equals(engine.phase()),"Intrinsic did not complete"); return engine.takeResult();
        }
    }
    private static Object call(String symbol,String lane,Object... arguments) {
        String[] lanes=new String[arguments.length]; Arrays.fill(lanes,lane);
        return callABI(symbol,lane,lanes,arguments);
    }
    private static int f32bits(Object value) { return Float.floatToRawIntBits((Float)value); }
    @SuppressWarnings("unchecked")
    private static void unsignedNatNarrowing() {
        // Pinned lean.h uint{8,16,32}_of_nat(_mk): modulo conversion for both
        // borrowed Nat and consuming BitVec representations, proof erased.
        for(int bits:new int[]{8,16,32}) for(int form=0;form<3;form++) {
            boolean owned=form==2,proof=form==1;
            String symbol="lean_uint"+bits+"_of_nat"+(owned?"_mk":""),lane="uint"+bits;
            Map<String,Object> row=externABI(symbol,lane,proof?new String[]{"tobject","erased"}:new String[]{"tobject"});
            Map<String,Object> ext=(Map<String,Object>)((Map<String,Object>)row.get("ir")).get("extern");
            ((Map<String,Object>)((List<?>)ext.get("xs")).get(0)).put("borrow",!owned);
            BigInteger mask=BigInteger.ONE.shiftLeft(bits).subtract(BigInteger.ONE);
            for(BigInteger n:new BigInteger[]{BigInteger.ZERO,mask,mask.add(BigInteger.ONE),
                    BigInteger.ONE.shiftLeft(64).subtract(BigInteger.ONE),
                    BigInteger.ONE.shiftLeft(200).add(new BigInteger("89abcdef",16))}) {
                Object actual=proof?callRow(row,n,0L):callRow(row,n);
                check(actual.equals(Long.valueOf(n.and(mask).longValue())),"Unsigned Nat narrowing/ownership ABI");
            }
        }
    }
    private static void floatBitObservations() {
        // Independent pinned object.cpp to_bits contract: all NaNs use the
        // logical canonical pattern; every other IEEE bit pattern is exact.
        for(long bits:new long[]{0,Long.MIN_VALUE,1,0x000fffffffffffffL,0x0010000000000000L,
                0x3ff0000000000001L,0x7fefffffffffffffL,0x7ff0000000000000L,0xfff0000000000000L,
                0x7ff8000000001234L,0x7ff0000000000001L,0xfff8000000001234L}) {
            long expected=Double.isNaN(Double.longBitsToDouble(bits))?0x7ff8000000000000L:bits;
            Object actual=callABI("lean_float_to_bits","uint64",new String[]{"float"},Double.valueOf(Double.longBitsToDouble(bits)));
            BigInteger observed=actual instanceof BigInteger?(BigInteger)actual:BigInteger.valueOf((Long)actual);
            check(observed.equals(new BigInteger(Long.toUnsignedString(expected))),"Float.toBits exact IEEE/canonical NaN");
        }
        for(int bits:new int[]{0,Integer.MIN_VALUE,1,0x007fffff,0x00800000,0x3f800001,
                0x7f7fffff,0x7f800000,0xff800000,0x7fc01234,0x7fa00001,0xffc01234}) {
            int expected=Float.isNaN(Float.intBitsToFloat(bits))?0x7fc00000:bits;
            check(callABI("lean_float32_to_bits","uint32",new String[]{"float32"},Float.valueOf(Float.intBitsToFloat(bits)))
                    .equals(Long.valueOf(Integer.toUnsignedLong(expected))),"Float32.toBits exact IEEE/canonical NaN");
        }
        try {
            Interpreter.prepare(List.of(externABI("lean_float_to_bits","uint32","float")));
            throw new AssertionError("Float.toBits accepted wrong result lane");
        } catch(IllegalArgumentException expected) { checks++; }
        try {
            Interpreter.prepare(List.of(externABI("lean_float32_to_bits","uint32","float")));
            throw new AssertionError("Float32.toBits accepted wrong argument lane");
        } catch(IllegalArgumentException expected) { checks++; }
    }
    private static void float32LiteralDependencies() {
        // Pin819816 object.cpp:1987 canonicalizes NaNs; non-NaNs retain their exact bits.
        for(long bits:new long[]{0,0x80000000L,1,0x007fffffL,0x00800000L,0x3f800001L,0x7f7fffffL,0x7f800000L,0xff800000L})
            check(f32bits(callABI("lean_float32_of_bits","float32",new String[]{"uint32"},Long.valueOf(bits)))==(int)bits,"Float32.ofBits non-NaN identity");
        for(long bits:new long[]{0x7fc01234L,0x7fa00001L,0xffc01234L})
            check(f32bits(callABI("lean_float32_of_bits","float32",new String[]{"uint32"},Long.valueOf(bits)))==0x7fc00000,"Float32.ofBits NaN canonicalization");
        BigInteger mask=BigInteger.ONE.shiftLeft(32).subtract(BigInteger.ONE);
        for(BigInteger input:new BigInteger[]{BigInteger.ZERO,BigInteger.valueOf(17),mask,
                BigInteger.ONE.shiftLeft(32),BigInteger.ONE.shiftLeft(200).add(new BigInteger("89abcdef",16))})
            check(callABI("lean_uint32_of_nat_mk","uint32",new String[]{"tobject"},input).equals(Long.valueOf(input.and(mask).longValue())),"Owned Nat narrowing modulo2^32");
        check(f32bits(call("lean_float32_div","float32",Float.valueOf(1),Float.valueOf(3)))==0x3eaaaaab,"Float32 division rounds to32bits");
        check(f32bits(call("lean_float32_div","float32",Float.valueOf(Float.MIN_VALUE),Float.valueOf(2)))==0,"Float32 division subnormal tie rounds even");
        check(f32bits(call("lean_float32_div","float32",Float.valueOf(-0.0f),Float.valueOf(2)))==Integer.MIN_VALUE,"Float32 division preserves negative zero");
        check(f32bits(call("lean_float32_div","float32",Float.valueOf(1),Float.valueOf(-0.0f)))==0xff800000,"Float32 division signed infinity");
        check(Float.isNaN((Float)call("lean_float32_div","float32",Float.valueOf(0),Float.valueOf(0))),"Float32 zero divided by zero");
        check(f32bits(call("lean_float32_mul","float32",Float.valueOf(Float.MIN_NORMAL),Float.valueOf(0.5f)))==0x00400000,"Float32 multiplication subnormal");
        check(f32bits(call("lean_float32_mul","float32",Float.valueOf(-0.0f),Float.valueOf(2)))==Integer.MIN_VALUE,"Float32 multiplication negative zero");
        check(Float.isInfinite((Float)call("lean_float32_mul","float32",Float.MAX_VALUE,Float.valueOf(2))),"Float32 multiplication overflow");
        float aboveOne=Float.intBitsToFloat(0x3f800001);
        check(f32bits(call("lean_float32_mul","float32",Float.valueOf(aboveOne),Float.valueOf(aboveOne)))==0x3f800002,"Float32 multiplication rounds at24bits");
        // This exact integer is just above a Float32 midpoint but rounds to that
        // midpoint in Double. A double-mediated conversion would yield5f000000.
        BigInteger midpointAbove=BigInteger.ONE.shiftLeft(63).add(BigInteger.ONE.shiftLeft(39)).add(BigInteger.ONE);
        check(f32bits(callABI("lean_uint64_to_float32","float32",new String[]{"uint64"},midpointAbove))==0x5f000001,"UInt64 to Float32 must not double-round");
        check(f32bits(callABI("lean_uint64_to_float32","float32",new String[]{"uint64"},BigInteger.ONE.shiftLeft(64).subtract(BigInteger.ONE)))==0x5f800000,"Unsigned64 maximum to Float32");
        check(f32bits(callABI("lean_uint64_to_float32","float32",new String[]{"uint64"},Long.valueOf(0)))==0,"Unsigned64 zero to Float32");
    }
    public static void main(String[] args) throws Exception {
        try(Interpreter engine=new Interpreter(Interpreter.prepare(List.of()),true)) {
            byte[] input={1,2,3}; Object[] arrayFields={new DataRef(0),new DataRef(1)};
            Object[] roots=engine.constructDataArguments(new DataCtor[]{DataCtor.boxedScalar("float",Long.MIN_VALUE),
                    DataCtor.bytes(input),DataCtor.array(arrayFields)},new Object[]{new DataRef(2)});
            Node array=(Node)roots[0],scalar=(Node)nodeFields(array)[0],bytes=(Node)nodeFields(array)[1];
            check(nodeTag(array)==246&&Boolean.TRUE.equals(field(array,"array")),"Array runtime kind");
            check(field(array,"metadata").getClass().getSimpleName().equals("ArrayState"),"Array metadata");
            check(((Integer)field(field(array,"metadata"),"size"))==2,"Array live size");
            check(nodeTag(scalar)==0&&nodeFields(scalar).length==0&&nodeScalars(scalar).length==8,"Scalar BOX layout");
            check(nodeScalars(scalar)[7]==(byte)128,"Float negative-zero raw bits");
            check(nodeTag(bytes)==248&&nodeFields(bytes).length==0&&nodeScalars(bytes).length==3,"ByteArray layout");
            check(field(bytes,"metadata").getClass().getSimpleName().equals("ByteArrayState"),"ByteArray metadata");
            check(nodeRC(array)==1&&nodeRC(scalar)==1&&nodeRC(bytes)==1,"Single owner per node");
            input[0]=99; arrayFields[0]=Long.valueOf(9);
            check(nodeScalars(bytes)[0]==1&&nodeFields(array)[0]==scalar,"Caller snapshots changed");
            release(engine,array);
            check(Boolean.TRUE.equals(field(array,"dead"))&&Boolean.TRUE.equals(field(scalar,"dead"))
                    &&Boolean.TRUE.equals(field(bytes,"dead")),"Owned tree release missed a special node");
            Object[] empty=engine.constructDataArguments(new DataCtor[]{DataCtor.array(new Object[0])},new Object[]{new DataRef(0)});
            check(nodeFields(((Node)empty[0])).length==0,"Empty Array"); release(engine,empty[0]);
            Object[] ordinary=engine.constructDataArguments(new DataCtor[]{new DataCtor(1,new Object[]{Long.valueOf(7)})},new Object[]{new DataRef(0)});
            check(nodeTag(((Node)ordinary[0]))==1,"Old constructor compatibility"); release(engine,ordinary[0]);
            Object[] f32=engine.constructDataArguments(new DataCtor[]{DataCtor.boxedScalar("float32",0x80000000L)},new Object[]{new DataRef(0)});
            check(nodeScalars(((Node)f32[0])).length==4&&nodeScalars(((Node)f32[0]))[3]==(byte)128,"Float32 negative zero"); release(engine,f32[0]);
            Object[] u64=engine.constructDataArguments(new DataCtor[]{DataCtor.boxedScalar("uint64",-1L)},new Object[]{new DataRef(0)});
            check(Arrays.equals(nodeScalars(((Node)u64[0])),new byte[]{-1,-1,-1,-1,-1,-1,-1,-1}),"UInt64 all bits"); release(engine,u64[0]);
            rejected(engine,()->DataCtor.boxedScalar("float32",0x100000000L));
            rejected(engine,()->DataCtor.boxedScalar("uint32",1));
            rejected(engine,()->engine.constructDataArguments(new DataCtor[]{DataCtor.array(new Object[]{new DataRef(0)})},new Object[]{new DataRef(0)}));
            rejected(engine,()->engine.constructDataArguments(new DataCtor[]{DataCtor.bytes(new byte[0])},new Object[]{new DataRef(0),new DataRef(0)}));
            rejected(engine,()->engine.constructDataArguments(new DataCtor[]{DataCtor.bytes(new byte[0])},new Object[0]));
            rejected(engine,()->engine.constructDataArguments(new DataCtor[]{DataCtor.bytes(new byte[600000]),DataCtor.bytes(new byte[600000])},new Object[]{new DataRef(0),new DataRef(1)}));
            rejected(engine,()->engine.constructDataArguments(new DataCtor[]{DataCtor.array(new Object[]{array})},new Object[]{new DataRef(0)}));
        }
        check(call("lean_uint8_add","uint8",Long.valueOf(255),Long.valueOf(2)).equals(Long.valueOf(1)),"UInt8 wraps modulo256");
        check(call("lean_int64_neg","uint64",BigInteger.ONE.shiftLeft(63)).equals(BigInteger.ONE.shiftLeft(63)),"Int64 min neg wraps");
        check(call("lean_int64_neg","uint64",Long.valueOf(1)).equals(BigInteger.ONE.shiftLeft(64).subtract(BigInteger.ONE)),"Int64 neg bits");
        check(call("lean_float_add","float",Double.valueOf(1.25),Double.valueOf(2.5)).equals(Double.valueOf(3.75)),"Float add");
        check(Double.doubleToRawLongBits((Double)call("lean_float_add","float",Double.valueOf(-0.0),Double.valueOf(-0.0)))==Long.MIN_VALUE,"Float signed zero");
        check(Double.isNaN((Double)call("lean_float_add","float",Double.POSITIVE_INFINITY,Double.NEGATIVE_INFINITY)),"Float nonfinite add");
        check(call("lean_float32_add","float32",Float.valueOf(16777216f),Float.valueOf(1f)).equals(Float.valueOf(16777216f)),"Float32 rounds at24bits");
        check(Float.floatToRawIntBits((Float)call("lean_float32_add","float32",Float.valueOf(-0.0f),Float.valueOf(-0.0f)))==Integer.MIN_VALUE,"Float32 signed zero");
        check(Float.isInfinite((Float)call("lean_float32_add","float32",Float.MAX_VALUE,Float.MAX_VALUE)),"Float32 overflow");
        float32LiteralDependencies();
        floatBitObservations();
        unsignedNatNarrowing();
        System.out.println("ManagedScalarBufferChecks PASS "+checks);
    }
}
