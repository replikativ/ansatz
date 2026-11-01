import ansatz.research.ir.Interpreter;
import ansatz.research.ir.Interpreter.DataCtor;
import ansatz.research.ir.Interpreter.DataRef;
import ansatz.research.ir.Interpreter.Node;
import java.lang.reflect.Field;
import java.math.BigInteger;
import java.util.*;

/** Synthetic engine contract checks; native source/cohort acceptance is separate. */
public final class ManagedScalarBufferChecks {
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
        try(Interpreter engine=new Interpreter(Interpreter.prepare(List.of(externABI(symbol,result,lanes))),true)) {
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
            Node array=(Node)roots[0],scalar=(Node)array.fields[0],bytes=(Node)array.fields[1];
            check(array.tag==246&&Boolean.TRUE.equals(field(array,"array")),"Array runtime kind");
            check(field(array,"metadata").getClass().getSimpleName().equals("ArrayState"),"Array metadata");
            check(((Integer)field(field(array,"metadata"),"size"))==2,"Array live size");
            check(scalar.tag==0&&scalar.fields.length==0&&scalar.scalars.length==8,"Scalar BOX layout");
            check(scalar.scalars[7]==(byte)128,"Float negative-zero raw bits");
            check(bytes.tag==248&&bytes.fields.length==0&&bytes.scalars.length==3,"ByteArray layout");
            check(field(bytes,"metadata").getClass().getSimpleName().equals("ByteArrayState"),"ByteArray metadata");
            check(array.rc==1&&scalar.rc==1&&bytes.rc==1,"Single owner per node");
            input[0]=99; arrayFields[0]=Long.valueOf(9);
            check(bytes.scalars[0]==1&&array.fields[0]==scalar,"Caller snapshots changed");
            release(engine,array);
            check(Boolean.TRUE.equals(field(array,"dead"))&&Boolean.TRUE.equals(field(scalar,"dead"))
                    &&Boolean.TRUE.equals(field(bytes,"dead")),"Owned tree release missed a special node");
            Object[] empty=engine.constructDataArguments(new DataCtor[]{DataCtor.array(new Object[0])},new Object[]{new DataRef(0)});
            check(((Node)empty[0]).fields.length==0,"Empty Array"); release(engine,empty[0]);
            Object[] ordinary=engine.constructDataArguments(new DataCtor[]{new DataCtor(1,new Object[]{Long.valueOf(7)})},new Object[]{new DataRef(0)});
            check(((Node)ordinary[0]).tag==1,"Old constructor compatibility"); release(engine,ordinary[0]);
            Object[] f32=engine.constructDataArguments(new DataCtor[]{DataCtor.boxedScalar("float32",0x80000000L)},new Object[]{new DataRef(0)});
            check(((Node)f32[0]).scalars.length==4&&((Node)f32[0]).scalars[3]==(byte)128,"Float32 negative zero"); release(engine,f32[0]);
            Object[] u64=engine.constructDataArguments(new DataCtor[]{DataCtor.boxedScalar("uint64",-1L)},new Object[]{new DataRef(0)});
            check(Arrays.equals(((Node)u64[0]).scalars,new byte[]{-1,-1,-1,-1,-1,-1,-1,-1}),"UInt64 all bits"); release(engine,u64[0]);
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
        System.out.println("ManagedScalarBufferChecks PASS "+checks);
    }
}
