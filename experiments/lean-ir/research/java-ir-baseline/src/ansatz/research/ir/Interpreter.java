/*
 * Experimental JVM port of Lean's lambda-RC interpreter, pinned to
 * 819816b2e0a3bf405af45ae5c7af2491d8f5bee6:src/library/ir_interpreter.cpp.
 * Upstream: Copyright (c) 2019 Microsoft Corporation. Apache-2.0.
 * Author of upstream interpreter: Sebastian Ullrich.
 *
 * Bounded object/uint8/uint32/usize/uint64/float profile (64-bit little-endian), not a public API.
 * Research eager graph forks and typed host requests, not a persistent branch
 * store, native ABI invocation, general host IO, or arbitrary World conversion.
 */
package ansatz.research.ir;

import java.math.BigInteger;
import java.math.BigDecimal;
import java.math.RoundingMode;
import java.lang.ref.WeakReference;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.concurrent.atomic.AtomicLong;

public final class Interpreter implements AutoCloseable {
    private static final int OBJ=0, U8=1, U32=2, USIZE=3, U64=4, F64=5;
    private static final int VDECL=0,JDECL=1,SET=2,SSET=3,INC=4,DEC=5,DEL=6,CASE=7,RET=8,JMP=9,UNREACHABLE=10,SETTAG=11,USET=12;
    private static final int MAP_APPLY=13,MAP_WRAP=14;
    private static final int CTOR=0,PROJ=1,SPROJ=2,FAP=3,PAP=4,AP=5,BOX=6,UNBOX=7,LIT=8,SHARED=9,UPROJ=10;
    private static final int ADD=1,SUB=2,MOD=3,EQ=4,LT=5,MUL=6,DIV=7,POW=8;
    private static final int USIZE_NAT=9,USIZE_REPR=10,U32_NAT=11,U32_EQ=12,U32_LE=13,PLATFORM_BITS=14;
    private static final int STR_POS_SET=260;
    private static final int EXPR_DATA=400,EXPR_APP_DATA=401,LEVEL_DATA=402,EXPR_CACHE=403;
    private static final int PROFILE_IT=410;
    private static final int STR_PUSH=15,STR_LIST=16,STR_GET=17,STR_NEXT=18,STR_APPEND=19,STR_SIZE=20,
                             ARRAY_MK=21,ARRAY_SIZE=22,ARRAY_GET=23,GET_STDOUT=24,PANIC=25;
    private static final int REF_MK=26,REF_GET=27,REF_SET=28,REF_SWAP=29,REF_TAKE=30,REF_PTR_EQ=31;
    private static final int ARRAY_EMPTY=32,ARRAY_PUSH=33,ARRAY_POP=34,ARRAY_USIZE=35,
                             ARRAY_FGET=36,ARRAY_UGET=37,ARRAY_UGET_BORROWED=38,
                             ARRAY_FSET=39,ARRAY_USET=40,ARRAY_SWAP=41,ARRAY_LIST=42,ARRAY_REPLICATE=43;
    private static final int STR_END=44,STR_SAFE_GET=45,STR_SAFE_NEXT=46,STR_PREV=47,STR_VALID=48,
                             STR_EXTRACT=49,STR_EQ=50,STR_LT=51,STR_COMPARE=52,STR_BYTE=53,
                             STR_CONTAINS=54,STR_LENGTH=55,STR_SET=56;
    private static final int NAT_LE=57,NAT_LOG2=58,NAT_OR=59,NAT_SHL=60,NAT_SHR=61,TASK_PURE=62,TASK_GET=63,TASK_MAP=97;
    private static final int ARRAY_CHECKED_GET=64,ARRAY_CHECKED_BORROWED=65;
    private static final int IO_INITIALIZING=66;
    private static final int USIZE_LT=67,USIZE_ADD=68,USIZE_EQ=69,USIZE_SUB=70,USIZE_TO_NAT=71,
                             USIZE_SHR=72,USIZE_SHL=73,USIZE_AND=74,U8_NAT=75,U8_EQ=76,U8_AND=77,
                             U8_LE=78,U32_FROM_NAT=79,U32_TO_U8=80,U32_ADD=81,USIZE_LE=82,USIZE_MUL=83;
    private static final int STR_HASH=84,U64_MIX=85,U64_NAT=86,U64_SHR=87,U64_XOR=88,U64_USIZE=89,
                             U64_LT=90,U64_EQ=91,U64_OWNED_NAT=92,U64_TO_U32=98;
    private static final int BOOL_U64=500,U64_ADD=501,U64_SUB=502,U64_MUL=503,U64_DIV=504,U64_MOD=505,
                             U64_AND=506,U64_OR=507,U64_NOT=508,U64_NEG=509,U64_LOG2=510,U64_SHL=511,U64_LE=512;
    private static final int U8_TO_U64=513,U32_TO_U64=514,USIZE_TO_U64=515;
    private static final int BYTE_MK=200,BYTE_GET=201,BYTE_SIZE=202,BYTE_PUSH=203;
    private static final int INT_OF_NAT=210,INT_NEG_SUCC=211,INT_NEG=212,INT_ABS=213,INT_ADD=214,INT_SUB=215,INT_EQ=216,INT_LT=217,INT_LE=218;
    private static final int STR_MEMCMP=230,STR_SUBSTRING_EQ=231,STR_POS_OF=232,STR_OFFSET_OF_POS=233,STR_PUSHN=234;
    private static final int MAX_STRING_OUTPUT_BYTES=16*1024*1024;
    private static final int MAX_BYTE_CAPACITY=16*1024*1024;
    private static final int POINTER_IDENTITY=93, NAME_EQ=94, BUILD_GITHASH=95, BUILD_TARGET=96;
    private static final int FLOAT_BITS=240,FLOAT_U64=241,FLOAT_SUB=242,FLOAT_MUL=243,FLOAT_DIV=244,FLOAT_EQ=245,FLOAT_LT=246,FLOAT_STRING=247;
    private static final int MAX_NAME_COMPARISON_STEPS=1_000_000;
    private static final int MAX_SHIFT_RESULT_BITS=16*1024*1024;
    private static final int MAX_ARRAY_CAPACITY=1_000_000;
    private static final int PROMISE_NEW=300,PROMISE_RESOLVE=301,PROMISE_RESULT=302,TASK_BIND=303,
                             IO_TASK_MAP=304,IO_TASK_BIND=305,TASK_STATE=306,TASK_WAIT=307,
                             TASK_CANCEL=308,TASK_CANCELED=309,OPTION_BLOCK=310,TASK_SPAWN=311,IO_AS_TASK=312;
    private static final int STREAM_FLUSH=100,STREAM_READ=101,STREAM_WRITE=102,STREAM_LINE=103,STREAM_PUT=104,STREAM_TTY=105;
    private static final BigInteger SMALL_MAX=BigInteger.valueOf(Long.MAX_VALUE);
    private static final Object ERASED=Long.valueOf(0);
    private static final int MAX_IMPORT_NODES=100_000, MAX_IMPORT_ROOTS=100_000, MAX_IMPORT_EDGES=1_000_000;
    private static final long MAX_IMPORT_SCALAR_BYTES=16L*1024*1024, MAX_IMPORT_CARRIER_BYTES=16L*1024*1024;

    /** Opt-in captured ABI descriptor, not a Java function or host capability.
     * Strings and array views are immutable/defensive. The driver supplies the
     * actual host behavior only after receiving an engine-owned request. */
    public static final class HostExtern {
        private final String symbol,resultType;
        private final String[] paramTypes;
        private final boolean[] borrowed;
        public HostExtern(String symbol,String[] paramTypes,boolean[] borrowed,String resultType) {
            require(symbol!=null&&!symbol.isEmpty()&&symbol.length()<=4096&&symbol.indexOf('\0')<0,
                    "Invalid host extern symbol");
            require(paramTypes!=null&&borrowed!=null&&paramTypes.length==borrowed.length,
                    "Invalid host extern parameter ABI");
            String[] types=paramTypes.clone(); boolean[] borrows=borrowed.clone();
            type(resultType);
            for(String parameter:types) type(parameter);
            this.symbol=symbol; this.resultType=resultType;
            this.paramTypes=types; this.borrowed=borrows;
        }
        public String symbol() { return symbol; }
        public String[] paramTypes() { return paramTypes.clone(); }
        public boolean[] borrowed() { return borrowed.clone(); }
        public String resultType() { return resultType; }
        private boolean sameAbi(HostExtern other) {
            return resultType.equals(other.resultType)&&Arrays.equals(paramTypes,other.paramTypes)
                    &&Arrays.equals(borrowed,other.borrowed);
        }
        private boolean matches(Map<String,Object> declaration) {
            List<Object> params=list(declaration.get("xs"));
            if(!resultType.equals(declaration.get("type"))||params.size()!=paramTypes.length) return false;
            for(int i=0;i<params.size();i++) {
                Map<String,Object> parameter=map(params.get(i));
                if(!paramTypes[i].equals(parameter.get("ty"))
                        ||!Boolean.valueOf(borrowed[i]).equals(parameter.get("borrow"))) return false;
            }
            return true;
        }
    }
    /** Borrowed diagnostic views acquire NO argument credits. Owned ABI args
     * remain the handler's consume/transfer obligations. Borrowed args must not
     * be consumed: root/AP calls hold known owned facade credits until a valid
     * successful reply; typed FAP calls have no such adapter credits. Returning
     * a borrowed argument requires an explicit owned retain by the handler. */
    public static final class HostRequest {
        private final Object owner;
        private final HostCall call;
        private HostRequest(Object owner,HostCall call) { this.owner=owner; this.call=call; }
        public String symbol() { return call.function.hostExtern.symbol; }
        public String[] paramTypes() { return call.function.hostExtern.paramTypes(); }
        public boolean[] borrowed() { return call.function.hostExtern.borrowed(); }
        public String resultType() { return call.function.hostExtern.resultType; }
        public Object[] arguments() { return argumentViews(call.function,call.arguments); }
        public boolean argumentTransferred(int index) {
            require(index>=0&&index<call.arguments.length,"Host argument index outside ABI");
            return call.argumentTransferred!=null&&call.argumentTransferred[index];
        }
    }
    /** Engine-private continuation and ownership disposition. It is copied by
     * the same fork memo as stack/argument graphs; it never runs a host handler. */
    private static final class HostCall {
        Function function;
        Object[] arguments,surplus;
        Body next;
        int dest,kind,borrowedCursor;
        boolean facade,replyClaimed,adapterReleaseStarted,resultOwned,resultTransferStarted;
        Object completionResult;
        long completionScalar;
        HostCall previousCompletion;
        boolean[] argumentTransferred;
    }

    /** Trusted-adapter setup policy, not source hash authentication. Headers
     * retain only their existing immutable code/source metadata, never an engine. */
    public static final class HostGuestPolicy {
        private final Header[] outerHeaders,helperHeaders;
        private HostGuestPolicy(Header[] outerHeaders,Header[] helperHeaders) {
            require(outerHeaders!=null&&outerHeaders.length>0&&outerHeaders.length<=64
                    &&helperHeaders!=null&&helperHeaders.length>0&&helperHeaders.length<=64,"Invalid host guest policy size");
            this.outerHeaders=outerHeaders.clone(); this.helperHeaders=helperHeaders.clone();
            Set<Header> seen=Collections.newSetFromMap(new IdentityHashMap<Header,Boolean>());
            for(Header header:this.outerHeaders) require(header!=null&&seen.add(header),"Duplicate/null outer Header");
            seen.clear();
            for(Header header:this.helperHeaders) require(header!=null&&seen.add(header),"Duplicate/null helper Header");
        }
        public static HostGuestPolicy of(Header[] outerHeaders,Header[] helperHeaders) {
            return new HostGuestPolicy(outerHeaders,helperHeaders);
        }
        private boolean outer(Header target) { for(Header h:outerHeaders) if(h==target) return true; return false; }
        private boolean helper(Header target) { for(Header h:helperHeaders) if(h==target) return true; return false; }
        public Header[] outerHeaders() { return outerHeaders.clone(); }
        public Header[] helperHeaders() { return helperHeaders.clone(); }
    }
    /** An explicit credit source, not a way to manufacture one. owned(value)
     * has the existing caller-owned-credit precondition. An outer-slot transfer
     * is checked/consumed once by its actual engine/HostCall, not this descriptor. */
    public static final class HostGuestArgument {
        private final Object value;
        private final HostRequest outer;
        private final int index;
        private HostGuestArgument(Object value,HostRequest outer,int index) { this.value=value; this.outer=outer; this.index=index; }
        public static HostGuestArgument owned(Object value) { return new HostGuestArgument(value,null,-1); }
        public static HostGuestArgument fromHostArgument(HostRequest outer,int index) {
            require(outer!=null&&index>=0,"Actual host argument index required");
            return new HostGuestArgument(null,outer,index);
        }
    }
    /** Borrowed operation/result view. The token owns no extra guest credits
     * and contains no strong Interpreter reference. Engine claim is one-shot. */
    public static final class HostGuestOperation {
        private final Object owner;
        private final HostGuestRecord record;
        private HostGuestOperation(Object owner,HostGuestRecord record) { this.owner=owner; this.record=record; }
        public HostRequest outerRequest() { return record.outer; }
        public Header helperHeader() { return record.helper; }
        public boolean isRelease() { return record.release; }
        public boolean resultTaken() { return record.taken; }
        public boolean argumentsOwned() { return record.argumentsOwned; }
        public boolean resultOwned() { return record.resultOwned; }
        public Object[] arguments() { return record.arguments==null?new Object[0]:record.arguments.clone(); }
        public Object result() {
            if(!record.complete||record.taken) throw new IllegalStateException("No unclaimed host guest result");
            return record.result;
        }
    }
    private static final class HostGuestRecord {
        HostGuestRecord parent;
        HostRequest outer;
        HostGuestOperation token;
        RuntimeAction action;
        Header helper;
        Function function,caller;
        PreparedBody callerPrepared;
        Body savedPc;
        TaskRecord scope;
        HostCall completionBase;
        Object[] arguments;
        int[] movedSlots;
        int bp,sp,jbp,jsp,depth,count;
        boolean release,argumentsOwned,entered,complete,resultOwned,taken,releaseClaimed;
        Object result;
    }

    /** Borrowed diagnostic view of a committed code activation. This request
     * grants no source IO capability and creates no argument owner credits. */
    public static final class CodeRequest {
        private final Object owner;
        private final CodeActivation activation;
        private CodeRequest(Object owner,CodeActivation activation) { this.owner=owner; this.activation=activation; }
        public Header header() { return activation.function.header; }
        public SourceBinding source() { return header().source(); }
        public Object name() { return header().name(); }
        public String originalSha256() { return header().originalSha256(); }
        public int functionId() { return activation.function.id; }
        public int[] params() { return header().params(); }
        public String[] paramTypes() { return header().paramTypes(); }
        public boolean[] borrowed() { return header().borrowed(); }
        public String resultType() { return header().resultType(); }
        public Object[] arguments() { return argumentViews(activation.function,activation.arguments); }
    }
    /** Arguments/captures have already transferred according to the caller's
     * ABI. Resume enters this exact activation; it never prepares AP again. */
    private static final class CodeActivation {
        Function function;
        Object[] arguments,surplus;
        Body next;
        int dest,kind;
        boolean claimed;
    }

    /** Exact captured ABI, deliberately distinct from physical JVM lanes. */
    private static final class ExternSpec {
        final String symbol,resultType;
        final int intrinsic;
        final String[] paramTypes;
        final boolean[] borrowed;
        ExternSpec(String symbol,int intrinsic,String resultType,String[] paramTypes,boolean[] borrowed) {
            this.symbol=symbol; this.intrinsic=intrinsic; this.resultType=resultType;
            this.paramTypes=paramTypes.clone(); this.borrowed=borrowed.clone();
            if(paramTypes.length!=borrowed.length) throw new IllegalArgumentException("Invalid extern registry entry");
        }
        boolean matches(Map<String,Object> declaration) {
            List<Object> params=list(declaration.get("xs"));
            if(!resultType.equals(declaration.get("type"))||params.size()!=paramTypes.length) return false;
            for(int i=0;i<params.size();i++) {
                Map<String,Object> p=map(params.get(i));
                if(!paramTypes[i].equals(p.get("ty"))||!Boolean.valueOf(borrowed[i]).equals(p.get("borrow"))) return false;
            }
            return true;
        }
    }
    private static final Map<String,List<ExternSpec>> EXTERNS=externRegistry();
    private static Map<String,List<ExternSpec>> externRegistry() {
        Map<String,List<ExternSpec>> registry=new LinkedHashMap<>();
        String[] symbols={"lean_nat_add","lean_nat_sub","lean_nat_mod","lean_nat_dec_eq","lean_nat_dec_lt",
                          "lean_nat_mul","lean_nat_div","lean_nat_pow"};
        int[] ops={ADD,SUB,MOD,EQ,LT,MUL,DIV,POW};
        for(int i=0;i<symbols.length;i++) register(registry,new ExternSpec(symbols[i],ops[i],
                ops[i]==EQ||ops[i]==LT?"uint8":"tobject",new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_usize_of_nat",USIZE_NAT,"usize",new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_usize_of_nat",USIZE_NAT,"usize",new String[]{"tobject","erased"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_string_of_usize",USIZE_REPR,"object",new String[]{"usize"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_uint32_to_nat",U32_NAT,"tobject",new String[]{"uint32"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint32_dec_eq",U32_EQ,"uint8",new String[]{"uint32","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint32_dec_le",U32_LE,"uint8",new String[]{"uint32","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_system_platform_nbits",PLATFORM_BITS,"tobject",new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_string_push",STR_PUSH,"object",new String[]{"object","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_mk",STR_LIST,"object",new String[]{"tobject"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_string_utf8_get_fast",STR_GET,"uint32",new String[]{"object","tobject","erased"},new boolean[]{true,true,false}));
        register(registry,new ExternSpec("lean_string_utf8_next_fast",STR_NEXT,"tagged",new String[]{"object","tobject","erased"},new boolean[]{true,true,false}));
        register(registry,new ExternSpec("lean_string_append",STR_APPEND,"object",new String[]{"object","object"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_string_utf8_byte_size",STR_SIZE,"tagged",new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_array_mk",ARRAY_MK,"object",new String[]{"erased","tobject"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_array_get_size",ARRAY_SIZE,"tagged",new String[]{"erased","object"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_array_fget_borrowed",ARRAY_GET,"tobject",new String[]{"erased","object","tobject","erased"},new boolean[]{false,true,true,false}));
        register(registry,new ExternSpec("lean_get_stdout",GET_STDOUT,"object",new String[]{"void"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_panic_fn_borrowed",PANIC,"tobject",new String[]{"erased","tobject","object"},new boolean[]{false,true,false}));
        register(registry,new ExternSpec("lean_st_mk_ref",REF_MK,"tobject",
                new String[]{"erased","erased","tobject","void"},new boolean[]{false,false,false,false}));
        register(registry,new ExternSpec("lean_st_ref_get",REF_GET,"tobject",
                new String[]{"erased","erased","tobject","void"},new boolean[]{false,false,true,false}));
        register(registry,new ExternSpec("lean_st_ref_set",REF_SET,"tagged",
                new String[]{"erased","erased","tobject","tobject","void"},new boolean[]{false,false,true,false,false}));
        register(registry,new ExternSpec("lean_st_ref_swap",REF_SWAP,"tobject",
                new String[]{"erased","erased","tobject","tobject","void"},new boolean[]{false,false,true,false,false}));
        register(registry,new ExternSpec("lean_st_ref_take",REF_TAKE,"tobject",
                new String[]{"erased","erased","tobject","void"},new boolean[]{false,false,true,false}));
        register(registry,new ExternSpec("lean_st_ref_ptr_eq",REF_PTR_EQ,"uint8",
                new String[]{"erased","erased","tobject","tobject","void"},new boolean[]{false,false,true,true,false}));
        register(registry,new ExternSpec("lean_mk_empty_array_with_capacity",ARRAY_EMPTY,"object",
                new String[]{"erased","tobject"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_array_push",ARRAY_PUSH,"object",
                new String[]{"erased","object","tobject"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_array_pop",ARRAY_POP,"object",
                new String[]{"erased","object"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_array_size",ARRAY_USIZE,"usize",
                new String[]{"erased","object"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_array_fget",ARRAY_FGET,"tobject",
                new String[]{"erased","object","tobject","erased"},new boolean[]{false,true,true,false}));
        register(registry,new ExternSpec("lean_array_uget",ARRAY_UGET,"tobject",
                new String[]{"erased","object","usize","erased"},new boolean[]{false,true,false,false}));
        register(registry,new ExternSpec("lean_array_uget_borrowed",ARRAY_UGET_BORROWED,"tobject",
                new String[]{"erased","object","usize","erased"},new boolean[]{false,true,false,false}));
        register(registry,new ExternSpec("lean_array_fset",ARRAY_FSET,"object",
                new String[]{"erased","object","tobject","tobject","erased"},new boolean[]{false,false,true,false,false}));
        register(registry,new ExternSpec("lean_array_uset",ARRAY_USET,"object",
                new String[]{"erased","object","usize","tobject","erased"},new boolean[]{false,false,false,false,false}));
        register(registry,new ExternSpec("lean_array_fswap",ARRAY_SWAP,"object",
                new String[]{"erased","object","tobject","tobject","erased","erased"},new boolean[]{false,false,true,true,false,false}));
        register(registry,new ExternSpec("lean_array_to_list",ARRAY_LIST,"tobject",
                new String[]{"erased","object"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_mk_array",ARRAY_REPLICATE,"object",
                new String[]{"erased","tobject","tobject"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_string_utf8_at_end",STR_END,"uint8",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_utf8_get",STR_SAFE_GET,"uint32",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_utf8_next",STR_SAFE_NEXT,"tobject",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_utf8_prev",STR_PREV,"tobject",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_is_valid_pos",STR_VALID,"uint8",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_utf8_extract",STR_EXTRACT,"object",
                new String[]{"object","tobject","tobject"},new boolean[]{true,true,true}));
        register(registry,new ExternSpec("lean_string_dec_eq",STR_EQ,"uint8",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_dec_lt",STR_LT,"uint8",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_compare",STR_COMPARE,"uint8",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_get_byte_fast",STR_BYTE,"uint8",
                new String[]{"object","tobject","erased"},new boolean[]{true,false,false}));
        register(registry,new ExternSpec("lean_string_contains",STR_CONTAINS,"uint8",
                new String[]{"object","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_length",STR_LENGTH,"tobject",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_string_utf8_set",STR_SET,"object",
                new String[]{"object","tobject","uint32"},new boolean[]{false,true,false}));
        register(registry,new ExternSpec("lean_string_utf8_set",STR_POS_SET,"object",
                new String[]{"object","tobject","uint32","erased"},new boolean[]{false,false,false,false}));
        register(registry,new ExternSpec("lean_nat_dec_le",NAT_LE,"uint8",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_nat_log2",NAT_LOG2,"tobject",
                new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_nat_lor",NAT_OR,"tobject",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_nat_shiftl",NAT_SHL,"tobject",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_nat_shiftr",NAT_SHR,"tobject",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_task_map",TASK_MAP,"object",
                new String[]{"erased","erased","tobject","object","tobject","uint8"},
                new boolean[]{false,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_task_pure",TASK_PURE,"object",
                new String[]{"erased","tobject"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_task_get_own",TASK_GET,"tobject",
                new String[]{"erased","object"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_io_promise_new",PROMISE_NEW,"tobject",
                new String[]{"erased","erased","void"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_io_promise_resolve",PROMISE_RESOLVE,"tagged",
                new String[]{"erased","tobject","tobject","void"},new boolean[]{false,false,true,false}));
        register(registry,new ExternSpec("lean_io_promise_result_opt",PROMISE_RESULT,"object",
                new String[]{"erased","tobject"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_task_bind",TASK_BIND,"object",
                new String[]{"erased","erased","object","object","tobject","uint8"},new boolean[]{false,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_io_map_task",IO_TASK_MAP,"object",
                new String[]{"erased","erased","object","object","tobject","uint8","void"},new boolean[]{false,false,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_io_bind_task",IO_TASK_BIND,"object",
                new String[]{"erased","erased","object","object","tobject","uint8","void"},new boolean[]{false,false,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_io_get_task_state",TASK_STATE,"uint8",
                new String[]{"erased","object","void"},new boolean[]{false,true,false}));
        register(registry,new ExternSpec("lean_io_wait",TASK_WAIT,"tobject",
                new String[]{"erased","object","void"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_io_cancel",TASK_CANCEL,"tagged",
                new String[]{"erased","object","void"},new boolean[]{false,true,false}));
        register(registry,new ExternSpec("lean_io_check_canceled",TASK_CANCELED,"uint8",
                new String[]{"void"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_option_get_or_block",OPTION_BLOCK,"tobject",
                new String[]{"erased","erased","tobject"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_task_spawn",TASK_SPAWN,"object",
                new String[]{"erased","tobject","tobject"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_io_as_task",IO_AS_TASK,"object",
                new String[]{"erased","object","tobject","void"},new boolean[]{false,false,false,false}));
        register(registry,new ExternSpec("lean_array_get",ARRAY_CHECKED_GET,"tobject",
                new String[]{"erased","tobject","object","tobject"},new boolean[]{false,true,true,true}));
        register(registry,new ExternSpec("lean_array_get_borrowed",ARRAY_CHECKED_BORROWED,"tobject",
                new String[]{"erased","tobject","object","tobject"},new boolean[]{false,true,true,true}));
        register(registry,new ExternSpec("lean_io_initializing",IO_INITIALIZING,"uint8",
                new String[]{"void"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_usize_dec_lt",USIZE_LT,"uint8",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_add",USIZE_ADD,"usize",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_dec_eq",USIZE_EQ,"uint8",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_sub",USIZE_SUB,"usize",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_to_nat",USIZE_TO_NAT,"tobject",
                new String[]{"usize"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_usize_shift_right",USIZE_SHR,"usize",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_shift_left",USIZE_SHL,"usize",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_land",USIZE_AND,"usize",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint8_to_nat",U8_NAT,"tagged",
                new String[]{"uint8"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint8_dec_eq",U8_EQ,"uint8",
                new String[]{"uint8","uint8"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint8_land",U8_AND,"uint8",
                new String[]{"uint8","uint8"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint8_dec_le",U8_LE,"uint8",
                new String[]{"uint8","uint8"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint32_of_nat",U32_FROM_NAT,"uint32",
                new String[]{"tobject","erased"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_uint32_to_uint8",U32_TO_U8,"uint8",
                new String[]{"uint32"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint32_add",U32_ADD,"uint32",
                new String[]{"uint32","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_dec_le",USIZE_LE,"uint8",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_mul",USIZE_MUL,"usize",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_hash",STR_HASH,"uint64",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_profileit",PROFILE_IT,"tobject",
                new String[]{"erased","object","object","tobject","tobject"},new boolean[]{false,true,true,false,false}));
        register(registry,new ExternSpec("lean_expr_data",EXPR_CACHE,"uint64",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_expr_mk_data",EXPR_DATA,"uint64",
                new String[]{"uint64","tobject","uint32","uint8","uint8","uint8","uint8"},
                new boolean[]{false,false,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_expr_mk_app_data",EXPR_APP_DATA,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_level_mk_data",LEVEL_DATA,"uint64",
                new String[]{"uint64","tobject","uint8","uint8"},new boolean[]{false,false,false,false}));
        register(registry,new ExternSpec("lean_uint8_to_uint64",U8_TO_U64,"uint64",
                new String[]{"uint8"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint32_to_uint64",U32_TO_U64,"uint64",
                new String[]{"uint32"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_usize_to_uint64",USIZE_TO_U64,"uint64",
                new String[]{"usize"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_bool_to_uint64",BOOL_U64,"uint64",
                new String[]{"uint8"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_add",U64_ADD,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_sub",U64_SUB,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_mul",U64_MUL,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_div",U64_DIV,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_mod",U64_MOD,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_land",U64_AND,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_lor",U64_OR,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_complement",U64_NOT,"uint64",
                new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_neg",U64_NEG,"uint64",
                new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_log2",U64_LOG2,"uint64",
                new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_shift_left",U64_SHL,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_dec_le",U64_LE,"uint8",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_mix_hash",U64_MIX,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_of_nat",U64_NAT,"uint64",
                new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_uint64_of_nat",U64_NAT,"uint64",
                new String[]{"tobject","erased"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_uint64_shift_right",U64_SHR,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_xor",U64_XOR,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_to_uint32",U64_TO_U32,"uint32",
                new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_to_usize",U64_USIZE,"usize",
                new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_dec_lt",U64_LT,"uint8",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_dec_eq",U64_EQ,"uint8",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_of_nat_mk",U64_OWNED_NAT,"uint64",
                new String[]{"tobject"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_byte_array_mk",BYTE_MK,"object",
                new String[]{"object"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_byte_array_fget",BYTE_GET,"uint8",
                new String[]{"object","tobject","erased"},new boolean[]{true,true,false}));
        register(registry,new ExternSpec("lean_byte_array_size",BYTE_SIZE,"tagged",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_byte_array_push",BYTE_PUSH,"object",
                new String[]{"object","uint8"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_ptr_addr",POINTER_IDENTITY,"usize",
                new String[]{"erased","tobject"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_nat_to_int",INT_OF_NAT,"tobject",
                new String[]{"tobject"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_int_neg_succ_of_nat",INT_NEG_SUCC,"tobject",
                new String[]{"tobject"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_int_neg",INT_NEG,"tobject",
                new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_nat_abs",INT_ABS,"tobject",
                new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_int_add",INT_ADD,"tobject",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_int_sub",INT_SUB,"tobject",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_int_dec_eq",INT_EQ,"uint8",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_int_dec_lt",INT_LT,"uint8",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_int_dec_le",INT_LE,"uint8",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_name_eq",NAME_EQ,"uint8",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_get_githash",BUILD_GITHASH,"object",
                new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_system_platform_target",BUILD_TARGET,"object",
                new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_string_memcmp",STR_MEMCMP,"uint8",
                new String[]{"object","object","tobject","tobject","tobject","erased","erased"},new boolean[]{true,true,true,true,true,false,false}));
        register(registry,new ExternSpec("lean_substring_beq",STR_SUBSTRING_EQ,"uint8",
                new String[]{"object","object"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_posof",STR_POS_OF,"tobject",
                new String[]{"object","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_offsetofpos",STR_OFFSET_OF_POS,"tobject",
                new String[]{"object","tobject"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_pushn",STR_PUSHN,"object",
                new String[]{"object","uint32","tobject"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_float_of_bits",FLOAT_BITS,"float",new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_to_float",FLOAT_U64,"float",new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_float_sub",FLOAT_SUB,"float",new String[]{"float","float"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float_mul",FLOAT_MUL,"float",new String[]{"float","float"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float_div",FLOAT_DIV,"float",new String[]{"float","float"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float_beq",FLOAT_EQ,"uint8",new String[]{"float","float"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float_decLt",FLOAT_LT,"uint8",new String[]{"float","float"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float_to_string",FLOAT_STRING,"object",new String[]{"float"},new boolean[]{false}));
        registry.replaceAll((symbol,entries)->Collections.unmodifiableList(entries));
        return Collections.unmodifiableMap(registry);
    }
    private static void register(Map<String,List<ExternSpec>> registry,ExternSpec spec) {
        registry.computeIfAbsent(spec.symbol,ignored->new ArrayList<>()).add(spec);
    }
    private static Object externSymbol(Map<String,Object> declaration) {
        List<Object> entries=list(map(declaration.get("ext")).get("entries"));
        if(entries.isEmpty()) throw error("Missing extern");
        Map<String,Object> entry=null;
        for(Object raw:entries) {
            Map<String,Object> candidate=map(raw);
            if(candidate.size()!=1) throw error("Invalid extern entry");
            String kind=candidate.keySet().iterator().next(); Map<String,Object> data=map(candidate.get(kind));
            String backend=name(data.get("backend"));
            if(backend.equals("all")||backend.equals("c")) {
                if(!kind.equals("standard")) throw error("Inline extern outside baseline profile");
                entry=data; break;
            }
        }
        if(entry==null) throw error("No supported extern backend");
        return entry.get("fn");
    }
    private static ExternSpec resolveExtern(Map<String,Object> declaration) {
        Object symbol=externSymbol(declaration);
        List<ExternSpec> allowed=EXTERNS.get(symbol);
        if(allowed==null) throw error("Unsupported baseline extern: "+symbol);
        for(ExternSpec spec:allowed) if(spec.matches(declaration)) return spec;
        throw error("Captured extern ABI mismatch: "+symbol);
    }
    /** Research-only validation; known ABI does not imply executable coverage. */
    public static String validateExternAbi(Map<String,Object> exportedRow) {
        require("decl".equals(exportedRow.get("kind")),"Expected extern declaration row");
        return resolveExtern(map(map(exportedRow.get("ir")).get("extern"))).symbol;
    }

    /** Kind-specific metadata owns no guest values. Mutable state is branch-local;
     * immutable provenance can share. Ordinary constructors allocate no metadata. */
    private interface NodeMetadata {
        // Metadata owns no guest values. Each mutable kind must explicitly copy.
        NodeMetadata copyForFork(Object childOwner);
    }
    /** Nonretaining shared namespace: never reuse an observed identity word. */
    private static final class PointerAllocator {
        final AtomicLong next;
        PointerAllocator(long first) {
            require(first!=0&&(first&7)==0,"Invalid pointer identity allocator seed");
            next=new AtomicLong(first);
        }
        long allocate() {
            while(true) {
                long word=next.get();
                require(word!=0,"Pointer identity namespace exhausted");
                if(next.compareAndSet(word,word+8)) return word;
            }
        }
    }
    private static final PointerAllocator POINTER_WORDS=new PointerAllocator(8);
    /** Owns only a scalar token, an opaque branch token and kind metadata. */
    private static final class PointerMetadata implements NodeMetadata {
        final long word;
        final Object owner;
        final NodeMetadata inner;
        PointerMetadata(long word,Object owner,NodeMetadata inner) {
            this.word=word; this.owner=owner; this.inner=inner;
        }
        public PointerMetadata copyForFork(Object childOwner) {
            return new PointerMetadata(word,childOwner,inner==null?null:inner.copyForFork(childOwner));
        }
    }
    /** Immutable monotone sharing marker; inner kind state owns no guest values.
     * PointerMetadata stays outermost so its word/branch guard remains visible. */
    private static final class SharingMetadata implements NodeMetadata {
        final NodeMetadata inner;
        SharingMetadata(NodeMetadata inner) { this.inner=inner; }
        public SharingMetadata copyForFork(Object childOwner) {
            return inner==null?this:new SharingMetadata(inner.copyForFork(childOwner));
        }
    }
    private static final SharingMetadata LOGICAL_MT=new SharingMetadata(null);
    private static NodeMetadata sharingMetadata(Node node) {
        return node.metadata instanceof PointerMetadata?((PointerMetadata)node.metadata).inner:node.metadata;
    }
    private static boolean logicalMT(Node node) { return sharingMetadata(node) instanceof SharingMetadata; }
    private static boolean exclusive(Node node) { return node.rc==1&&!logicalMT(node); }
    private static boolean refMaybeMT(Node node) { return node.rc==0||logicalMT(node); }
    private static NodeMetadata kindMetadata(Node node) {
        NodeMetadata metadata=sharingMetadata(node);
        return metadata instanceof SharingMetadata?((SharingMetadata)metadata).inner:metadata;
    }
    /** Pinned mark_mt owning-edge walk, independent of positive owner counts.
     * Pending runtime Tasks start MT; the only ST Task shape is ready.
     * Mark before descending so cycles and duplicate edges terminate. */
    private void markLogicalMT(Object value) {
        validateHostObject(value);
        if(!(value instanceof Node)) return;
        Node root=(Node)value;
        if(root.rc==0||logicalMT(root)) return;
        ArrayDeque<Node> todo=new ArrayDeque<>(); todo.push(root);
        while(!todo.isEmpty()) {
            Node current=todo.pop(); validateHostObject(current);
            if(current.rc==0||logicalMT(current)) continue;
            if(current.readyTask) readyTaskNode(current);
            NodeMetadata old=sharingMetadata(current);
            NodeMetadata marked=old==null?LOGICAL_MT:new SharingMetadata(old);
            if(current.metadata instanceof PointerMetadata) {
                PointerMetadata observed=(PointerMetadata)current.metadata;
                current.metadata=new PointerMetadata(observed.word,observed.owner,marked);
            } else current.metadata=marked;
            int live=current.array?arrayState(current).size:current.fields.length;
            for(int i=0;i<live;i++) {
                Object child=current.fields[i];
                // Only Ref.take's empty cell may have an absent owning slot.
                if(child==null) { require(current.ref,"Absent value in MT owning-edge walk"); continue; }
                validateHostObject(child);
                if(child instanceof Node) todo.push((Node)child);
            }
        }
    }
    private void checkPointerOwner(Node node) {
        if(node.metadata instanceof PointerMetadata)
            require(((PointerMetadata)node.metadata).owner==runtimeIdentity,"Pointer-observed object belongs to another interpreter");
    }
    private long pointerWord(Object value) {
        if(value instanceof Long&&((Long)value)>=0) return (((Long)value)<<1)|1;
        require(value instanceof Node,"Pointer identity supports only Nodes and canonical nonnegative Long immediates");
        Node node=node(value);
        require(node.rc>=0,"Invalid pointer object reference count");
        if(node.metadata instanceof PointerMetadata) return ((PointerMetadata)node.metadata).word;
        long word=POINTER_WORDS.allocate();
        node.metadata=new PointerMetadata(word,runtimeIdentity,node.metadata);
        return word;
    }
    private void pointerIdentity(Function function,int[] slots,PreparedBody prepared,Expr site) {
        require(prepared!=null&&prepared.pointerSites!=null&&prepared.pointerSites.contains(site)
                &&site.op==FAP&&site.target==function&&site.args==slots&&function.intrinsic==POINTER_IDENTITY,
                "Pointer identity requires the exact certified FAP site");
        require(ERASED.equals(obj(slots[0])),"Pointer identity erased parameter requires erased placeholder");
        scalarResult=pointerWord(obj(slots[1]));
    }
    private static final class ArrayState implements NodeMetadata {
        int size;
        ArrayState(int size) { this.size=size; }
        public ArrayState copyForFork(Object childOwner) { return new ArrayState(size); }
    }
    private static final class ByteArrayState implements NodeMetadata {
        int size;
        ByteArrayState(int size) { this.size=size; }
        public ByteArrayState copyForFork(Object childOwner) { return new ByteArrayState(size); }
    }
    private static boolean isByteArray(Node value) { return kindMetadata(value) instanceof ByteArrayState; }
    public static final class Node {
        public int tag, rc=1;
        public final Object[] fields;
        public final byte[] scalars;
        private Function closure;
        // Kind metadata: Generation for closures, ArrayState for arrays, otherwise
        // null. Lazy sharing/pointer wrappers preserve it without owning guest values.
        private NodeMetadata metadata;
        private boolean dead;
        private boolean array;
        private boolean ref;
        private boolean readyTask;
        /** Logical live size; fields.length is capacity and spare slots are null. */
        public int arraySize() {
            require(array,"Expected Array"); return ((ArrayState)kindMetadata(this)).size;
        }
        public int byteArraySize() {
            require(isByteArray(this),"Expected ByteArray"); return ((ByteArrayState)kindMetadata(this)).size;
        }
        Node(int tag, int size, int scalarBytes) {
            this.tag=tag; fields=new Object[size]; scalars=new byte[scalarBytes];
        }
        private Node(int tag,Object[] fields,int scalarBytes) {
            this.tag=tag; this.fields=fields; scalars=new byte[scalarBytes];
        }
    }
    /** Trusted-host source boundary, not a digest verifier. The adapter supplies
     * a lightweight immutable accepted catalogue/lease identity, verifies raw
     * bytes and extraction against it, then issues headers and supplies rows.
     * Do not pass a full parsed catalogue here or infer authority from a hash. */
    public static final class SourceBinding {
        private final Object acceptedCatalogueSnapshot;
        public SourceBinding(Object acceptedCatalogueSnapshot) {
            require(acceptedCatalogueSnapshot!=null,"Actual accepted catalogue snapshot required");
            this.acceptedCatalogueSnapshot=acceptedCatalogueSnapshot;
        }
        public Header header(Map<String,Object> declarationHeaderRow,String originalSha256) {
            return new Header(this,declarationHeaderRow,originalSha256);
        }
        public Object acceptedCatalogueSnapshot() { return acceptedCatalogueSnapshot; }
    }
    /** Immutable original ABI issued by one actual trusted source binding.
     * A supplied SHA is descriptive; the source adapter authenticates bytes. */
    public static final class Header {
        private final SourceBinding source;
        private final String originalSha256,kind,resultType;
        private final Object exactName;
        private final int[] params;
        private final String[] paramTypes;
        private final boolean[] borrowed;
        private final Map<String,Object> declaration,evidence;
        private Header(SourceBinding source,Map<String,Object> row,String digest) {
            require(row!=null&&"decl".equals(row.get("kind")),"Expected declaration header row");
            require(digest!=null&&digest.matches("[0-9a-f]{64}"),"Expected original SHA-256 identity");
            this.source=source; originalSha256=digest;
            exactName=frozenName(row.get("name")); Interpreter.name(exactName);
            Map<String,Object> ir=map(row.get("ir"));
            require(ir.size()==1&&(ir.containsKey("fdecl")||ir.containsKey("extern")),"Invalid declaration header kind");
            kind=ir.containsKey("extern")?"extern":"fdecl";
            Map<String,Object> raw=map(ir.get(kind)),metadata=new LinkedHashMap<>(raw);
            require(exactName.equals(frozenName(raw.get("f"))),"Declaration Name differs from exported row Name");
            metadata.remove("body");
            declaration=map(frozenMetadata(metadata));
            params=Interpreter.params(raw.get("xs"));
            List<Object> xs=list(raw.get("xs")); paramTypes=new String[params.length]; borrowed=new boolean[params.length];
            Set<Integer> seen=new HashSet<>();
            for(int i=0;i<params.length;i++) {
                mark(seen,params[i]); Map<String,Object> parameter=map(xs.get(i));
                paramTypes[i]=metadataType(parameter.get("ty"));
                require(parameter.get("borrow") instanceof Boolean,"Invalid original parameter borrow flag");
                borrowed[i]=(Boolean)parameter.get("borrow");
            }
            resultType=metadataType(raw.get("type"));
            Map<String,Object> selected=new LinkedHashMap<>();
            for(String key:new String[]{"runtime","dependencies","redirect","sourceLocal","sourceModule"})
                if(row.containsKey(key)) selected.put(key,row.get(key));
            evidence=map(frozenMetadata(selected));
            if(evidence.containsKey("runtime")) {
                Map<String,Object> runtime=map(evidence.get("runtime"));
                if("initialized".equals(runtime.get("role"))) {
                    require(params.length==0,"Initialized global must be nullary");
                    Interpreter.name(frozenName(runtime.get("initializer")));
                }
            }
        }
        public SourceBinding source() { return source; }
        public Object name() { return exactName; }
        public String originalSha256() { return originalSha256; }
        public String kind() { return kind; }
        public int[] params() { return params.clone(); }
        public String[] paramTypes() { return paramTypes.clone(); }
        public boolean[] borrowed() { return borrowed.clone(); }
        public String resultType() { return resultType; }
        public Map<String,Object> metadata() { return evidence; }
        private boolean sameOriginalHeader(Header other) {
            return source==other.source&&exactName.equals(other.exactName)&&kind.equals(other.kind)
                    &&declaration.equals(other.declaration)&&evidence.equals(other.evidence);
        }
        private boolean initialized() {
            return evidence.containsKey("runtime")&&"initialized".equals(map(evidence.get("runtime")).get("role"));
        }
    }
    private static Object frozenMetadata(Object value) {
        if(value==null||value instanceof String||value instanceof Boolean||value instanceof Long
                ||value instanceof Integer||value instanceof Short||value instanceof Byte||value instanceof BigInteger) return value;
        if(value instanceof List) {
            List<Object> out=new ArrayList<>();
            for(Object item:(List<?>)value) out.add(frozenMetadata(item));
            return Collections.unmodifiableList(out);
        }
        if(value instanceof Map) {
            Map<String,Object> out=new LinkedHashMap<>();
            for(Map.Entry<?,?> entry:((Map<?,?>)value).entrySet()) {
                require(entry.getKey() instanceof String,"Invalid metadata key");
                out.put((String)entry.getKey(),frozenMetadata(entry.getValue()));
            }
            return Collections.unmodifiableMap(out);
        }
        throw error("Mutable or unsupported declaration metadata");
    }
    private static String metadataType(Object value) {
        require(value instanceof String,"Unsupported structured or malformed IR metadata type");
        String type=(String)value;
        switch(type) {
            case "object": case "tobject": case "tagged": case "erased": case "void":
            case "uint8": case "uint16": case "uint32": case "uint64": case "usize":
            case "float": case "float32": return type;
            default: throw error("Unknown IR metadata type: "+type);
        }
    }
    private static int metadataLane(String raw) {
        if(raw.equals("uint16")||raw.equals("float32")) return -1;
        return type(raw);
    }
    /** Source-local graph identity, never a native pointer or runtime Node. */
    public static final class GraphRef {
        private final long sourceId;
        public GraphRef(long sourceId) {
            require(sourceId>=0,"Negative prepared graph source ID"); this.sourceId=sourceId;
        }
        public long sourceId() { return sourceId; }
    }
    /** Explicit signed logical Int metadata for selected-owner import only.
     * This is data transport, not UInt64 reinterpretation or Int arithmetic. */
    public static final class GraphInt {
        private final BigInteger value;
        private final Object runtimeValue;
        public GraphInt(BigInteger exactSignedValue) {
            require(exactSignedValue!=null&&exactSignedValue.getClass()==BigInteger.class,
                    "Exact immutable BigInteger required for GraphInt");
            value=exactSignedValue;
            runtimeValue=value.compareTo(BigInteger.valueOf(Long.MIN_VALUE))>=0&&value.compareTo(SMALL_MAX)<=0
                    ?Long.valueOf(value.longValue()):value;
        }
        public BigInteger value() { return value; }
    }
    /** Immutable source metadata. Numeric positive RC is descriptive, never a
     * destination owner count. PreparedGraph chooses the explicit import profile. */
    public static final class ImportNode {
        private static final int CONSTRUCTOR=0, ARRAY=1, REF=2, CLOSURE=3, BYTE_ARRAY=4;
        private final long sourceId;
        private final int sourceRC,kind,tag;
        private final Object[] fields;
        private final byte[] scalars;
        private final Header header;
        private ImportNode(long id,int sourceRC,int kind,int tag,Object[] fields,byte[] scalars,Header header) {
            require(id>=0,"Negative prepared graph source ID");
            require(sourceRC>=0,"Negative prepared graph source reference count");
            require(fields!=null&&scalars!=null,"Explicit prepared graph payload required");
            this.sourceId=id; this.sourceRC=sourceRC; this.kind=kind; this.tag=tag;
            this.fields=graphValues(fields); this.scalars=scalars.clone(); this.header=header;
        }
        public long sourceId() { return sourceId; }
        public int sourceRC() { return sourceRC; }
        public static ImportNode ctor(long id,int sourceRC,int tag,Object[] fields,byte[] scalars) {
            require(tag>=0&&tag<=243,"Prepared constructor tag outside Lean constructor domain");
            require(fields!=null&&fields.length<256&&scalars!=null&&scalars.length<1024,
                    "Prepared constructor payload outside Lean limits");
            require(fields.length!=0||scalars.length!=0,"Nullary scalar constructor must use an immediate Long");
            return new ImportNode(id,sourceRC,CONSTRUCTOR,tag,fields,scalars,null);
        }
        public static ImportNode array(long id,int sourceRC,Object[] elements) {
            require(elements!=null&&elements.length<=MAX_IMPORT_EDGES,"Prepared array outside research limits");
            return new ImportNode(id,sourceRC,ARRAY,246,elements,new byte[0],null);
        }
        public static ImportNode byteArray(long id,int sourceRC,byte[] liveBytes) {
            require(liveBytes!=null&&liveBytes.length<=MAX_BYTE_CAPACITY,"Prepared ByteArray outside byte capacity limit");
            return new ImportNode(id,sourceRC,BYTE_ARRAY,248,new Object[0],liveBytes,null);
        }
        public static ImportNode ref(long id,int sourceRC,Object value) {
            return new ImportNode(id,sourceRC,REF,253,new Object[]{value},new byte[0],null);
        }
        public static ImportNode closure(long id,int sourceRC,Header header,Object[] captures) {
            require(header!=null,"Actual prepared closure Header required");
            return new ImportNode(id,sourceRC,CLOSURE,245,captures,new byte[0],header);
        }
    }
    /** Trusted adapter's accepted state recipe, not cryptographic admission.
     * Source/state tokens must be lightweight immutable authority/lease tokens.
     * Arrays and byte payloads are copied; no existing runtime Nodes are input.
     * The default constructor accepts only source RC0 and nonnegative carriers.
     * selectedOwners explicitly recomputes positive counts and permits GraphInt.
     * Persistence comes from trusted source metadata; it does not make refs
     * immutable, and neither profile authenticates caller-supplied state facts. */
    public static final class PreparedGraph {
        private final SourceBinding binding;
        private final Object acceptedStateToken;
        private final ImportNode[] nodes;
        private final Header[] globals;
        private final Object[] globalValues,ownedRoots;
        private final boolean selectedOwners;
        public PreparedGraph(SourceBinding binding,Object acceptedStateToken,ImportNode[] nodes,
                             Header[] globals,Object[] globalValues,Object[] ownedRoots) {
            this(binding,acceptedStateToken,nodes,globals,globalValues,ownedRoots,false);
        }
        public static PreparedGraph selectedOwners(SourceBinding binding,Object acceptedStateToken,ImportNode[] nodes,
                                                    Header[] globals,Object[] globalValues,Object[] ownedRoots) {
            return new PreparedGraph(binding,acceptedStateToken,nodes,globals,globalValues,ownedRoots,true);
        }
        private PreparedGraph(SourceBinding binding,Object acceptedStateToken,ImportNode[] nodes,
                              Header[] globals,Object[] globalValues,Object[] ownedRoots,boolean selectedOwners) {
            require(binding!=null&&acceptedStateToken!=null,"Actual accepted source/state tokens required");
            require(nodes!=null&&globals!=null&&globalValues!=null&&ownedRoots!=null,
                    "Explicit prepared graph tables and roots required");
            require(nodes.length<=MAX_IMPORT_NODES,"Prepared graph exceeds research node limit");
            require(globals.length<=MAX_IMPORT_ROOTS&&ownedRoots.length<=MAX_IMPORT_ROOTS,"Prepared graph exceeds root/global limit");
            require(globals.length==globalValues.length,"Prepared global table length mismatch");
            checkGraphProfile(nodes,globalValues,ownedRoots,selectedOwners);
            checkGraphBudget(nodes,globalValues,ownedRoots);
            this.selectedOwners=selectedOwners;
            this.binding=binding; this.acceptedStateToken=acceptedStateToken;
            this.nodes=nodes.clone(); this.globals=globals.clone();
            this.globalValues=graphValues(globalValues); this.ownedRoots=graphValues(ownedRoots);
            for(ImportNode node:this.nodes) require(node!=null,"Null prepared graph node");
            for(Header header:this.globals) require(header!=null,"Null prepared global Header");
        }
    }
    /** Lightweight state provenance only: no source-ID table or graph recipe. */
    private static final class PreparedGlobalSource {
        final SourceBinding binding;
        final Object acceptedStateToken;
        PreparedGlobalSource(SourceBinding binding,Object acceptedStateToken) {
            this.binding=binding; this.acceptedStateToken=acceptedStateToken;
        }
    }
    private static void requireDefaultGraphValues(Object[] values) {
        for(Object value:values) require(!(value instanceof GraphInt),"GraphInt requires selected-owner import profile");
    }
    private static void checkGraphProfile(ImportNode[] nodes,Object[] globals,Object[] roots,boolean selectedOwners) {
        for(ImportNode node:nodes) {
            require(node!=null,"Null prepared graph node");
            require(node.sourceRC>=0,"Negative prepared graph source reference count");
            if(!selectedOwners) {
                require(node.sourceRC==0,"Default prepared graph import requires source RC zero");
                requireDefaultGraphValues(node.fields);
            }
        }
        if(!selectedOwners) { requireDefaultGraphValues(globals); requireDefaultGraphValues(roots); }
    }
    private static long graphBudget(long used,long added,long maximum,String label) {
        if(added<0||used>maximum-added) throw error("Prepared graph exceeds "+label+" budget");
        return used+added;
    }
    private static long graphCarrierBytes(Object value) {
        if(value instanceof GraphRef) return 0;
        if(value instanceof GraphInt) {
            Object carrier=((GraphInt)value).runtimeValue;
            return carrier instanceof Long?8:(((BigInteger)carrier).bitLength()+8L)/8;
        }
        if(value instanceof String) return 3L*((String)value).length(); // conservative UTF-8 bound, no temporary encoding
        if(value instanceof Long&&((Long)value)>=0) return 8;
        if(value!=null&&value.getClass()==BigInteger.class&&((BigInteger)value).signum()>=0)
            return (((BigInteger)value).bitLength()+7L)/8;
        throw error("Prepared graph value outside immutable nonnegative carrier profile");
    }
    private static Object[] graphValues(Object[] values) {
        require(values!=null,"Explicit prepared graph values required");
        require(values.length<=MAX_IMPORT_EDGES,"Prepared graph value array exceeds edge limit");
        long bytes=0;
        for(Object value:values) bytes=graphBudget(bytes,graphCarrierBytes(value),MAX_IMPORT_CARRIER_BYTES,"immutable carrier byte");
        return values.clone();
    }
    private static void checkGraphBudget(ImportNode[] nodes,Object[] globalValues,Object[] roots) {
        long edges=graphBudget(globalValues.length,roots.length,MAX_IMPORT_EDGES,"edge"),scalars=0,carriers=0;
        for(Object value:globalValues) carriers=graphBudget(carriers,graphCarrierBytes(value),MAX_IMPORT_CARRIER_BYTES,"immutable carrier byte");
        for(Object value:roots) carriers=graphBudget(carriers,graphCarrierBytes(value),MAX_IMPORT_CARRIER_BYTES,"immutable carrier byte");
        for(ImportNode node:nodes) {
            require(node!=null,"Null prepared graph node");
            edges=graphBudget(edges,node.fields.length,MAX_IMPORT_EDGES,"edge");
            scalars=graphBudget(scalars,node.scalars.length,MAX_IMPORT_SCALAR_BYTES,"scalar byte");
            for(Object value:node.fields) carriers=graphBudget(carriers,graphCarrierBytes(value),MAX_IMPORT_CARRIER_BYTES,"immutable carrier byte");
        }
    }

    /** Stable callable identity and ABI; executable layout belongs to a Program. */
    static final class Function {
        final String label;
        final int id, resultType, intrinsic;
        final int[] params, paramTypes;
        final Object privateOwner;
        final HostExtern hostExtern;
        final Header header;
        Function(String label,int id,int[] params,int[] paramTypes,int resultType,
                 int intrinsic,HostExtern hostExtern,Object privateOwner) {
            this(label,id,params,paramTypes,resultType,intrinsic,hostExtern,privateOwner,null);
        }
        Function(String label,int id,int[] params,int[] paramTypes,int resultType,
                 int intrinsic,HostExtern hostExtern,Object privateOwner,Header header) {
            this.header=header;
            this.label=label; this.id=id; this.params=params.clone(); this.paramTypes=paramTypes.clone();
            this.resultType=resultType; this.intrinsic=intrinsic;
            this.hostExtern=hostExtern; this.privateOwner=privateOwner;
        }
    }
    /** Source layouts publish after validation; inherited slots share identity.
     * The private map layout below never occupies a Program slot. */
    private static final class PreparedBody {
        final Body body;
        final int width, joinWidth;
        final Set<Expr> pointerSites;
        private PreparedBody(Body runtimeMapBody) {
            body=runtimeMapBody; width=8; joinWidth=0; pointerSites=null;
        }
        PreparedBody(Body body,int width,int joinWidth) {
            this.body=body; this.width=width; this.joinWidth=joinWidth;
            this.pointerSites=certifyPointerSites(body);
        }
    }
    /** Local preparation state, never retained by a published Function or Program. */
    private static final class BodyBuilder {
        int width=1, joinWidth=1;
        Body body;
        BodyBuilder(Function function) {
            for(int param:function.params) width=Math.max(width,param+1);
        }
        PreparedBody finish() { return new PreparedBody(body,width,joinWidth); }
    }
    static final class Expr {
        int op, a,b,tag,size,scalarBytes;
        int[] args;
        Object literal;
        Function target;
    }
    static final class Body {
        int op,a,b,type;
        int[] args,tags;
        Expr expr;
        Body next,body;
        Body[] alternatives;
    }
    private static final PreparedBody TASK_MAP_LAYOUT=taskMapLayout();
    private static PreparedBody taskMapLayout() {
        Body apply=new Body(),wrap=new Body(); apply.op=MAP_APPLY; wrap.op=MAP_WRAP;
        apply.next=wrap; return new PreparedBody(apply);
    }
    /** Identity-only lineage: no function/map/Program references. Binary lifting
     * bounds ancestry checks without retaining every old full image table. */
    private static final class Generation implements NodeMetadata {
        public Generation copyForFork(Object childOwner) { return this; }
        final int depth;
        final Generation[] jumps;
        Generation(Generation parent) {
            depth=parent==null?0:Math.addExact(parent.depth,1);
            jumps=new Generation[depth==0?0:32-Integer.numberOfLeadingZeros(depth)];
            if(jumps.length!=0) jumps[0]=parent;
            for(int i=1;i<jumps.length;i++) jumps[i]=jumps[i-1].jumps[i-1];
        }
        boolean accepts(Generation ancestor) {
            if(ancestor==null||ancestor.depth>depth) return false;
            Generation cursor=this;
            int difference=depth-ancestor.depth,bit=0;
            while(difference!=0) {
                if((difference&1)!=0) cursor=cursor.jumps[bit];
                difference>>>=1; bit++;
            }
            return cursor==ancestor;
        }
    }
    /** Trusted-host export association, not a source-byte or export-attribute
     * verifier. Both original Headers stay unchanged; no executable host code. */
    public static final class GuestExportBinding {
        private final Header origin,target;
        public GuestExportBinding(Header origin,Header target) {
            require(origin!=null&&target!=null,"Actual export origin and target Headers required");
            this.origin=origin; this.target=target;
        }
    }
    public static final class Program {
        final Function[] functions;
        final PreparedBody[] preparedBodies;
        final Map<String,Function> labels;
        final Map<Object,Function> typedNames;
        final Map<String,List<HostExtern>> hostRegistry;
        final Generation generation;
        private final Function[] guestExports;
        private Program(Function[] functions,PreparedBody[] preparedBodies,Map<String,Function> labels,Map<Object,Function> typedNames,
                        Map<String,List<HostExtern>> hostRegistry,Generation generation,Function[] guestExports) {
            this.guestExports=guestExports;
            this.functions=functions; this.preparedBodies=preparedBodies; this.labels=labels; this.typedNames=typedNames;
            this.hostRegistry=hostRegistry; this.generation=generation;
        }
        public int functionId(String label) {
            Function f=labels.get(label);
            if(f==null) throw error("Unknown function: "+label);
            return f.id;
        }
        public int functionId(Header header) {
            require(header!=null,"Actual declaration Header required");
            Function function=typedNames.get(header.exactName);
            require(function!=null&&function.header==header,"Header is not registered in this Program");
            return function.id;
        }
        /** Header metadata is trusted-host input; this does not verify source bytes.
         * Extern metadata currently requires a standard c/all entry. A missing
         * implementation or supported lane does not prevent header registration. */
        public static Program registerHeaders(Program base,Header[] headers) {
            return registerHeaders(base,headers,new HostExtern[0]);
        }
        public static Program registerHeaders(Program base,Header[] headers,HostExtern[] additionalExterns) {
            return registeredHeaders(base,headers,additionalExterns);
        }
        /** Adapter must verify original raw bytes before supplying this parsed row.
         * Dependencies are the exact unique direct non-self FAP/PAP headers. */
        public static Program materialize(Program base,Header target,Map<String,Object> originalRow,Header[] directHeaders) {
            return materializedBody(base,target,originalRow,directHeaders);
        }
        /** Add explicit source-backed implementations for unavailable externs.
         * Caller authenticates export association and original row bytes. This
         * publishes one immutable descendant; rejected batches change nothing. */
        public static Program bindGuestExports(Program base,GuestExportBinding[] bindings) {
            return boundGuestExports(base,bindings);
        }
        public int functionCount() { return functions.length; }
        /** Append-only link against this actual base, preserving every old
         * function identity/ID. Metadata-only input with no new ABI is a no-op. */
        public static Program extend(Program base,List<?> rows) { return extend(base,rows,new HostExtern[0]); }
        public static Program extend(Program base,List<?> rows,HostExtern[] additionalExterns) {
            require(base!=null,"Actual base Program required");
            return link(base,rows,additionalExterns);
        }
    }

    private static Program boundGuestExports(Program base,GuestExportBinding[] bindings) {
        require(base!=null&&bindings!=null,"Actual base Program and explicit export bindings required");
        Function[] targets=base.guestExports.clone(); boolean changed=false;
        for(GuestExportBinding binding:bindings.clone()) {
            require(binding!=null,"Null guest export binding");
            Header origin=binding.origin,target=binding.target;
            Function from=base.functions[base.functionId(origin)],to=base.functions[base.functionId(target)];
            require(origin.kind.equals("extern")&&target.kind.equals("fdecl"),
                    "Guest export requires extern origin and direct fdecl target");
            require(from!=to&&origin.source==target.source,"Guest export source binding differs");
            require(from.params.length>0&&!origin.initialized()&&!target.initialized(),
                    "Nullary or initialized guest exports are outside this profile");
            Object symbol=externSymbol(origin.declaration);
            require(symbol instanceof String&&!((String)symbol).isEmpty()&&((String)symbol).length()<=4096
                    &&((String)symbol).indexOf('\0')<0,"Invalid guest export symbol");
            require(!EXTERNS.containsKey(symbol),"Guest export cannot shadow builtin: "+symbol);
            require(from.hostExtern==null&&!base.hostRegistry.containsKey(symbol),
                    "Guest export conflicts with host extern: "+symbol);
            require(from.intrinsic==0&&to.intrinsic==0&&to.hostExtern==null,"Guest export requires ordinary target code");
            require(origin.resultType.equals(target.resultType)&&Arrays.equals(origin.paramTypes,target.paramTypes)
                    &&Arrays.equals(origin.borrowed,target.borrowed),"Guest export raw ABI mismatch");
            requireExecutableAbi(from); requireExecutableAbi(to);
            require(targets[from.id]==null||targets[from.id]==to,"Guest export binding cannot be replaced");
            if(targets[from.id]==null) { targets[from.id]=to; changed=true; }
        }
        if(!changed) return base;
        return new Program(base.functions,base.preparedBodies,base.labels,base.typedNames,base.hostRegistry,
                           new Generation(base.generation),targets);
    }
    private static void hostExportConflict(Program base,String symbol) {
        if(base==null) return;
        for(int i=0;i<base.guestExports.length;i++) if(base.guestExports[i]!=null)
            require(!symbol.equals(externSymbol(base.functions[i].header.declaration)),
                    "Host extern conflicts with guest export: "+symbol);
    }
    private static Map<String,List<HostExtern>> extendedHostRegistry(Program base,HostExtern[] additional) {
        require(additional!=null,"Explicit host extern registry required");
        Map<String,List<HostExtern>> registry=new HashMap<>();
        for(Map.Entry<String,List<HostExtern>> entry:base.hostRegistry.entrySet())
            registry.put(entry.getKey(),new ArrayList<>(entry.getValue()));
        for(HostExtern descriptor:additional.clone()) {
            require(descriptor!=null,"Null host extern descriptor");
            hostExportConflict(base,descriptor.symbol);
            require(!EXTERNS.containsKey(descriptor.symbol),"Host extern cannot shadow builtin: "+descriptor.symbol);
            List<HostExtern> entries=registry.computeIfAbsent(descriptor.symbol,ignored->new ArrayList<>());
            for(HostExtern old:entries) require(!descriptor.sameAbi(old),"Duplicate host extern ABI: "+descriptor.symbol);
            entries.add(descriptor);
        }
        registry.replaceAll((symbol,entries)->Collections.unmodifiableList(entries));
        return Collections.unmodifiableMap(registry);
    }
    private static Function headerFunction(Header header,int id,Map<String,List<HostExtern>> registry) {
        int[] lanes=new int[header.paramTypes.length];
        for(int i=0;i<lanes.length;i++) lanes[i]=metadataLane(header.paramTypes[i]);
        int intrinsic=0; HostExtern host=null;
        if(header.kind.equals("extern")) {
            Object symbol=externSymbol(header.declaration);
            if(EXTERNS.containsKey(symbol)) {
                for(ExternSpec spec:EXTERNS.get(symbol)) if(spec.matches(header.declaration)) { intrinsic=spec.intrinsic; break; }
            } else if(registry.containsKey(symbol)) {
                for(HostExtern descriptor:registry.get(symbol)) if(descriptor.matches(header.declaration)) { host=descriptor; break; }
            }
        }
        return new Function(name(header.exactName),id,header.params,lanes,metadataLane(header.resultType),
                            intrinsic,host,null,header);
    }
    private static Program registeredHeaders(Program base,Header[] headers,HostExtern[] additional) {
        require(base!=null,"Actual base Program required"); require(headers!=null,"Explicit declaration headers required");
        Map<String,List<HostExtern>> registry=extendedHostRegistry(base,additional);
        Map<Object,Function> byName=new HashMap<>(base.typedNames);
        Map<String,Function> labels=new LinkedHashMap<>(base.labels);
        List<Function> additions=new ArrayList<>();
        for(Header header:headers.clone()) {
            require(header!=null,"Null declaration Header");
            Function old=byName.get(header.exactName);
            if(old!=null) { require(old.header==header,"Conflicting declaration header identity"); continue; }
            String label=name(header.exactName);
            require(!labels.containsKey(label),"Duplicate/ambiguous function name: "+label);
            Function function=headerFunction(header,base.functions.length+additions.size(),registry);
            byName.put(header.exactName,function); labels.put(label,function); additions.add(function);
        }
        if(additions.isEmpty()&&additional.length==0) return base;
        Function[] functions=Arrays.copyOf(base.functions,base.functions.length+additions.size());
        for(Function function:additions) functions[function.id]=function;
        return new Program(functions,Arrays.copyOf(base.preparedBodies,functions.length),
                           Collections.unmodifiableMap(labels),Collections.unmodifiableMap(byName),registry,
                           new Generation(base.generation),Arrays.copyOf(base.guestExports,functions.length));
    }
    private static void directTargets(Body body,Set<Function> targets) {
        if(body==null) return;
        if(body.expr!=null&&(body.expr.op==FAP||body.expr.op==PAP)) targets.add(body.expr.target);
        directTargets(body.next,targets); directTargets(body.body,targets);
        if(body.alternatives!=null) for(Body alternative:body.alternatives) directTargets(alternative,targets);
    }
    private static Program materializedBody(Program base,Header target,Map<String,Object> originalRow,Header[] directHeaders) {
        require(base!=null&&target!=null,"Actual base Program and target Header required");
        int id=base.functionId(target);
        require(base.preparedBodies[id]==null,"Prepared body replacement is not supported");
        require(target.kind.equals("fdecl"),"Only original fdecl bodies can be materialized");
        Header actual=new Header(target.source,originalRow,target.originalSha256);
        require(target.sameOriginalHeader(actual),"Original row differs from issued declaration header");
        require(directHeaders!=null,"Explicit direct declaration headers required");
        Header[] dependencies=directHeaders.clone(); Set<Header> expected=Collections.newSetFromMap(new IdentityHashMap<>());
        for(Header dependency:dependencies) {
            require(dependency!=null&&dependency.source==target.source,"Direct header source binding differs");
            require(dependency!=target&&expected.add(dependency),"Duplicate or self direct header");
        }
        Program staged=registeredHeaders(base,dependencies,new HostExtern[0]);
        Function function=staged.functions[id]; requireExecutableAbi(function);
        BodyBuilder builder=new BodyBuilder(function);
        builder.body=body(map(map(originalRow.get("ir")).get("fdecl")).get("body"),builder,staged.typedNames);
        Set<Function> targets=Collections.newSetFromMap(new IdentityHashMap<>()); directTargets(builder.body,targets);
        targets.remove(function);
        require(targets.size()==expected.size(),"Direct header set differs from original FAP/PAP targets");
        for(Function callee:targets) require(callee.header!=null&&expected.remove(callee.header),
                                             "Original call target differs from supplied direct header identity");
        require(expected.isEmpty(),"Unused direct declaration header");
        validate(function,builder.body);
        PreparedBody[] slots=staged.preparedBodies.clone(); slots[id]=builder.finish();
        return new Program(staged.functions,slots,staged.labels,staged.typedNames,staged.hostRegistry,new Generation(staged.generation),staged.guestExports);
    }

    /** Explicit trusted-host selection of guest producer metadata, not a hash
     * verifier or an assertion about the JVM host's OS or this executable.
     * Contains no catalogue, channel, source binding, or Interpreter owner. */
    public static final class BuildIdentity {
        private static final BuildIdentity LEAN_4331=new BuildIdentity();
        private BuildIdentity() {}
        public static BuildIdentity supportedLean4331() { return LEAN_4331; }
        public String githash() { return "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"; }
        public String target() { return "x86_64-unknown-linux-gnu"; }
    }
    /** Explicit logical synchronous profile; no native manager/thread authority.
     * Pending values and callbacks are enabled only by its completed control
     * protocol, never inferred from initialization or SourceBinding metadata. */
    public static final class TaskRuntime {
        private static final TaskRuntime SYNC=new TaskRuntime();
        private TaskRuntime() {}
        public static TaskRuntime logicalSynchronous() { return SYNC; }
    }
    private static final int PROMISE_KIND=1,TASK_KIND=2;
    /** Kind/branch authority only. Guest values live exclusively in owning
     * Node fields; these metadata contain no registration/callback references. */
    private static final class TaskMetadata implements NodeMetadata {
        final int kind;
        final Object owner;
        int state;
        TaskMetadata(int kind,Object owner,int state) { this.kind=kind; this.owner=owner; this.state=state; }
        public TaskMetadata copyForFork(Object childOwner) { return new TaskMetadata(kind,childOwner,state); }
    }
    private static final class DependencyList { Registration head; }
    private static final class Registration {
        DependencyList list;
        Registration previous,next;
        TaskRecord source,dependent;
    }
    /** All links here are NONOWNING guest references. Keepalive is a real
     * separately counted Task credit, never supplied by registration reachability. */
    private static final class TaskRecord {
        Node task;
        DependencyList dependents=new DependencyList();
        Registration waiting;
        boolean canceled,deactivated,keepalive,bind,io,forward,running;
    }
    private IdentityHashMap<Node,TaskRecord> taskRecords=new IdentityHashMap<>();
    private TaskRecord currentTask;
    /** Explicit disabled-only native profiling gate. Header bytes are
     * authenticated by the trusted source adapter; this checks its pinned role.
     * The policy owns no guest value and retains no Program/catalogue reader. */
    public static final class ProfilingPolicy {
        private final Header getter;
        private ProfilingPolicy(Header getter) { this.getter=getter; }
        public static ProfilingPolicy requireDisabled(Header getter) {
            require(getter!=null&&getter.kind.equals("fdecl")
                    &&getter.originalSha256.equals("697f802be49ca83e350147ca7a564a73e3162beb454ca78d2990455df96796ed"),
                    "Profiling requires the pinned original boxed option getter");
            Object name=Arrays.asList("anonymous");
            for(String segment:new String[]{"_private","Lean","Util","Profile"}) name=Arrays.asList("str",name,segment);
            name=Arrays.asList("num",name,"0");
            for(String segment:new String[]{"Lean","get_profiler","_boxed"}) name=Arrays.asList("str",name,segment);
            require(getter.exactName.equals(frozenName(name))&&getter.params.length==1
                    &&getter.paramTypes[0].equals("object")&&!getter.borrowed[0]&&getter.resultType.equals("tagged"),
                    "Profiling option getter Name or raw ABI differs");
            return new ProfilingPolicy(getter);
        }
    }
    private final ProfilingPolicy profilingPolicy;
    private final TaskRuntime taskRuntime;
    private final BuildIdentity buildIdentity;
    private Program program;
    private Object[] objects=new Object[1024];
    private long[] numbers=new long[1024];
    private Body[] joins=new Body[256];
    private int bp,sp,jbp,jsp;
    private Object result;
    private long scalarResult;
    private Object[] constants;
    private boolean[] constantReady;
    private boolean[] constantRetired;
    private boolean disposed;
    private boolean graphInstalled;
    private boolean initializing;
    private Map<Integer,PreparedGlobalSource> preparedGlobalSources=Collections.emptyMap();
    private boolean closed;
    private boolean untrackedFailure;
    private final Object runtimeIdentity=new Object();
    private Node stdoutRoot;
    private final StringBuilder output=new StringBuilder();
    private WeakReference<String> utf8Key;
    private byte[] utf8Bytes;
    private Object[] releaseWork=new Object[32];
    private int releasePending;
    private Node quietCurrent;
    private int quietFieldCursor;
    private boolean releaseRoot;
    private ReleaseTransaction releaseTransaction;
    /** Explicit finalizer-free root only. Credits are claimed once; current and
     * queued dead shells still own each not-yet-scanned field edge. */
    private static final class ReleaseTransaction {
        Node origin,current;
        int count,fieldCursor,fieldLimit;
        boolean claimed;
    }
    private long callsLeft;
    private final boolean explicit;
    private static final int IDLE=0, RUNNING=1, COMPLETE=2, FAILED=3, HOST_CALL=4, CODE_CALL=5, WAITING=6, HOST_GUEST_RESULT=7;
    private static final int ASSIGN=0, CACHE=1, APPLY=2, ROOT=4;
    private int phase=IDLE, continuationDepth;
    private long instructions;
    private boolean advancing, pendingOwnedResult;
    private Function active, entry;
    private PreparedBody activePrepared;
    private Body pc;
    private Continuation[] continuations;
    private Function applicationTarget;
    private Object[] applicationArgs,applicationSurplus;
    private Object applicationResult;
    private boolean applicationResultOwned,applicationArgumentsOwned;
    private int applicationCaptureCount,applicationRetainedCaptures;
    private void applicationEntry(int kind) {
        if(taskRuntime!=null&&(kind&APPLY)!=0) applicationArgumentsOwned=false;
    }
    private void clearApplication() {
        applicationTarget=null; applicationArgs=null; applicationSurplus=null;
        applicationResult=null; applicationResultOwned=false; applicationArgumentsOwned=false;
        applicationCaptureCount=0; applicationRetainedCaptures=0;
    }
    private HostRequest hostRequest,failedHostRequest;
    private HostGuestPolicy hostGuestPolicy;
    private HostGuestRecord hostGuestRecord;
    private HostCall hostCompletion;
    private RuntimeAction runtimeAction,failedRuntimeAction;
    private static final int ACTION_RELEASE=1,ACTION_DISPOSE=2,ACTION_NATIVE=3,ACTION_HOST=4,ACTION_TASK=5,ACTION_RESOLVE=6,ACTION_RUN_TASK=7,ACTION_PROFILE=8,ACTION_HOST_GUEST=20;
    private static final Body ACTION_BODY=new Body();
    /** Typed ownership/control state, separate from NodeMetadata. The output
     * scratch slot is reserved before callbacks may enter generic AP. */
    private static final class RuntimeAction {
        RuntimeAction parent;
        HostGuestRecord guest;
        int operation,stage,savedSp,slot,dest,kind,cursor,limit,pending;
        Function function;
        Body next;
        Object[] surplus,work,arguments;
        HostCall completion;
        HostRequest request;
        TaskRecord task,scope;
        DependencyList batch;
        Object output,retiring;
        boolean releaseClaimed;
        Node current,origin;
    }
    private RuntimeAction newAction(int operation,Function function,Body next,int dest,int kind,Object[] surplus) {
        int nextSp=Math.addExact(sp,1); require(nextSp<=8_000_000,"Runtime action stack limit");
        ensure(nextSp,jsp);
        RuntimeAction action=new RuntimeAction();
        action.operation=operation; action.function=function; action.next=next; action.dest=dest;
        action.kind=kind; action.surplus=surplus; action.savedSp=sp; action.slot=sp;
        return action;
    }
    private void publishAction(RuntimeAction action) {
        action.parent=runtimeAction; runtimeAction=action; sp=action.savedSp+1; pc=ACTION_BODY;
    }
    private void finishAction(RuntimeAction action,Object value) {
        require(runtimeAction==action,"Runtime action order differs");
        action.output=value;
        int type=action.function==null?OBJ:action.function.resultType;
        long raw=type==OBJ?0:readSavedScalar(value,type);
        objects[action.slot]=null; sp=action.savedSp; runtimeAction=action.parent;
        if((action.kind&ROOT)!=0) {
            if(type==OBJ) result=value; else scalarResult=raw;
            pendingOwnedResult=true; phase=COMPLETE; return;
        }
        if((action.kind&APPLY)!=0) {
            Object answer=type==OBJ?value:boxScalar(raw,type);
            if(action.surplus!=null) {
                try { applyExplicit(answer,action.surplus,action.next,action.dest); }
                catch(Throwable failure) { failedRuntimeAction=action; throw failure; }
                return;
            }
            if(action.dest>=0) objects[action.dest]=answer;
        } else if(action.dest>=0) {
            if(type==OBJ) objects[action.dest]=value; else numbers[action.dest]=raw;
        }
        pc=action.next;
    }
    private void markReleaseClaim(Object value) {
        if(runtimeAction!=null&&runtimeAction.retiring==value) runtimeAction.releaseClaimed=true;
    }
    private boolean beginRelease(Object value,int count,Body next) { return beginRelease(value,count,next,false); }
    private boolean beginRelease(Object value,int count,Body next,boolean budgeted) {
        require(count>=0,"Negative reference decrement");
        validateHostObject(value);
        Node root=value instanceof Node?(Node)value:null;
        if(root==null||root.rc==0||count==0) return false;
        require(count<=root.rc,"Reference count underflow");
        if(count<root.rc) { markReleaseClaim(value); root.rc-=count; releases+=count; return false; }
        int limit=owningFieldCount(root);
        require(limit>=0&&limit<=root.fields.length,"Release field count outside payload");
        if(budgeted) {
            RuntimeAction action=newAction(ACTION_RELEASE,null,next,-1,ASSIGN,null);
            action.origin=root; action.current=root; action.limit=limit; action.work=new Object[32];
            publishAction(action); root.rc=0; root.dead=true; releases+=count; return true;
        }
        // QUIET_COMPLETE/NEEDS_DISPATCH: ordinary destruction uses reusable
        // scratch and no heap continuation. Stop BEFORE a kind finalizer; its
        // caller's exact suffix is already published or remains the IR PC.
        require(quietCurrent==null&&releasePending==0,"Quiet release scratch is already occupied");
        quietCurrent=root; quietFieldCursor=0; markReleaseClaim(value); root.rc=0; root.dead=true; releases+=count;
        while(quietCurrent!=null) {
            if(isPromise(quietCurrent)) {
                RuntimeAction action=newAction(ACTION_RELEASE,null,next,-1,ASSIGN,null);
                Object[] replacement=new Object[32];
                action.origin=root; action.current=quietCurrent; action.limit=owningFieldCount(quietCurrent);
                action.work=releaseWork; action.pending=releasePending;
                publishAction(action); releaseWork=replacement; releasePending=0; quietCurrent=null; quietFieldCursor=0;
                return true;
            }
            if(runtimeTask(quietCurrent)&&quietCurrent.fields[0]==null
                    &&((TaskMetadata)kindMetadata(quietCurrent)).state!=3) retirePendingTask(quietCurrent);
            if(quietCurrent.readyTask&&(!runtimeTask(quietCurrent)||quietCurrent.fields[0]!=null)) {
                require(quietCurrent.fields.length==1||runtimeTask(quietCurrent),"Invalid Task retirement shape");
                Object valueToDrop=quietCurrent.fields[0];
                validateHostObject(valueToDrop);
                Node child=valueToDrop instanceof Node?node(valueToDrop):null;
                quietCurrent.fields[0]=null;
                // A ready Task's nested DEC has no after-suffix. Tail-drain its
                // last-value retirement before the enclosing zero-shell queue.
                if(child!=null&&child.rc!=0) {
                    require(child.rc>0,"Reference count underflow"); child.rc--; releases++;
                    if(child.rc==0) { child.dead=true; quietCurrent=child; quietFieldCursor=0; continue; }
                }
                quietCurrent=releasePending==0?null:takeReleased(); quietFieldCursor=0; continue;
            }
            int size=owningFieldCount(quietCurrent);
            while(quietFieldCursor<size) { releaseField(quietCurrent,quietFieldCursor); quietFieldCursor++; }
            quietCurrent=releasePending==0?null:takeReleased(); quietFieldCursor=0;
        }
        return false;
    }
    private void stepRelease(RuntimeAction action) {
        if(action.stage==0&&isPromise(action.current)) {
            action.output=action.current.fields[0]; action.current.fields[0]=null;
            action.stage=10; action.cursor=action.limit;
            startResolve((Node)action.output,ERASED,ACTION_BODY); return;
        }
        if(action.stage==10) {
            action.stage=11; action.retiring=action.output;
            if(beginRelease(action.output,1,ACTION_BODY)) return;
        }
        if(action.stage==0&&runtimeTask(action.current)&&action.current.fields[0]==null) {
            retirePendingTask(action.current); action.stage=1;
        }
        if(action.stage==0&&action.current.readyTask) {
            // Native Task retirement is a nested DEC, not an edge in the
            // enclosing constructor's zero-shell worklist.
            require(action.current.fields.length==1||runtimeTask(action.current),"Invalid Task retirement shape");
            Object value=action.current.fields[0]; validateHostObject(value);
            Node child=value instanceof Node?node(value):null;
            action.current.fields[0]=null; action.stage=1; action.cursor=action.limit;
            if(child!=null&&child.rc!=0) {
                require(child.rc>0,"Reference count underflow"); child.rc--; releases++;
                if(child.rc==0) {
                    child.dead=true; action.current=child; action.cursor=0;
                    action.limit=owningFieldCount(child); action.stage=0;
                }
            }
            return;
        }
        action.stage=1;
        if(action.cursor<action.limit) {
            Object edge=action.current.fields[action.cursor];
            if(edge instanceof Node) {
                Node child=node(edge);
                if(child.rc!=0) {
                    require(child.rc>0,"Reference count underflow");
                    if(child.rc==1&&action.pending==action.work.length)
                        action.work=Arrays.copyOf(action.work,Math.multiplyExact(action.pending,2));
                    child.rc--; releases++;
                    if(child.rc==0) { child.dead=true; action.work[action.pending++]=child; }
                }
            }
            action.current.fields[action.cursor]=null; action.cursor++;
        } else if(action.pending!=0) {
            Node child=(Node)action.work[action.pending-1]; int limit=owningFieldCount(child);
            require(limit>=0&&limit<=child.fields.length,"Release field count outside payload");
            action.work[--action.pending]=null; action.current=child; action.cursor=0; action.limit=limit; action.stage=0;
        } else finishAction(action,ERASED);
    }
    /** Explicit private-cache owner disposal. External guest owners must be
     * discharged separately; persistent globals and RC cycles are not collected. */
    public void startDispose() {
        explicitOnly(); require(taskRuntime!=null,"Task runtime disposal requires an active profile");
        if(advancing||phase!=IDLE||pendingOwnedResult||untrackedFailure||sp!=0||continuationDepth!=0
                ||runtimeAction!=null||quietCurrent!=null||releasePending!=0||releaseRoot||disposed)
            throw new IllegalStateException("Disposal requires an open idle undisposed runtime");
        RuntimeAction action=newAction(ACTION_DISPOSE,null,null,0,ROOT,null);
        releaseRoot=true; entry=null; result=null; instructions=0; callsLeft=10_000_000; phase=RUNNING; publishAction(action);
    }
    private void stepDispose(RuntimeAction action) {
        if(action.cursor==0) {
            Node old=stdoutRoot; action.retiring=old; action.releaseClaimed=false; stdoutRoot=null; action.cursor++;
            if(old!=null) { beginRelease(old,1,ACTION_BODY); action.releaseClaimed=true; }
        } else if(action.cursor<=constants.length) {
            int index=action.cursor++-1;
            if(constantReady[index]) {
                Object old=constants[index]; action.retiring=old; action.releaseClaimed=false; constants[index]=null; constantReady[index]=false; constantRetired[index]=true;
                if(program.functions[index].resultType==OBJ) { beginRelease(old,1,ACTION_BODY); action.releaseClaimed=true; }
            }
        } else {
            // A finalizer may have initialized a previously untouched closed
            // constant behind the sweep cursor. Own and retire it in another
            // pass; retired slots remain tombstoned throughout callbacks.
            if(stdoutRoot!=null) { action.cursor=0; return; }
            for(int i=0;i<constantReady.length;i++) if(constantReady[i]) { action.cursor=1; return; }
            for(TaskRecord record:taskRecords.values()) if(record.keepalive) { phase=WAITING; return; }
            disposed=true; finishAction(action,ERASED);
        }
    }
    private boolean actionPrimitive(Function function) {
        int op=function.intrinsic;
        return taskRuntime!=null&&(op==PROFILE_IT||taskPrimitive(op)||op==TASK_MAP||op==REF_SET||op==ARRAY_POP||op==ARRAY_FSET||op==ARRAY_USET||op==ARRAY_REPLICATE);
    }
    private Object[] savedArguments(Function function,int[] slots) {
        Object[] args=new Object[slots.length];
        for(int i=0;i<args.length;i++) args[i]=function.paramTypes[i]==OBJ?obj(slots[i]):saveScalar(numbers[bp+slots[i]],function.paramTypes[i]);
        return args;
    }
    private Function profilingGetter(Function function) {
        require(explicit&&taskRuntime!=null&&profilingPolicy!=null,
                "Native profiling requires an active explicit runtime and checked-disabled policy");
        Header getter=profilingPolicy.getter;
        require(function.header!=null&&function.header.source==getter.source,"Profiling getter source binding differs");
        Function target=program.functions[program.functionId(getter)];
        require(target.header==getter&&target.intrinsic==0&&target.hostExtern==null
                &&program.guestExports[target.id]==null,"Profiling getter is not the original guest function");
        return preflightCallable(target,true);
    }
    private void validateProfile(Function function,Object[] args) {
        profilingGetter(function);
        require(args.length==5&&ERASED.equals(args[0]),"Profiling erased parameter required");
        utf8(args[1]); validateHostObject(args[2]); validateHostObject(args[4]);
        Node callback=node(args[3]); require(callback.closure!=null,"Profiling requires a closure"); acceptsClosure(callback);
        Function target=callback.closure; rootEntry(target); requireExecutableAbi(target);
        require(target.resultType==OBJ,"Profiling requires boxed callback result");
        for(int lane:target.paramTypes) require(lane==OBJ,"Profiling requires boxed callback parameters");
        require(callback.fields.length<target.params.length,"Profiling requires an unsaturated callback");
        IdentityHashMap<Node,Integer> credits=new IdentityHashMap<>(); credits.put(callback,1);
        if(args[4] instanceof Node) credits.merge((Node)args[4],1,Integer::sum);
        if(args[2] instanceof Node&&credits.containsKey((Node)args[2])) credits.merge((Node)args[2],1,Integer::sum);
        for(Map.Entry<Node,Integer> credit:credits.entrySet())
            require(credit.getKey().rc==0||credit.getKey().rc>=credit.getValue(),"Insufficient profiling owned/borrowed alias credits");
    }
    private void validateNative(Function function,Object[] args) {
        if(function.intrinsic==PROFILE_IT) { validateProfile(function,args); return; }
        if(taskPrimitive(function.intrinsic)||function.intrinsic==TASK_MAP) { validateTaskOperation(function,args); return; }
        if(function.intrinsic==REF_SET) {
            refPlaceholders(args[0],args[1],args[args.length-1]);
            Node ref=reference(args[2]); validateHostObject(args[3]);
            if(ref.fields[0]!=null) { validateHostObject(ref.fields[0]); refIncomingAlias(ref.fields[0],args[3]); }
        } else {
            arrayPlaceholders(function,args[0],args.length>3?args[args.length-1]:ERASED,args.length==6?args[4]:ERASED);
            if(function.intrinsic==ARRAY_REPLICATE) { arrayCapacity(args[1]); validateHostObject(args[2]); }
            else {
                Node array=array(args[1]);
                if(function.intrinsic!=ARRAY_POP) {
                    int index=arrayIndex(array,externalArgument(function,args,2));
                    validateHostObject(args[3]); refIncomingAlias(array.fields[index],args[3]);
                }
            }
        }
    }
    private void enterNative(Function function,Object[] args,Body next,int dest,int kind,Object[] surplus) {
        validateNative(function,args);
        RuntimeAction action=newAction(function.intrinsic==PROFILE_IT?ACTION_PROFILE:
                taskPrimitive(function.intrinsic)||function.intrinsic==TASK_MAP?ACTION_TASK:ACTION_NATIVE,function,next,dest,kind,surplus);
        action.arguments=args; publishAction(action); applicationEntry(kind);
    }
    private void stepProfile(RuntimeAction action) {
        Object[] args=action.arguments;
        if(action.stage==0) {
            Function getter=profilingGetter(action.function);
            Object[] packet=new Object[]{args[2]};
            inc(args[2],1); // object_ref::to_obj_arg: original getter owns ONE copy.
            action.work=packet; action.stage=1;
            enterExplicit(getter,null,packet,ACTION_BODY,action.slot,ASSIGN,null); return;
        }
        if(action.stage==1) {
            Object enabled=objects[action.slot];
            require(ERASED.equals(enabled)||Long.valueOf(1).equals(enabled),"Profiling getter did not return Bool");
            require(ERASED.equals(enabled),"Enabled native profiling is outside the checked-disabled runtime profile");
            objects[action.slot]=null; action.work=null; action.stage=2;
            // Native time_task's by-value name parameter retires at constructor
            // exit when disabled, BEFORE apply_1. A finalizer may suspend here.
            action.retiring=args[4]; action.releaseClaimed=false;
            if(beginRelease(args[4],1,ACTION_BODY)) return;
        }
        if(action.stage==2) {
            action.stage=3;
            // arguments[] is an alias packet, not a second set of owners.
            // Generic AP records its once-only transfer/failure progress.
            applyExplicit(args[3],new Object[]{ERASED},ACTION_BODY,action.slot); return;
        }
        require(action.stage==3,"Invalid profiling continuation");
        Object answer=objects[action.slot]; objects[action.slot]=null;
        finishAction(action,answer);
    }
    private void stepNative(RuntimeAction action) {
        Object[] args=action.arguments; int op=action.function.intrinsic;
        if(action.stage==0) {
            action.stage=1;
            Object old=null;
            if(op==REF_SET) {
                Node ref=reference(args[2]); old=ref.fields[0]; action.current=ref;
                if(refMaybeMT(ref)) {
                    markLogicalMT(args[3]); ref.fields[0]=args[3]; stores++; action.stage=2;
                }
                action.output=ERASED;
            } else if(op==ARRAY_REPLICATE) {
                int size=arrayCapacity(args[1]); Node out=newArray(size,size); action.output=out;
                action.stage=2;
                if(size==0) old=args[2];
                else { inc(args[2],size-1); Arrays.fill(out.fields,args[2]); }
            } else {
                Node out=exclusiveArray(array(args[1]),false); action.output=out;
                if(op==ARRAY_POP) {
                    action.stage=2;
                    if(arrayState(out).size!=0) {
                        int index=--arrayState(out).size; old=out.fields[index]; out.fields[index]=null; stores++;
                    }
                } else { action.cursor=arrayIndex(out,externalArgument(action.function,args,2)); old=out.fields[action.cursor]; }
            }
            action.retiring=old; action.releaseClaimed=false;
            if(old!=null) {
                boolean dispatch=beginRelease(old,1,ACTION_BODY); action.releaseClaimed=true;
                if(dispatch) return;
            }
        }
        if(action.stage==1) {
            if(op==REF_SET) action.current.fields[0]=args[3];
            else ((Node)action.output).fields[action.cursor]=args[3];
            stores++; action.stage=2;
        }
        finishAction(action,action.output);
    }
    private void stepHostCompletion(RuntimeAction action) {
        HostCall call=action.completion;
        if(call.facade&&call.borrowedCursor<call.arguments.length) {
            if(action.stage==1) {
                call.adapterReleaseStarted=false; call.borrowedCursor++; action.stage=0; return;
            }
            int index=call.borrowedCursor;
            if(call.function.hostExtern.borrowed[index]) {
                call.adapterReleaseStarted=true; action.stage=1;
                if(beginRelease(call.arguments[index],1,ACTION_BODY)) return;
                call.adapterReleaseStarted=false; action.stage=0;
            }
            call.borrowedCursor++; return;
        }
        // Pop the cleanup frame before delivering/overapplying the reply; a
        // nested request then links to the still-waiting outer completion.
        Object answer=call.function.resultType==OBJ?call.completionResult:
                (call.kind&APPLY)!=0?boxScalar(call.completionScalar,call.function.resultType):null;
        if((call.kind&APPLY)!=0&&call.function.resultType!=OBJ) {
            // Boxing acquires an owned result before surplus validation. Keep
            // that box in the completion packet if delivery later fails.
            call.completionResult=answer; call.resultOwned=true;
        }
        require(runtimeAction==action,"Host cleanup action order differs");
        objects[action.slot]=null; sp=action.savedSp; runtimeAction=action.parent;
        hostCompletion=call.previousCompletion;
        if((call.kind&ROOT)!=0) {
            if(call.function.resultType==OBJ) result=answer; else scalarResult=call.completionScalar;
            call.resultOwned=false; pendingOwnedResult=true; phase=COMPLETE;
        } else if((call.kind&APPLY)!=0) {
            if(call.surplus==null) { objects[call.dest]=answer; pc=call.next; call.resultOwned=false; }
            else {
                Node closure=node(answer); require(closure.closure!=null,"Expected closure"); acceptsClosure(closure);
                call.resultTransferStarted=true; call.resultOwned=false; applyExplicit(answer,call.surplus,call.next,call.dest);
            }
        } else {
            if(call.function.resultType==OBJ) objects[call.dest]=answer; else numbers[call.dest]=call.completionScalar;
            pc=call.next; call.resultOwned=false;
        }
    }
    private void stepAction() {
        RuntimeAction action=runtimeAction;
        require(action!=null,"Missing runtime continuation");
        if(action.operation==ACTION_RELEASE) stepRelease(action);
        else if(action.operation==ACTION_DISPOSE) stepDispose(action);
        else if(action.operation==ACTION_NATIVE) stepNative(action);
        else if(action.operation==ACTION_TASK) stepTask(action);
        else if(action.operation==ACTION_RESOLVE) stepResolve(action);
        else if(action.operation==ACTION_RUN_TASK) stepRunTask(action);
        else if(action.operation==ACTION_PROFILE) stepProfile(action);
        else if(action.operation==ACTION_HOST_GUEST) stepHostGuest(action);
        else if(action.operation==ACTION_HOST) {
            try { stepHostCompletion(action); }
            catch(Throwable failure) { markHostFailure(action.request,failure); throw failure; }
        }
        else throw error("Unknown runtime continuation");
    }
    private Throwable hostFailure;
    private CodeRequest codeRequest,failedCodeRequest;
    private Throwable codeFailure;
    private static final class Continuation {
        Function caller;
        PreparedBody callerPrepared;
        Body next;
        int bp,sp,jbp,jsp,dest,kind;
        Object[] surplus;
        void clear() { caller=null; callerPrepared=null; next=null; surplus=null; }
    }
    public long allocations,stores,retains,releases,shellDeletes;

    public Interpreter(Program program) { this(program,false); }
    /** Existing constructors denote ordinary post-boot execution, not native
     * process startup or evidence of module/global initialization completeness. */
    public Interpreter(Program program,boolean explicit) { this(program,explicit,false); }
    /** Fresh initialization mode is explicit; it is never re-entered by imports. */
    public Interpreter(Program program,boolean explicit,boolean initializing) {
        this(program,explicit,initializing,null);
    }
    /** The caller has independently accepted the selected producer profile.
     * Null keeps build identity unavailable; module initialization is separate. */
    public Interpreter(Program program,boolean explicit,boolean initializing,BuildIdentity buildIdentity) {
        this(program,explicit,initializing,buildIdentity,null);
    }
    public Interpreter(Program program,boolean explicit,boolean initializing,BuildIdentity buildIdentity,TaskRuntime taskRuntime) {
        this(program,explicit,initializing,buildIdentity,taskRuntime,null);
    }
    public Interpreter(Program program,boolean explicit,boolean initializing,BuildIdentity buildIdentity,TaskRuntime taskRuntime,ProfilingPolicy profilingPolicy) {
        require(profilingPolicy==null||(explicit&&taskRuntime!=null),"Profiling policy requires an active explicit runtime");
        this.profilingPolicy=profilingPolicy;
        require(taskRuntime==null||explicit,"Logical task runtime requires the explicit driver");
        this.taskRuntime=taskRuntime;
        this.program=program;
        this.buildIdentity=buildIdentity;
        this.initializing=initializing;
        this.explicit=explicit;
        if(explicit) continuations=new Continuation[32];
        constants=new Object[program.functions.length];
        constantReady=new boolean[constants.length];
        constantRetired=new boolean[constants.length];
    }

    public boolean isInitializing() { return initializing; }
    /** One-way host launch boundary, analogous to native mark_end_initialization.
     * Program/header/graph operations never infer or change this phase. */
    public void finishInitialization() {
        if(closed||disposed||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||untrackedFailure)
            throw new IllegalStateException("Initialization completion requires an open idle engine");
        initializing=false;
    }

    /** Eager research fork, O(allocated stack capacity + reachable graph), not
     * a cheap branch store or an ownership ledger. Engine remains thread-confined.
     * Caller must exclusively own it and account for ALL external owner credits
     * and aliases in the copied graph, including objects reached through stale
     * registers. Completeness cannot be inferred from those registers: omitted
     * external credits remain in the copied RC count and are the caller's unmet
     * precondition, not managed ownership. The roots vector remaps identities;
     * duplicate entries never create credits. Returned roots are child objects;
     * old references still denote the parent. Object[] bundles are supported;
     * primitive-array aliases are not roots (supply their owning Node instead).
     * RC counts are copied, never incremented. Stale stack aliases are copied
     * too; their presence does not acquire ownership. No host resources exist
     * in this profile and failed-execution cleanup remains unsupported. */
    public static final class Fork {
        public final Interpreter engine;
        public final Object[] roots;
        private Fork(Interpreter engine,Object[] roots) { this.engine=engine; this.roots=roots; }
    }
    public Fork eagerFork() { return eagerFork(new Object[0]); }
    public Fork eagerFork(Object[] externalRoots) {
        if(closed||disposed||advancing||phase==FAILED||untrackedFailure||(!explicit&&sp!=0))
            throw new IllegalStateException("Fork requires an open idle or paused instruction boundary");
        if(externalRoots==null) throw error("Explicit fork roots required");
        // phase RUNNING between advance calls is a paused dispatch/release-work
        // boundary. No Java call frame is captured in that state.
        Interpreter child=new Interpreter(program,explicit,initializing,buildIdentity,taskRuntime,profilingPolicy);
        ForkCopy copy=new ForkCopy(child);
        copy.bind(constants,child.constants);
        child.objects=(Object[])copy.value(objects);
        child.numbers=numbers.clone(); child.joins=joins.clone();
        System.arraycopy(constantReady,0,child.constantReady,0,constantReady.length);
        child.constantRetired=constantRetired.clone(); child.disposed=disposed;
        child.graphInstalled=graphInstalled; child.preparedGlobalSources=preparedGlobalSources;
        child.bp=bp; child.sp=sp; child.jbp=jbp; child.jsp=jsp;
        child.result=copy.value(result); child.scalarResult=scalarResult;
        child.stdoutRoot=(Node)copy.value(stdoutRoot);
        child.output.append(output);
        String key=utf8Key==null?null:utf8Key.get();
        child.utf8Key=key==null?null:new WeakReference<>(key);
        child.utf8Bytes=utf8Bytes==null?null:utf8Bytes.clone();
        child.releaseWork=(Object[])copy.value(releaseWork); child.releasePending=releasePending;
        child.quietCurrent=(Node)copy.value(quietCurrent); child.quietFieldCursor=quietFieldCursor;
        child.releaseRoot=releaseRoot; child.releaseTransaction=(ReleaseTransaction)copy.value(releaseTransaction);
        child.callsLeft=callsLeft; child.phase=phase; child.continuationDepth=continuationDepth;
        child.untrackedFailure=untrackedFailure;
        child.instructions=instructions; child.pendingOwnedResult=pendingOwnedResult;
        child.active=(Function)copy.value(active); child.activePrepared=activePrepared; child.entry=(Function)copy.value(entry); child.pc=pc;
        if(continuations!=null) {
            child.continuations=new Continuation[continuations.length];
            copy.bind(continuations,child.continuations);
        }
        child.applicationTarget=(Function)copy.value(applicationTarget);
        child.applicationArgs=(Object[])copy.value(applicationArgs);
        child.applicationSurplus=(Object[])copy.value(applicationSurplus);
        child.applicationResult=copy.value(applicationResult); child.applicationResultOwned=applicationResultOwned;
        child.applicationArgumentsOwned=applicationArgumentsOwned; child.applicationCaptureCount=applicationCaptureCount;
        child.applicationRetainedCaptures=applicationRetainedCaptures;
        child.hostRequest=(HostRequest)copy.value(hostRequest);
        child.hostCompletion=(HostCall)copy.value(hostCompletion);
        child.hostGuestPolicy=hostGuestPolicy; child.hostGuestRecord=(HostGuestRecord)copy.value(hostGuestRecord);
        child.runtimeAction=(RuntimeAction)copy.value(runtimeAction);
        child.failedRuntimeAction=(RuntimeAction)copy.value(failedRuntimeAction);
        child.currentTask=(TaskRecord)copy.value(currentTask);
        for(Map.Entry<Node,TaskRecord> item:taskRecords.entrySet())
            child.taskRecords.put((Node)copy.value(item.getKey()),(TaskRecord)copy.value(item.getValue()));
        child.codeRequest=(CodeRequest)copy.value(codeRequest);
        child.allocations=allocations; child.stores=stores; child.retains=retains;
        child.releases=releases; child.shellDeletes=shellDeletes;
        Object[] roots=(Object[])copy.value(externalRoots);
        copy.finish();
        return new Fork(child,roots);
    }
    /** One identity map covers mutable arrays, nodes, continuations and private
     * stream function descriptors. Graph traversal is iterative, including cycles. */
    private final class ForkCopy {
        final Interpreter child;
        final IdentityHashMap<Object,Object> copies=new IdentityHashMap<>();
        final ArrayDeque<Object[]> pending=new ArrayDeque<>();
        ForkCopy(Interpreter child) { this.child=child; }
        void bind(Object[] source,Object[] target) {
            copies.put(source,target); pending.addLast(new Object[]{source,target});
        }
        Object value(Object source) {
            if(source==null||source instanceof Long||source instanceof BigInteger||source instanceof String||source instanceof F64Bits||source instanceof Double) return source;
            Object prior=copies.get(source); if(prior!=null) return prior;
            if(source instanceof Node) {
                Node old=(Node)source;
                checkRuntimeOwner(old);
                Object[] fields=(Object[])copies.get(old.fields);
                boolean fresh=fields==null;
                if(fresh) fields=new Object[old.fields.length];
                Node out=new Node(old.tag,fields,old.scalars.length);
                copies.put(source,out); out.rc=old.rc; out.dead=old.dead; out.array=old.array; out.ref=old.ref; out.readyTask=old.readyTask; out.metadata=old.metadata==null?null:old.metadata.copyForFork(child.runtimeIdentity);
                out.closure=(Function)value(old.closure);
                System.arraycopy(old.scalars,0,out.scalars,0,old.scalars.length);
                if(fresh) bind(old.fields,out.fields); return out;
            }
            if(source instanceof Object[]) {
                Object[] out=new Object[((Object[])source).length]; bind((Object[])source,out); return out;
            }
            if(source instanceof Function) {
                Function old=(Function)source;
                if(old.privateOwner!=runtimeIdentity) return old;
                Function out=new Function(old.label,old.id,old.params,old.paramTypes,
                        old.resultType,old.intrinsic,old.hostExtern,child.runtimeIdentity);
                copies.put(source,out); return out;
            }
            if(source instanceof TaskRecord) {
                TaskRecord out=new TaskRecord(); copies.put(source,out);
                pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof DependencyList) {
                DependencyList out=new DependencyList(); copies.put(source,out);
                pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof Registration) {
                Registration out=new Registration(); copies.put(source,out);
                pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof HostGuestRecord) {
                HostGuestRecord out=new HostGuestRecord(); copies.put(source,out);
                pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof HostGuestOperation) {
                HostGuestOperation old=(HostGuestOperation)source;
                require(old.owner==runtimeIdentity,"Foreign host guest operation");
                HostGuestOperation out=new HostGuestOperation(child.runtimeIdentity,(HostGuestRecord)value(old.record));
                copies.put(source,out); return out;
            }
            if(source instanceof RuntimeAction) {
                RuntimeAction out=new RuntimeAction(); copies.put(source,out);
                pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof ReleaseTransaction) {
                ReleaseTransaction old=(ReleaseTransaction)source,out=new ReleaseTransaction(); copies.put(source,out);
                out.origin=(Node)value(old.origin); out.current=(Node)value(old.current);
                out.count=old.count; out.fieldCursor=old.fieldCursor; out.fieldLimit=old.fieldLimit; out.claimed=old.claimed;
                return out;
            }
            if(source instanceof CodeRequest) {
                CodeRequest old=(CodeRequest)source;
                if(old.owner!=runtimeIdentity) throw error("Code request belongs to another interpreter");
                CodeRequest out=new CodeRequest(child.runtimeIdentity,(CodeActivation)value(old.activation));
                copies.put(source,out); return out;
            }
            if(source instanceof CodeActivation) {
                CodeActivation old=(CodeActivation)source,out=new CodeActivation(); copies.put(source,out);
                out.function=(Function)value(old.function); out.arguments=(Object[])value(old.arguments);
                out.surplus=(Object[])value(old.surplus); out.next=old.next;
                out.dest=old.dest; out.kind=old.kind; out.claimed=old.claimed;
                return out;
            }
            if(source instanceof HostRequest) {
                HostRequest old=(HostRequest)source;
                if(old.owner!=runtimeIdentity) throw error("Host request belongs to another interpreter");
                HostRequest out=new HostRequest(child.runtimeIdentity,(HostCall)value(old.call));
                copies.put(source,out); return out;
            }
            if(source instanceof HostCall) {
                HostCall out=new HostCall(); copies.put(source,out);
                pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof Continuation) {
                Continuation old=(Continuation)source,out=new Continuation(); copies.put(source,out);
                out.caller=(Function)value(old.caller); out.callerPrepared=old.callerPrepared; out.next=old.next;
                out.bp=old.bp; out.sp=old.sp; out.jbp=old.jbp; out.jsp=old.jsp;
                out.dest=old.dest; out.kind=old.kind; out.surplus=(Object[])value(old.surplus);
                return out;
            }
            throw error("Fork root outside immutable/Node runtime profile: "+source.getClass().getName());
        }
        void finish() {
            while(!pending.isEmpty()) {
                Object[] task=pending.removeFirst();
                Object source=task[0],target=task[1];
                if(source instanceof Object[]) {
                    Object[] from=(Object[])source,to=(Object[])target;
                    for(int i=0;i<from.length;i++) to[i]=value(from[i]);
                } else if(source instanceof RuntimeAction) {
                    RuntimeAction old=(RuntimeAction)source,out=(RuntimeAction)target;
                    out.parent=(RuntimeAction)value(old.parent); out.guest=(HostGuestRecord)value(old.guest); out.operation=old.operation; out.stage=old.stage;
                    out.savedSp=old.savedSp; out.slot=old.slot; out.dest=old.dest; out.kind=old.kind;
                    out.cursor=old.cursor; out.limit=old.limit; out.pending=old.pending;
                    out.function=(Function)value(old.function); out.next=old.next;
                    out.surplus=(Object[])value(old.surplus); out.work=(Object[])value(old.work);
                    out.arguments=(Object[])value(old.arguments); out.completion=(HostCall)value(old.completion);
                    out.request=(HostRequest)value(old.request);
                    out.task=(TaskRecord)value(old.task); out.scope=(TaskRecord)value(old.scope); out.batch=(DependencyList)value(old.batch);
                    out.output=value(old.output); out.retiring=value(old.retiring); out.releaseClaimed=old.releaseClaimed; out.current=(Node)value(old.current); out.origin=(Node)value(old.origin);

                } else if(source instanceof HostCall) {
                    HostCall old=(HostCall)source,out=(HostCall)target;
                    out.function=(Function)value(old.function); out.arguments=(Object[])value(old.arguments);
                    out.surplus=(Object[])value(old.surplus); out.next=old.next;
                    out.dest=old.dest; out.kind=old.kind; out.borrowedCursor=old.borrowedCursor;
                    out.facade=old.facade; out.replyClaimed=old.replyClaimed;
                    out.adapterReleaseStarted=old.adapterReleaseStarted; out.resultOwned=old.resultOwned;
                    out.resultTransferStarted=old.resultTransferStarted;
                    out.completionResult=value(old.completionResult); out.completionScalar=old.completionScalar;
                    out.previousCompletion=(HostCall)value(old.previousCompletion);
                    out.argumentTransferred=old.argumentTransferred==null?null:old.argumentTransferred.clone();

                } else if(source instanceof TaskRecord) {
                    TaskRecord old=(TaskRecord)source,out=(TaskRecord)target;
                    out.task=(Node)value(old.task); out.dependents=(DependencyList)value(old.dependents);
                    out.waiting=(Registration)value(old.waiting); out.canceled=old.canceled; out.deactivated=old.deactivated;
                    out.keepalive=old.keepalive; out.bind=old.bind; out.io=old.io; out.forward=old.forward; out.running=old.running;
                } else if(source instanceof DependencyList) {
                    ((DependencyList)target).head=(Registration)value(((DependencyList)source).head);
                } else if(source instanceof Registration) {
                    Registration old=(Registration)source,out=(Registration)target;
                    out.list=(DependencyList)value(old.list); out.previous=(Registration)value(old.previous);
                    out.next=(Registration)value(old.next); out.source=(TaskRecord)value(old.source); out.dependent=(TaskRecord)value(old.dependent);
                } else if(source instanceof HostGuestRecord) {
                    HostGuestRecord old=(HostGuestRecord)source,out=(HostGuestRecord)target;
                    out.parent=(HostGuestRecord)value(old.parent); out.outer=(HostRequest)value(old.outer);
                    out.token=(HostGuestOperation)value(old.token); out.action=(RuntimeAction)value(old.action);
                    out.helper=old.helper; out.function=(Function)value(old.function); out.caller=(Function)value(old.caller);
                    out.callerPrepared=old.callerPrepared; out.savedPc=old.savedPc; out.scope=(TaskRecord)value(old.scope);
                    out.completionBase=(HostCall)value(old.completionBase); out.arguments=(Object[])value(old.arguments);
                    out.movedSlots=old.movedSlots==null?null:old.movedSlots.clone();
                    out.bp=old.bp; out.sp=old.sp; out.jbp=old.jbp; out.jsp=old.jsp; out.depth=old.depth; out.count=old.count;
                    out.release=old.release; out.argumentsOwned=old.argumentsOwned; out.entered=old.entered;
                    out.complete=old.complete; out.resultOwned=old.resultOwned; out.taken=old.taken;
                    out.releaseClaimed=old.releaseClaimed; out.result=value(old.result);
                } else throw error("Unknown deferred fork record");
            }
        }
    }
    private static IllegalArgumentException error(String message) { return new IllegalArgumentException(message); }
    private static int number(Object x) {
        if(!(x instanceof Number)||!x.toString().matches("0|[1-9][0-9]*")) throw error("Expected exact nonnegative integer: "+x);
        BigInteger n=new BigInteger(x.toString());
        if(n.compareTo(BigInteger.valueOf(1_000_000))>0) throw error("Integer outside preparation bounds: "+n);
        return n.intValue();
    }
    @SuppressWarnings("unchecked") private static Map<String,Object> map(Object x) {
        if(!(x instanceof Map)) throw error("Expected IR map");
        return (Map<String,Object>)x;
    }
    @SuppressWarnings("unchecked") private static List<Object> list(Object x) {
        if(!(x instanceof List)) throw error("Expected IR array");
        return (List<Object>)x;
    }
    private static int type(Object x) {
        if("uint8".equals(x)) return U8;
        if("uint32".equals(x)) return U32;
        if("usize".equals(x)) return USIZE;
        if("uint64".equals(x)) return U64;
        if("float".equals(x)) return F64;
        if("object".equals(x)||"tobject".equals(x)||"tagged".equals(x)||"erased".equals(x)||"void".equals(x)) return OBJ;
        throw error("Unsupported baseline IR type: "+x);
    }
    private static String name(Object x) {
        List<Object> n=list(x);
        switch((String)n.get(0)) {
            case "anonymous": return "";
            case "str": case "num": {
                String p=name(n.get(1)); return p.isEmpty()?n.get(2).toString():p+"."+n.get(2);
            }
            default: throw error("Unsupported name");
        }
    }
    private static int variable(Object x) { int id=number(map(x).get("idx")); if(id==0) throw error("Variable/join zero is reserved"); return id; }
    private static int arg(Object x) {
        if("erased".equals(x)) return 0;
        return variable(map(map(x).get("var")).get("id"));
    }
    private static int[] args(Object x) { List<Object> xs=list(x); int[] out=new int[xs.size()]; for(int i=0;i<out.length;i++) out[i]=arg(xs.get(i)); return out; }
    private static int[] params(Object x) { List<Object> xs=list(x); int[] out=new int[xs.size()]; for(int i=0;i<out.length;i++) out[i]=variable(map(xs.get(i)).get("x")); return out; }

    /** Freeze every nested Name list and leaf before retaining it as a key.
     * No caller-owned list/map/array can later change a generation's index. */
    private static Object frozenName(Object value) {
        if(value instanceof List) {
            List<Object> out=new ArrayList<>();
            for(Object element:(List<?>)value) out.add(frozenName(element));
            return Collections.unmodifiableList(out);
        }
        if(value instanceof String||value instanceof Long||value instanceof Integer
                ||value instanceof Short||value instanceof Byte||value instanceof BigInteger
                ||value instanceof Boolean) return value;
        throw error("Mutable or unsupported captured Name component");
    }
    /** Prepare original exported IR once. All functions must be in the profile. */
    public static Program prepare(List<?> rows) { return prepare(rows,new HostExtern[0]); }
    public static Program prepare(List<?> rows,HostExtern[] externs) { return link(null,rows,externs); }
    private static Program link(Program base,List<?> rows,HostExtern[] externs) {
        require(rows!=null,"Explicit declaration rows required");
        require(externs!=null,"Explicit host extern registry required");
        Map<String,List<HostExtern>> hostRegistry=new HashMap<>();
        if(base!=null) for(Map.Entry<String,List<HostExtern>> entry:base.hostRegistry.entrySet())
            hostRegistry.put(entry.getKey(),new ArrayList<>(entry.getValue()));
        for(HostExtern descriptor:externs.clone()) {
            require(descriptor!=null,"Null host extern descriptor");
            hostExportConflict(base,descriptor.symbol);
            require(!EXTERNS.containsKey(descriptor.symbol),"Host extern cannot shadow builtin: "+descriptor.symbol);
            List<HostExtern> entries=hostRegistry.computeIfAbsent(descriptor.symbol,ignored->new ArrayList<>());
            for(HostExtern old:entries) require(!descriptor.sameAbi(old),"Duplicate host extern ABI: "+descriptor.symbol);
            entries.add(descriptor);
        }
        Map<Object,Function> byName=base==null?new HashMap<>():new HashMap<>(base.typedNames);
        Map<String,Function> labels=base==null?new LinkedHashMap<>():new LinkedHashMap<>(base.labels);
        List<Map<String,Object>> declarations=new ArrayList<>();
        List<Function> additions=new ArrayList<>();
        int inherited=base==null?0:base.functions.length;
        for(Object row:rows) {
            Map<String,Object> r=map(row);
            if(!"decl".equals(r.get("kind"))) continue;
            Object key=frozenName(r.get("name")); String label=name(key);
            if(byName.containsKey(key)||labels.containsKey(label)) throw error("Duplicate/ambiguous function name: "+label);
            Map<String,Object> ir=map(r.get("ir")); boolean external=ir.containsKey("extern");
            Map<String,Object> d=map(ir.get(external?"extern":"fdecl"));
            int[] parameters=params(d.get("xs")),paramTypes=new int[parameters.length];
            for(int i=0;i<parameters.length;i++) paramTypes[i]=type(map(list(d.get("xs")).get(i)).get("ty"));
            int resultType=type(d.get("type")),intrinsic=0;
            HostExtern hostExtern=null;
            if(external) {
                Object symbol=externSymbol(d);
                if(EXTERNS.containsKey(symbol)||!hostRegistry.containsKey(symbol)) {
                    ExternSpec spec=resolveExtern(d);
                    if(spec.intrinsic==0) throw error("Known extern ABI outside execution profile: "+spec.symbol);
                    intrinsic=spec.intrinsic;
                } else {
                    for(HostExtern descriptor:hostRegistry.get(symbol)) if(descriptor.matches(d)) { hostExtern=descriptor; break; }
                    if(hostExtern==null) throw error("Captured host extern ABI mismatch: "+symbol);
                }
            }
            Function f=new Function(label,Math.addExact(inherited,declarations.size()),parameters,paramTypes,
                                    resultType,intrinsic,hostExtern,null);
            byName.put(key,f); labels.put(label,f); declarations.add(r); additions.add(f);
        }
        if(base!=null&&declarations.isEmpty()&&externs.length==0) return base;
        // Every immutable new header is reserved before any body is parsed/validated.
        PreparedBody[] preparedBodies=base==null?new PreparedBody[additions.size()]
                :Arrays.copyOf(base.preparedBodies,inherited+additions.size());
        for(int rowIndex=0;rowIndex<declarations.size();rowIndex++) {
            Function f=additions.get(rowIndex);
            Map<String,Object> ir=map(declarations.get(rowIndex).get("ir"));
            BodyBuilder builder=new BodyBuilder(f);
            if(!ir.containsKey("extern")) builder.body=body(map(ir.get("fdecl")).get("body"),builder,byName);
            validate(f,builder.body);
            preparedBodies[f.id]=builder.finish();
        }
        Function[] prepared=labels.values().toArray(new Function[0]);
        hostRegistry.replaceAll((symbol,entries)->Collections.unmodifiableList(entries));
        return new Program(prepared,preparedBodies,Collections.unmodifiableMap(labels),Collections.unmodifiableMap(byName),
                           Collections.unmodifiableMap(hostRegistry),new Generation(base==null?null:base.generation),
                           base==null?new Function[prepared.length]:Arrays.copyOf(base.guestExports,prepared.length));
    }
    private static Function target(Map<Object,Function> functions,Object name) {
        Function f=functions.get(frozenName(name)); if(f==null) throw error("Unresolved function: "+name); return f;
    }
    private static Expr expr(Object input, BodyBuilder f, Map<Object,Function> functions) {
        Map<String,Object> e=map(input); if(e.size()!=1) throw error("Invalid expression");
        String op=e.keySet().iterator().next(); Map<String,Object> d=map(e.get(op)); Expr out=new Expr();
        switch(op) {
            case "ctor": {
                out.op=CTOR; Map<String,Object> info=map(d.get("i")); out.tag=number(info.get("cidx"));
                out.size=number(info.get("size")); int usize=number(info.get("usize"));
                out.scalarBytes=Math.addExact(Math.multiplyExact(usize,8),number(info.get("ssize"))); out.args=args(d.get("ys"));
                if(out.args.length!=out.size) throw error("Constructor arity mismatch"); break;
            }
            case "proj": out.op=PROJ; out.a=variable(d.get("x")); out.b=number(d.get("i")); break;
            case "uproj": out.op=UPROJ; out.a=variable(d.get("x")); out.b=number(d.get("i")); break;
            case "sproj": out.op=SPROJ; out.a=variable(d.get("x")); out.b=number(d.get("offset")); out.size=number(d.get("n")); break;
            case "fap": case "pap": out.op=op.equals("fap")?FAP:PAP; out.target=target(functions,d.get("c")); out.args=args(d.get("ys")); break;
            case "ap": out.op=AP; out.a=variable(d.get("x")); out.args=args(d.get("ys")); break;
            case "box": out.op=BOX; out.b=type(d.get("ty")); out.a=variable(d.get("x")); break;
            case "unbox": out.op=UNBOX; out.a=variable(d.get("x")); break;
            case "lit": {
                out.op=LIT; Map<String,Object> lit=map(d.get("v"));
                if(lit.containsKey("num")) { Object n=map(lit.get("num")).get("v"); BigInteger big=new BigInteger(n.toString()); out.literal=normalize(big); }
                else if(lit.containsKey("str")) { out.literal=map(lit.get("str")).get("v"); require(out.literal instanceof String,"Invalid string literal"); }
                else throw error("Unsupported literal"); break;
            }
            case "isShared": out.op=SHARED; out.a=variable(d.get("x")); break;
            default: throw error("Unsupported baseline expression: "+op);
        }
        f.width=Math.max(f.width,out.a+1);
        if(out.args!=null) for(int a:out.args) f.width=Math.max(f.width,a+1);
        return out;
    }
    private static Body body(Object input,BodyBuilder f,Map<Object,Function> functions) {
        List<Object> b=list(input); String op=(String)b.get(0); Body out=new Body();
        switch(op) {
            case "vdecl": out.op=VDECL; out.a=variable(b.get(1)); out.type=type(b.get(2)); out.expr=expr(b.get(3),f,functions); out.next=body(b.get(4),f,functions); break;
            case "jdecl": out.op=JDECL; out.a=variable(b.get(1)); out.args=params(b.get(2)); out.tags=new int[out.args.length]; for(int i=0;i<out.args.length;i++) out.tags[i]=type(map(list(b.get(2)).get(i)).get("ty")); out.body=body(b.get(3),f,functions); out.next=body(b.get(4),f,functions); f.joinWidth=Math.max(f.joinWidth,out.a+1); break;
            case "jmp": out.op=JMP; out.a=variable(b.get(1)); out.args=args(b.get(2)); f.joinWidth=Math.max(f.joinWidth,out.a+1); break;
            case "case": {
                out.op=CASE; out.a=variable(b.get(2)); out.type=type(b.get(3)); List<Object> alts=list(b.get(4));
                out.tags=new int[alts.size()]; out.alternatives=new Body[alts.size()];
                for(int i=0;i<alts.size();i++) {
                    List<Object> alt=list(alts.get(i)); boolean fallback="default".equals(alt.get(0));
                    out.tags[i]=fallback?-1:number(map(alt.get(1)).get("cidx"));
                    out.alternatives[i]=body(alt.get(fallback?1:2),f,functions);
                } break;
            }
            case "ret": out.op=RET; out.a=arg(b.get(1)); break;
            case "inc": case "dec": out.op=op.equals("inc")?INC:DEC; out.a=variable(b.get(1)); out.b=number(b.get(2)); out.next=body(b.get(5),f,functions); break;
            case "del": out.op=DEL; out.a=variable(b.get(1)); out.next=body(b.get(2),f,functions); break;
            case "set": out.op=SET; out.a=variable(b.get(1)); out.b=number(b.get(2)); out.args=new int[]{arg(b.get(3))}; out.next=body(b.get(4),f,functions); break;
            case "uset": out.op=USET; out.a=variable(b.get(1)); out.b=number(b.get(2)); out.args=new int[]{variable(b.get(3))}; out.next=body(b.get(4),f,functions); break;
            case "sset": out.op=SSET; out.a=variable(b.get(1)); out.b=number(b.get(3)); out.tags=new int[]{number(b.get(2))}; out.args=new int[]{variable(b.get(4))}; out.type=type(b.get(5)); out.next=body(b.get(6),f,functions); break;
            case "setTag": out.op=SETTAG; out.a=variable(b.get(1)); out.b=number(b.get(2)); out.next=body(b.get(3),f,functions); break;
            case "unreachable": out.op=UNREACHABLE; break;
            default: throw error("Unsupported baseline body: "+op);
        }
        f.width=Math.max(f.width,out.a+1);
        if(out.args!=null) for(int a:out.args) f.width=Math.max(f.width,a+1);
        return out;
    }

    private static void require(boolean condition,String message) { if(!condition) throw error(message); }
    private static int lane(Map<Integer,Integer> env,int variable) {
        if(variable==0) return OBJ;
        Integer t=env.get(variable); if(t==null) throw error("Unbound IR variable: "+variable); return t;
    }
    private static void mark(Set<Integer> seen,int id) { require(id>0&&seen.add(id),"Duplicate/zero binder: "+id); }
    private static void checkArgs(Map<Integer,Integer> env,int[] args,int[] types) {
        require(args.length==types.length,"Static arity mismatch");
        for(int i=0;i<args.length;i++) require(lane(env,args[i])==types[i],"Argument lane mismatch");
    }
    private static void validate(Function f,Body body) {
        Map<Integer,Integer> env=new HashMap<>(); Set<Integer> seen=new HashSet<>();
        for(int i=0;i<f.params.length;i++) { mark(seen,f.params[i]); env.put(f.params[i],f.paramTypes[i]); }
        if(f.intrinsic==0&&f.hostExtern==null) validateBody(body,f,env,new HashMap<>(),seen);
    }
    private static void validateBody(Body b,Function f,Map<Integer,Integer> env,Map<Integer,Body> joins,Set<Integer> seen) {
        // Lexical scope, unique binders and physical lanes are preparation facts.
        // This is deliberately separate from kernel proof/admission authority.
        switch(b.op) {
            case VDECL: {
                Expr e=b.expr;
                switch(e.op) {
                    case CTOR: require(b.type==OBJ,"Constructor requires object result"); for(int a:e.args) require(lane(env,a)==OBJ,"Object constructor argument required"); break;
                    case PROJ: require(b.type==OBJ&&lane(env,e.a)==OBJ,"Projection lane mismatch"); break;
                    case SPROJ: require((b.type==U8||b.type==U32||b.type==U64||b.type==F64)&&lane(env,e.a)==OBJ,"Scalar projection lane mismatch"); break;
                    case UPROJ: require(b.type==USIZE&&lane(env,e.a)==OBJ,"USize projection lane mismatch"); break;
                    case FAP: requireExecutableAbi(e.target); checkArgs(env,e.args,e.target.paramTypes); require(b.type==e.target.resultType,"Call result lane mismatch"); break;
                    case PAP: requireExecutableAbi(e.target); require(e.target.intrinsic!=PROFILE_IT,"Borrowed profiling primitive requires an owned guest wrapper"); require(!borrowedTaskPrimitive(e.target.intrinsic),"Borrowed task primitive requires owned closure wrapper"); require(b.type==OBJ&&e.args.length<e.target.params.length,"Invalid partial application"); require(!borrowedArrayPrimitive(e.target.intrinsic),"Borrowed array primitive requires owned closure wrapper"); require(!borrowedIntPrimitive(e.target.intrinsic),"Borrowed Int primitive requires owned closure wrapper"); require(!borrowedStringPositionPrimitive(e.target.intrinsic),"Borrowed String position primitive requires owned closure wrapper"); require(!borrowedStringCompletionPrimitive(e.target.intrinsic),"Borrowed String range primitive requires owned closure wrapper"); require(!borrowedBytePrimitive(e.target.intrinsic),"Borrowed ByteArray primitive requires owned closure wrapper"); require(e.target.intrinsic!=NAME_EQ,"Borrowed Name equality requires an owned guest wrapper"); require(e.target.intrinsic!=EXPR_CACHE,"Borrowed Expr data requires an owned guest wrapper"); require(e.target.intrinsic!=POINTER_IDENTITY,"Pointer identity requires a certified direct FAP site"); require(!borrowedRefPrimitive(e.target.intrinsic),"Borrowed ref primitive requires owned closure wrapper"); for(int i=0;i<e.target.paramTypes.length;i++) require(e.target.paramTypes[i]==OBJ,"Unboxed partial target unsupported; boxed wrapper required"); for(int a:e.args) require(lane(env,a)==OBJ,"Partial argument must be boxed"); break;
                    case AP: require(b.type==OBJ&&lane(env,e.a)==OBJ&&e.args.length>0,"Unsupported closure application"); for(int a:e.args) require(lane(env,a)==OBJ,"Closure argument must be boxed"); break;
                    case BOX: require(b.type==OBJ&&e.b!=OBJ&&lane(env,e.a)==e.b,"Box lane mismatch"); break;
                    case UNBOX: require(b.type!=OBJ&&lane(env,e.a)==OBJ,"Unbox lane mismatch"); break;
                    case SHARED: require(b.type==U8&&lane(env,e.a)==OBJ,"Sharing-test lane mismatch"); break;
                    case LIT: if(b.type==F64) e.literal=Long.valueOf(Double.doubleToRawLongBits(nat(e.literal).doubleValue()));
                              else if(b.type==U64) e.literal=Long.valueOf(nat(e.literal).longValue());
                              else if(b.type!=OBJ) e.literal=Long.valueOf(inputScalar(e.literal,b.type)); break;
                    default: throw error("Invalid expression opcode");
                }
                mark(seen,b.a); Map<Integer,Integer> next=new HashMap<>(env); next.put(b.a,b.type);
                validateBody(b.next,f,next,joins,seen); break;
            }
            case JDECL: {
                mark(seen,b.a); Map<Integer,Integer> scope=new HashMap<>(env);
                for(int i=0;i<b.args.length;i++) { mark(seen,b.args[i]); scope.put(b.args[i],b.tags[i]); }
                validateBody(b.body,f,scope,joins,seen);
                Map<Integer,Body> next=new HashMap<>(joins); next.put(b.a,b);
                validateBody(b.next,f,env,next,seen); break;
            }
            case JMP: { Body target=joins.get(b.a); require(target!=null,"Unknown lexical join"); checkArgs(env,b.args,target.tags); break; }
            case CASE: require(b.type!=F64,"Float case outside execution profile"); require(lane(env,b.a)==b.type,"Case lane mismatch"); for(Body alt:b.alternatives) validateBody(alt,f,env,joins,seen); break;
            case RET: require(lane(env,b.a)==f.resultType,"Return lane mismatch"); break;
            case SET: require(lane(env,b.a)==OBJ&&lane(env,b.args[0])==OBJ,"Field store lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
            case SSET: require(lane(env,b.a)==OBJ&&(b.type==U8||b.type==U32||b.type==U64||b.type==F64)&&lane(env,b.args[0])==b.type,"Scalar store lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
            case USET: require(lane(env,b.a)==OBJ&&lane(env,b.args[0])==USIZE,"USize store lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
            case INC: case DEC: case DEL: case SETTAG: require(lane(env,b.a)==OBJ,"Object instruction lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
            case UNREACHABLE: break;
            default: throw error("Invalid body opcode");
        }
    }
    /** Closed syntactic def/use proof, issued only after normal lexical/lane validation.
     * No pointer values can escape to another activation or scalar storage. */
    private static Set<Expr> certifyPointerSites(Body body) {
        if(body==null) return null;
        Map<Integer,Expr> definitions=new HashMap<>();
        collectPointerDefinitions(body,definitions);
        if(definitions.isEmpty()) return null;
        Set<Integer> used=new HashSet<>();
        checkPointerUses(body,definitions,used);
        require(used.containsAll(definitions.keySet()),"Unused pointer identity observation is outside the certified profile");
        Set<Expr> sites=Collections.newSetFromMap(new IdentityHashMap<>());
        sites.addAll(definitions.values());
        return Collections.unmodifiableSet(sites);
    }
    private static void collectPointerDefinitions(Body body,Map<Integer,Expr> definitions) {
        switch(body.op) {
            case VDECL:
                if(body.expr.op==FAP&&body.expr.target.intrinsic==POINTER_IDENTITY) {
                    require(body.type==USIZE,"Invalid pointer identity result lane");
                    definitions.put(body.a,body.expr);
                }
                collectPointerDefinitions(body.next,definitions); break;
            case JDECL:
                collectPointerDefinitions(body.body,definitions); collectPointerDefinitions(body.next,definitions); break;
            case CASE:
                for(Body alternative:body.alternatives) collectPointerDefinitions(alternative,definitions); break;
            case SET: case SSET: case USET: case SETTAG: case INC: case DEC: case DEL:
                collectPointerDefinitions(body.next,definitions); break;
            case RET: case JMP: case UNREACHABLE: break;
            default: throw error("Unaudited pointer identity body opcode");
        }
    }
    private static void noPointerUse(int variable,Map<Integer,Expr> definitions) {
        require(!definitions.containsKey(variable),"Pointer identity value escapes direct fresh-pointer equality");
    }
    private static void noPointerUses(int[] variables,Map<Integer,Expr> definitions) {
        for(int variable:variables) noPointerUse(variable,definitions);
    }
    private static void checkPointerUses(Body body,Map<Integer,Expr> definitions,Set<Integer> used) {
        switch(body.op) {
            case VDECL: {
                Expr e=body.expr;
                switch(e.op) {
                    case FAP:
                        if(e.target.intrinsic==USIZE_EQ&&e.args.length==2
                                &&(definitions.containsKey(e.args[0])||definitions.containsKey(e.args[1]))) {
                            require(definitions.containsKey(e.args[0])&&definitions.containsKey(e.args[1]),
                                    "Pointer identity equality requires two direct fresh-pointer definitions");
                            used.add(e.args[0]); used.add(e.args[1]);
                        } else noPointerUses(e.args,definitions);
                        break;
                    case CTOR: case PAP: noPointerUses(e.args,definitions); break;
                    case AP: noPointerUse(e.a,definitions); noPointerUses(e.args,definitions); break;
                    case PROJ: case SPROJ: case UPROJ: case BOX: case UNBOX: case SHARED:
                        noPointerUse(e.a,definitions); break;
                    case LIT: break;
                    default: throw error("Unaudited pointer identity expression opcode");
                }
                checkPointerUses(body.next,definitions,used); break;
            }
            case JDECL:
                checkPointerUses(body.body,definitions,used); checkPointerUses(body.next,definitions,used); break;
            case CASE:
                noPointerUse(body.a,definitions);
                for(Body alternative:body.alternatives) checkPointerUses(alternative,definitions,used); break;
            case SET: case SSET: case USET:
                noPointerUse(body.a,definitions); noPointerUses(body.args,definitions);
                checkPointerUses(body.next,definitions,used); break;
            case INC: case DEC: case DEL: case SETTAG:
                noPointerUse(body.a,definitions); checkPointerUses(body.next,definitions,used); break;
            case JMP: noPointerUses(body.args,definitions); break;
            case RET: noPointerUse(body.a,definitions); break;
            case UNREACHABLE: break;
            default: throw error("Unaudited pointer identity body opcode");
        }
    }
    private void ensure(int slots,int joinSlots) {
        if(slots>objects.length) { int n=Math.max(slots,objects.length*2); objects=Arrays.copyOf(objects,n); numbers=Arrays.copyOf(numbers,n); }
        if(joinSlots>joins.length) joins=Arrays.copyOf(joins,Math.max(joinSlots,joins.length*2));
    }
    private Object obj(int variable) { return variable==0?ERASED:objects[bp+variable]; }
    private Node node(Object o) {
        if(!(o instanceof Node)||((Node)o).dead) throw error("Expected live object");
        Node value=(Node)o; checkRuntimeOwner(value); return value;
    }
    private void checkRuntimeOwner(Node value) {
        checkPointerOwner(value);
        NodeMetadata kind=kindMetadata(value);
        if(kind instanceof TaskMetadata) require(((TaskMetadata)kind).owner==runtimeIdentity,
                "Task/Promise belongs to another interpreter");
    }
    public void inc(Object o,int n) {
        if(taskRuntime!=null&&(closed||disposed||untrackedFailure||phase==FAILED))
            throw new IllegalStateException("Active runtime cannot acquire owners after disposal or terminal failure");
        if(n<0) throw error("Negative reference increment");
        if(o instanceof Node) { Node v=node(o); if(v.rc!=0) { v.rc=Math.addExact(v.rc,n); retains+=n; } }
    }
    public void dec(Object o,int n) {
        if(taskRuntime!=null) throw new IllegalStateException("Active task runtime requires an explicit release transaction");
        releaseQuiet(o,n);
    }
    /** Finalizer-free/local quiet-proof path. Active arbitrary releases use an
     * action; this helper must never become a callback dispatcher. */
    private void releaseQuiet(Object o,int n) {
        if(releaseTransaction!=null||(releaseRoot&&taskRuntime==null))
            throw new IllegalStateException("Synchronous DEC cannot overlap a release transaction");
        if(n<0) throw error("Negative reference decrement");
        if(!(o instanceof Node)) return;
        Node v=node(o);
        if(v.rc==0) return;
        if(n>v.rc) throw error("Reference count underflow");
        markReleaseClaim(o); v.rc-=n; releases+=n;
        if(v.rc==0) destroy(v);
    }
    /** Consume each owning edge before visiting any zero-owner child. Pinned
     * lean_del_core scans ascending, then drains zero shells in LIFO order.
     * Queued zero is dead, distinct from a live persistent rc0 object. */
    private int owningFieldCount(Node current) { return current.array?arrayState(current).size:current.fields.length; }
    private void releaseField(Node current,int index) {
        Object child=current.fields[index];
        if(child instanceof Node) {
            Node value=node(child);
            if(value.rc!=0) {
                if(value.rc<0) throw error("Reference count underflow");
                // Capacity is secured before the last child credit is claimed.
                if(value.rc==1&&releasePending==releaseWork.length)
                    releaseWork=Arrays.copyOf(releaseWork,Math.multiplyExact(releasePending,2));
                value.rc--; releases++;
                if(value.rc==0) { value.dead=true; releaseWork[releasePending++]=value; }
            }
        }
        current.fields[index]=null;
    }
    private void releaseFields(Node current) {
        int size=owningFieldCount(current);
        for(int i=0;i<size;i++) releaseField(current,i);
    }
    private Node takeReleased() {
        Node next=(Node)releaseWork[--releasePending]; releaseWork[releasePending]=null; return next;
    }
    /** The active quiet-proof path cannot dispatch. Invariant failures still
     * retain every unscanned edge/zero shell in engine diagnostic scratch. */
    private void destroyQuietProof(Node root) {
        require(quietCurrent==null&&releasePending==0,"Quiet release scratch is already occupied");
        quietCurrent=root; quietFieldCursor=0;
        while(quietCurrent!=null) {
            quietCurrent.dead=true;
            require(!isPromise(quietCurrent),"Quiet release proof reached Promise finalizer");
            require(!runtimeTask(quietCurrent)||quietCurrent.fields[0]!=null,
                    "Quiet release proof reached pending Task finalizer");
            int size=owningFieldCount(quietCurrent);
            while(quietFieldCursor<size) { releaseField(quietCurrent,quietFieldCursor); quietFieldCursor++; }
            quietCurrent=releasePending==0?null:takeReleased(); quietFieldCursor=0;
        }
    }
    private void destroy(Node current) {
        if(taskRuntime!=null) { destroyQuietProof(current); return; }
        try {
            while(true) {
                current.dead=true;
                releaseFields(current);
                if(releasePending==0) return;
                current=takeReleased();
            }
        } finally {
            Arrays.fill(releaseWork,0,releasePending,null); releasePending=0;
        }
    }
    /** Claim external credits once, then budget ordinary native-order release.
     * Existing value/pointer/closure discipline is checked, not a universal
     * proof that arbitrary unstamped Node references belong to this branch. */
    public void startRelease(Object value,int count) {
        explicitOnly();
        if(advancing||phase!=IDLE||pendingOwnedResult||untrackedFailure||sp!=0||continuationDepth!=0
                ||releaseRoot||releasePending!=0||disposed||quietCurrent!=null)
            throw new IllegalStateException("Release transaction requires an open idle engine");
        require(count>=0,"Negative release count");
        if(taskRuntime!=null) {
            validateHostObject(value);
            // Preflight and allocate before publishing root ownership/control.
            boolean suspended=beginRelease(value,count,null,true);
            releaseRoot=true; entry=null; active=null; activePrepared=null; result=null; instructions=0; callsLeft=10_000_000;
            if(suspended) { runtimeAction.kind=ROOT; phase=RUNNING; }
            else completeRelease();
            return;
        }
        validateHostObject(value);
        Node root=value instanceof Node?(Node)value:null;
        if(root!=null&&root.rc!=0) require(count<=root.rc,"Reference count underflow");
        ReleaseTransaction transaction=null;
        if(root!=null&&root.rc!=0&&count!=0&&count==root.rc) {
            int limit=owningFieldCount(root);
            require(limit>=0&&limit<=root.fields.length,"Release field count outside payload");
            transaction=new ReleaseTransaction(); transaction.origin=root; transaction.current=root;
            transaction.count=count; transaction.fieldLimit=limit;
        }
        // Publish the preallocated claim record before consuming the root token.
        releaseRoot=true; releaseTransaction=transaction; entry=null; active=null; activePrepared=null; pc=null;
        result=null; instructions=0;
        if(root!=null&&root.rc!=0) { root.rc-=count; releases+=count; }
        if(transaction==null) { completeRelease(); return; }
        transaction.claimed=true; root.dead=true; phase=RUNNING;
    }
    private void completeRelease() {
        releaseTransaction=null; result=ERASED; pendingOwnedResult=true; phase=COMPLETE;
    }
    private void runReleaseLoop(long budget) {
        while(phase==RUNNING&&budget-->0) {
            instructions++;
            ReleaseTransaction transaction=releaseTransaction;
            if(transaction.fieldCursor<transaction.fieldLimit) {
                releaseField(transaction.current,transaction.fieldCursor);
                transaction.fieldCursor++;
            } else if(releasePending!=0) {
                Node next=(Node)releaseWork[releasePending-1]; int limit=owningFieldCount(next);
                require(limit>=0&&limit<=next.fields.length,"Release field count outside payload");
                transaction.current=takeReleased(); transaction.fieldCursor=0; transaction.fieldLimit=limit;
            } else completeRelease();
        }
    }
    private Node constructorNode(Object value) {
        Node node=node(value); require(!node.ref&&!node.array&&!node.readyTask&&!isPromise(node)&&!isByteArray(node),"Reference/array/task/byte-array is not a constructor"); return node;
    }
    private void unique(Node n) {
        require(!n.ref&&!n.array&&!n.readyTask&&!isPromise(n)&&!isByteArray(n),"Reference/array/task/byte-array is not a constructor");
        if(!exclusive(n)) throw error("Expected exclusive object");
    }
    private static BigInteger nat(Object x) {
        if(x instanceof Long&&((Long)x)>=0) return BigInteger.valueOf((Long)x);
        if(x instanceof BigInteger&&((BigInteger)x).signum()>=0) return (BigInteger)x;
        throw error("Invalid Nat");
    }
    private static Object normalize(BigInteger n) { if(n.signum()<0) throw error("Negative Nat"); return n.compareTo(SMALL_MAX)<=0?Long.valueOf(n.longValue()):n; }
    private static long inputScalar(Object value,int type) {
        if(type==F64) {
            require(value instanceof Double,"Expected Double Float scalar");
            return Double.doubleToRawLongBits((Double)value);
        }
        BigInteger n;
        if(value instanceof BigInteger) n=(BigInteger)value;
        else if(value instanceof Long||value instanceof Integer||value instanceof Short||value instanceof Byte)
            n=BigInteger.valueOf(((Number)value).longValue());
        else throw error("Expected exact unsigned scalar");
        int bits=type==U8?8:type==U32?32:64;
        if(n.signum()<0||n.bitLength()>bits) throw error("Unsigned scalar outside "+bits+"-bit range");
        return n.longValue();
    }
    private static Object externalScalar(long value,int type) {
        if(type==F64) return Double.valueOf(Double.longBitsToDouble(value));
        if((type==USIZE||type==U64)&&value<0) return BigInteger.valueOf(value&Long.MAX_VALUE).setBit(63);
        return Long.valueOf(value);
    }
    /** Typed suspended control state only; never an admitted OBJ carrier. */
    private static final class F64Bits {
        final long bits;
        F64Bits(long bits) { this.bits=bits; }
    }
    private static Object saveScalar(long bits,int lane) {
        return lane==F64?new F64Bits(bits):externalScalar(bits,lane);
    }
    private static long readSavedScalar(Object value,int lane) {
        return lane==F64&&value instanceof F64Bits?((F64Bits)value).bits:inputScalar(value,lane);
    }
    private static Object[] argumentViews(Function function,Object[] arguments) {
        Object[] views=arguments.clone();
        for(int i=0;i<views.length;i++) if(function.paramTypes[i]==F64)
            views[i]=externalScalar(readSavedScalar(views[i],F64),F64);
        return views;
    }
    private static int scalarWidth(int type) { return type==U8?1:type==U32?4:8; }
    private static int rawOffset(Node n,int word,int extra) {
        return Math.addExact(Math.multiplyExact(Math.subtractExact(word,n.fields.length),8),extra);
    }
    private static long readScalar(Node n,int offset,int type) {
        int width=scalarWidth(type);
        if(offset<0||offset>n.scalars.length-width) throw error("Scalar field outside payload");
        if(type==U8) return Byte.toUnsignedInt(n.scalars[offset]);
        long value=0;
        for(int i=0;i<width;i++) value|=(long)Byte.toUnsignedInt(n.scalars[offset+i])<<(8*i);
        return value;
    }
    private static void writeScalar(Node n,int offset,int type,long value) {
        int width=scalarWidth(type);
        if(offset<0||offset>n.scalars.length-width) throw error("Scalar field outside payload");
        if(type==U8) { n.scalars[offset]=(byte)value; return; }
        for(int i=0;i<width;i++) n.scalars[offset+i]=(byte)(value>>>(8*i));
    }
    private Object boxScalar(long value,int type) {
        if(type==USIZE||type==U64||type==F64) {
            Node n=new Node(0,0,8); writeScalar(n,0,type,value); allocations++; return n;
        }
        return Long.valueOf(type==U8?value&255:value&0xffffffffL);
    }
    private long unboxScalar(Object value,int type) {
        if(type==USIZE||type==U64||type==F64) {
            Node n=constructorNode(value);
            require(n.tag==0&&n.fields.length==0&&n.scalars.length==8&&n.closure==null,type==USIZE?"Expected boxed USize":type==F64?"Expected boxed Float":"Expected boxed UInt64");
            return readScalar(n,0,type);
        }
        return inputScalar(value,type);
    }
    private long caseTag(Body b) {
        if(b.type==OBJ) {
            Object value=obj(b.a);
            if(value instanceof Node) return constructorNode(value).tag;
            if(value instanceof Long) return ((Long)value)&0xffffffffL;
            throw error("Object case outside baseline value profile");
        }
        long value=numbers[bp+b.a];
        // The pinned C++ driver truncates USize tags to unsigned32, unlike the
        // LLVM backend. Reject that ambiguous raw-IR domain in this profile.
        if((b.type==USIZE||b.type==U64)&&(value<0||value>0xffffffffL))
            throw error(b.type==USIZE?"Wide USize case outside execution profile":"Wide UInt64 case outside execution profile");
        return value;
    }
    private void intrinsicSlots(Function f,int[] slots) {
        require(f.intrinsic!=TASK_MAP,"Task.map requires its runtime frame");
        if(floatPrimitive(f.intrinsic)) {
            floatIntrinsic(f,numbers[bp+slots[0]],slots.length<2?0:numbers[bp+slots[1]]); return;
        }
        require(f.intrinsic!=POINTER_IDENTITY,"Pointer identity requires a certified direct FAP site");
        if(f.intrinsic==EXPR_CACHE) { scalarResult=exprCachedData(obj(slots[0])); return; }
        if(f.intrinsic==EXPR_DATA) {
            exprData(numbers[bp+slots[0]],obj(slots[1]),numbers[bp+slots[2]],numbers[bp+slots[3]],
                    numbers[bp+slots[4]],numbers[bp+slots[5]],numbers[bp+slots[6]]); return;
        }
        if(f.intrinsic==LEVEL_DATA) {
            levelData(numbers[bp+slots[0]],obj(slots[1]),numbers[bp+slots[2]],numbers[bp+slots[3]]); return;
        }
        if(f.intrinsic==EXPR_APP_DATA) { exprAppData(numbers[bp+slots[0]],numbers[bp+slots[1]]); return; }
        if(f.intrinsic==STR_POS_SET) {
            stringPosSet(obj(slots[0]),obj(slots[1]),Long.valueOf(numbers[bp+slots[2]]),obj(slots[3])); return;
        }
        if(f.intrinsic==STR_MEMCMP) {
            stringMemcmp(obj(slots[0]),obj(slots[1]),obj(slots[2]),obj(slots[3]),obj(slots[4]),obj(slots[5]),obj(slots[6])); return;
        }
        if(advancedArrayPrimitive(f.intrinsic)) {
            arrayPlaceholders(f,obj(slots[0]),slots.length>3?obj(slots[slots.length-1]):ERASED,
                              slots.length==6?obj(slots[4]):ERASED);
            Object a=slotValue(f,slots,1),b=slots.length>2?slotValue(f,slots,2):ERASED;
            Object c=slots.length>3?slotValue(f,slots,3):ERASED;
            arrayIntrinsic(f,a,b,c); return;
        }
        if(refPrimitive(f.intrinsic)) {
            refPlaceholders(obj(slots[0]),obj(slots[1]),obj(slots[slots.length-1]));
            refIntrinsic(f,obj(slots[2]),slots.length==5?obj(slots[3]):ERASED); return;
        }
        if(f.intrinsic<=POW||(f.intrinsic>=NAT_LE&&f.intrinsic<=NAT_SHR)) { intrinsic(f,obj(slots[0]),slots.length<2?ERASED:obj(slots[1])); return; }
        Object a=f.paramTypes[0]==OBJ?obj(slots[0]):Long.valueOf(numbers[bp+slots[0]]);
        Object b=slots.length<2?ERASED:f.paramTypes[1]==OBJ?obj(slots[1]):Long.valueOf(numbers[bp+slots[1]]);
        if(f.intrinsic>=STR_PUSH&&!(f.intrinsic>=USIZE_LT&&f.intrinsic<=USIZE_MUL)&&!u64ScalarPrimitive(f.intrinsic)) {
            Object c=slots.length<3?ERASED:f.paramTypes[2]==OBJ?obj(slots[2]):Long.valueOf(numbers[bp+slots[2]]);
            runtimeIntrinsic(f,a,b,c);
        } else scalarIntrinsic(f,a,b);
    }
    private void intrinsicExternal(Function f,Object[] args) {
        require(f.intrinsic!=TASK_MAP,"Task.map requires its runtime frame");
        if(floatPrimitive(f.intrinsic)) {
            floatIntrinsic(f,readSavedScalar(args[0],f.paramTypes[0]),args.length<2?0:readSavedScalar(args[1],f.paramTypes[1])); return;
        }
        require(f.intrinsic!=POINTER_IDENTITY,"Pointer identity requires a certified direct FAP site");
        if(f.intrinsic==EXPR_CACHE) { scalarResult=exprCachedData(args[0]); return; }
        if(f.intrinsic==EXPR_DATA) {
            exprData(inputScalar(args[0],U64),args[1],inputScalar(args[2],U32),inputScalar(args[3],U8),
                    inputScalar(args[4],U8),inputScalar(args[5],U8),inputScalar(args[6],U8)); return;
        }
        if(f.intrinsic==LEVEL_DATA) {
            levelData(inputScalar(args[0],U64),args[1],inputScalar(args[2],U8),inputScalar(args[3],U8)); return;
        }
        if(f.intrinsic==EXPR_APP_DATA) { exprAppData(inputScalar(args[0],U64),inputScalar(args[1],U64)); return; }
        if(f.intrinsic==STR_POS_SET) {
            stringPosSet(args[0],args[1],externalArgument(f,args,2),args[3]); return;
        }
        if(f.intrinsic==STR_MEMCMP) {
            stringMemcmp(args[0],args[1],args[2],args[3],args[4],args[5],args[6]); return;
        }
        if(advancedArrayPrimitive(f.intrinsic)) {
            arrayPlaceholders(f,args[0],args.length>3?args[args.length-1]:ERASED,
                              args.length==6?args[4]:ERASED);
            Object a=externalArgument(f,args,1),b=args.length>2?externalArgument(f,args,2):ERASED;
            Object c=args.length>3?externalArgument(f,args,3):ERASED;
            arrayIntrinsic(f,a,b,c); return;
        }
        if(refPrimitive(f.intrinsic)) {
            refPlaceholders(args[0],args[1],args[args.length-1]);
            refIntrinsic(f,args[2],args.length==5?args[3]:ERASED); return;
        }
        if(f.intrinsic<=POW||(f.intrinsic>=NAT_LE&&f.intrinsic<=NAT_SHR)) { intrinsic(f,args[0],args.length<2?ERASED:args[1]); return; }
        Object a=f.paramTypes[0]==OBJ?args[0]:Long.valueOf(inputScalar(args[0],f.paramTypes[0]));
        Object b=args.length<2?ERASED:f.paramTypes[1]==OBJ?args[1]:Long.valueOf(inputScalar(args[1],f.paramTypes[1]));
        if(f.intrinsic>=STR_PUSH&&!(f.intrinsic>=USIZE_LT&&f.intrinsic<=USIZE_MUL)&&!u64ScalarPrimitive(f.intrinsic)) {
            Object c=args.length<3?ERASED:f.paramTypes[2]==OBJ?args[2]:Long.valueOf(inputScalar(args[2],f.paramTypes[2]));
            runtimeIntrinsic(f,a,b,c);
        } else scalarIntrinsic(f,a,b);
    }
    private static boolean floatPrimitive(int op) { return op>=FLOAT_BITS&&op<=FLOAT_STRING; }
    private static boolean nanBits(long bits) { return (bits&0x7ff0000000000000L)==0x7ff0000000000000L&&(bits&0x000fffffffffffffL)!=0; }
    private strictfp void floatIntrinsic(Function f,long a,long b) {
        if(f.intrinsic==FLOAT_BITS) { scalarResult=nanBits(a)?0x7ff8000000000000L:a; return; }
        if(f.intrinsic==FLOAT_U64) {
            BigInteger unsigned=BigInteger.valueOf(a&Long.MAX_VALUE); if(a<0) unsigned=unsigned.setBit(63);
            scalarResult=Double.doubleToRawLongBits(unsigned.doubleValue()); return;
        }
        double x=Double.longBitsToDouble(a),y=Double.longBitsToDouble(b);
        switch(f.intrinsic) {
            case FLOAT_SUB: scalarResult=Double.doubleToRawLongBits(x-y); break;
            case FLOAT_MUL: scalarResult=Double.doubleToRawLongBits(x*y); break;
            case FLOAT_DIV: scalarResult=Double.doubleToRawLongBits(x/y); break;
            case FLOAT_EQ: scalarResult=x==y?1:0; break;
            case FLOAT_LT: scalarResult=x<y?1:0; break;
            case FLOAT_STRING:
                if(nanBits(a)) result="NaN";
                else if(Double.isInfinite(x)) result=x<0?"-inf":"inf";
                else {
                    BigDecimal rounded=new BigDecimal(x).setScale(6,RoundingMode.HALF_EVEN);
                    result=(a<0&&rounded.signum()==0?"-":"")+rounded.toPlainString();
                }
                break;
            default: throw error("Unsupported Float intrinsic");
        }
    }
    private static boolean advancedArrayPrimitive(int op) { return op>=ARRAY_EMPTY&&op<=ARRAY_REPLICATE||op==ARRAY_CHECKED_GET||op==ARRAY_CHECKED_BORROWED; }
    private static boolean borrowedArrayPrimitive(int op) {
        return op==ARRAY_SIZE||op==ARRAY_GET||op==ARRAY_USIZE||op==ARRAY_FGET||op==ARRAY_UGET||op==ARRAY_UGET_BORROWED||op==ARRAY_CHECKED_GET||op==ARRAY_CHECKED_BORROWED;
    }
    private Object slotValue(Function f,int[] slots,int i) {
        return f.paramTypes[i]==OBJ?obj(slots[i]):externalScalar(numbers[bp+slots[i]],f.paramTypes[i]);
    }
    private static Object externalArgument(Function f,Object[] args,int i) {
        return f.paramTypes[i]==OBJ?args[i]:externalScalar(inputScalar(args[i],f.paramTypes[i]),f.paramTypes[i]);
    }
    private static void arrayPlaceholders(Function f,Object erased,Object last,Object penultimate) {
        require(ERASED.equals(erased),"Array erased parameter requires erased placeholder");
        if(f.intrinsic!=ARRAY_CHECKED_GET&&f.intrinsic!=ARRAY_CHECKED_BORROWED&&f.params.length>=4)
            require(ERASED.equals(last)&&ERASED.equals(penultimate),
                "Array proof parameters require erased placeholders");
    }
    private static int arrayCapacity(Object value) {
        BigInteger n=nat(value);
        require(n.compareTo(BigInteger.valueOf(MAX_ARRAY_CAPACITY))<=0,"Array capacity outside bounded runtime profile");
        return n.intValue();
    }
    private static ArrayState arrayState(Node value) { return (ArrayState)kindMetadata(value); }
    private static int arrayIndex(Node a,Object index) {
        BigInteger n=nat(index);
        require(n.compareTo(BigInteger.valueOf(arrayState(a).size))<0,"Array index outside bounds");
        return n.intValue();
    }
    private Node newArray(int size,int capacity) {
        require(size>=0&&capacity>=size&&capacity<=MAX_ARRAY_CAPACITY,"Array capacity outside bounded runtime profile");
        Node out=new Node(246,capacity,0); out.array=true; out.metadata=new ArrayState(size); allocations++; return out;
    }
    /** Copy only shared/persistent arrays. Unique growth transfers element owners
     * into a replacement shell; unused capacity never owns values. */
    private Node exclusiveArray(Node a,boolean push) {
        boolean exclusive=exclusive(a);
        if(exclusive&&(!push||arrayState(a).size<a.fields.length)) return a;
        boolean expand=push&&(exclusive||a.fields.length<2L*arrayState(a).size+1);
        int capacity=expand?Math.multiplyExact(Math.addExact(a.fields.length,1),2):a.fields.length;
        Node out=newArray(arrayState(a).size,capacity);
        if(exclusive) {
            System.arraycopy(a.fields,0,out.fields,0,arrayState(a).size);
            Arrays.fill(a.fields,null); a.dead=true; a.rc=0; shellDeletes++;
        } else {
            for(int i=0;i<arrayState(a).size;i++) { Object v=a.fields[i]; inc(v,1); out.fields[i]=v; }
            releaseQuiet(a,1);
        }
        return out;
    }
    private void arrayIntrinsic(Function f,Object a,Object b,Object c) {
        if(f.intrinsic==ARRAY_CHECKED_GET||f.intrinsic==ARRAY_CHECKED_BORROWED) {
            validateHostObject(a);
            Node array=array(b); BigInteger index=nat(c);
            require(index.compareTo(BigInteger.valueOf(arrayState(array).size))<0,
                    "Array.get! panic path outside bounded runtime profile");
            Object value=array.fields[index.intValue()];
            if(f.intrinsic==ARRAY_CHECKED_GET) inc(value,1);
            result=value; return;
        }
        if(f.intrinsic==ARRAY_EMPTY) { result=newArray(0,arrayCapacity(a)); return; }
        if(f.intrinsic==ARRAY_REPLICATE) {
            int size=arrayCapacity(a); validateHostObject(b);
            Node out=newArray(size,size);
            if(size==0) releaseQuiet(b,1); else { inc(b,size-1); Arrays.fill(out.fields,b); }
            result=out; return;
        }
        Node n=array(a);
        switch(f.intrinsic) {
            case ARRAY_USIZE: scalarResult=arrayState(n).size; return;
            case ARRAY_FGET: case ARRAY_UGET: case ARRAY_UGET_BORROWED: {
                Object v=n.fields[arrayIndex(n,b)];
                if(f.intrinsic!=ARRAY_UGET_BORROWED) inc(v,1);
                result=v; return;
            }
            case ARRAY_PUSH: {
                validateHostObject(b); Node out=exclusiveArray(n,true);
                out.fields[arrayState(out).size++]=b; stores++; result=out; return;
            }
            case ARRAY_POP: {
                Node out=exclusiveArray(n,false);
                if(arrayState(out).size!=0) { int i=--arrayState(out).size; Object old=out.fields[i]; out.fields[i]=null; stores++; releaseQuiet(old,1); }
                result=out; return;
            }
            case ARRAY_FSET: case ARRAY_USET: {
                int index=arrayIndex(n,b); validateHostObject(c);
                refIncomingAlias(n.fields[index],c);
                Node out=exclusiveArray(n,false); Object old=out.fields[index];
                out.fields[index]=c; stores++; releaseQuiet(old,1); result=out; return;
            }
            case ARRAY_SWAP: {
                int i=arrayIndex(n,b),j=arrayIndex(n,c); Node out=exclusiveArray(n,false);
                Object old=out.fields[i]; out.fields[i]=out.fields[j]; out.fields[j]=old;
                stores+=2; result=out; return;
            }
            case ARRAY_LIST: {
                Object list=ERASED;
                for(int i=arrayState(n).size-1;i>=0;i--) {
                    Object v=n.fields[i]; inc(v,1); Node cons=new Node(1,2,0); allocations++;
                    cons.fields[0]=v; cons.fields[1]=list; list=cons;
                }
                releaseQuiet(n,1); result=list; return;
            }
            default: throw error("Invalid array intrinsic");
        }
    }
    private static boolean refPrimitive(int intrinsic) { return intrinsic>=REF_MK&&intrinsic<=REF_PTR_EQ; }
    private static boolean borrowedRefPrimitive(int intrinsic) { return intrinsic>=REF_GET&&intrinsic<=REF_PTR_EQ; }
    private static void refPlaceholders(Object erased1,Object erased2,Object world) {
        require(ERASED.equals(erased1)&&ERASED.equals(erased2)&&ERASED.equals(world),
                "ST.Ref erased/world parameters require erased placeholders");
    }
    private Node reference(Object value) {
        Node ref=node(value);
        require(ref.ref&&!ref.array&&ref.closure==null&&ref.tag==253&&ref.fields.length==1&&ref.scalars.length==0,
                "Expected ST.Ref cell");
        return ref;
    }
    private Object refPayload(Node ref,Function function) {
        Object value=ref.fields[0];
        if(value==null) throw error("Empty ST.Ref in "+function.label+" (single-thread execution profile)");
        validateHostObject(value); return value;
    }
    private static void refIncomingAlias(Object previous,Object incoming) {
        if(previous==incoming&&incoming instanceof Node) {
            Node node=(Node)incoming;
            require(node.rc==0||node.rc>=2,"ST.Ref replacement aliases cell payload without a separate owned credit");
        }
    }
    /** Thread-confined refs preserve logical MT/persistent payload marking;
     * no native atomic waits or hidden borrowed-ref adapter. */
    private void refIntrinsic(Function function,Object a,Object b) {
        if(function.intrinsic==REF_MK) {
            validateHostObject(a);
            Node ref=new Node(253,1,0); ref.ref=true; ref.fields[0]=a;
            allocations++; result=ref; return;
        }
        Node ref=reference(a);
        if(function.intrinsic==REF_PTR_EQ) { scalarResult=ref==reference(b)?1:0; return; }
        if(function.intrinsic==REF_GET) { Object value=refPayload(ref,function); inc(value,1); result=value; return; }
        if(function.intrinsic==REF_TAKE) {
            Object value=refPayload(ref,function); ref.fields[0]=null; stores++; result=value; return;
        }
        validateHostObject(b);
        if(function.intrinsic==REF_SET) {
            Object old=ref.fields[0];
            if(old!=null) { validateHostObject(old); refIncomingAlias(old,b); }
            if(refMaybeMT(ref)) {
                markLogicalMT(b); ref.fields[0]=b; stores++;
                if(old!=null) releaseQuiet(old,1);
            } else {
                // Still finalizer-free: preserve the native ST release/store order.
                if(old!=null) releaseQuiet(old,1);
                ref.fields[0]=b; stores++;
            }
            result=ERASED; return;
        }
        if(function.intrinsic==REF_SWAP) {
            Object old=refPayload(ref,function); refIncomingAlias(old,b);
            if(refMaybeMT(ref)) markLogicalMT(b);
            ref.fields[0]=b; stores++; result=old; return;
        }
        throw error("Invalid ST.Ref intrinsic");
    }
    private static boolean leadingByte(byte value) { return (value&0xc0)!=0x80; }
    private static int utf8Width(byte value) {
        int b=Byte.toUnsignedInt(value);
        return b<128?1:b<224?2:b<240?3:4;
    }
    private static int utf8CodePoint(byte[] bytes,int p) {
        int first=Byte.toUnsignedInt(bytes[p]),width=utf8Width(bytes[p]);
        int cp=width==1?first:first&((1<<(7-width))-1);
        for(int i=1;i<width;i++) cp=(cp<<6)|(bytes[p+i]&63);
        return cp;
    }
    /** Native strings use byte positions, including defined safe invalid-index
     * behavior. Java carriers are validated Unicode; no normalization occurs. */
    private void stringPositionIntrinsic(Function f,Object a,Object b,Object c) {
        byte[] bytes=utf8(a); BigInteger position=nat(b);
        int length=bytes.length;
        if(f.intrinsic==STR_END) { scalarResult=position.compareTo(BigInteger.valueOf(length))>=0?1:0; return; }
        if(f.intrinsic==STR_SAFE_NEXT) {
            int width=1;
            if(position.compareTo(BigInteger.valueOf(length))<0) {
                int p=position.intValue(); width=leadingByte(bytes[p])?utf8Width(bytes[p]):1;
            }
            result=normalize(position.add(BigInteger.valueOf(width))); return;
        }
        if(f.intrinsic==STR_PREV) {
            if(position.signum()==0) { result=ERASED; return; }
            if(position.compareTo(BigInteger.valueOf(length))>0) { result=normalize(position.subtract(BigInteger.ONE)); return; }
            int p=position.intValue()-1;
            while(p>0&&!leadingByte(bytes[p])) p--;
            result=Long.valueOf(p); return;
        }
        if(f.intrinsic==STR_VALID) {
            scalarResult=position.compareTo(BigInteger.valueOf(length))<=0
                    &&(position.intValue()==length||leadingByte(bytes[position.intValue()]))?1:0; return;
        }
        if(f.intrinsic==STR_EXTRACT) {
            BigInteger end=nat(c);
            if(position.bitLength()>63||end.bitLength()>63) { result=a; return; }
            if(position.compareTo(end)>=0||position.compareTo(BigInteger.valueOf(length))>=0) { result=""; return; }
            int begin=position.intValue();
            if(!leadingByte(bytes[begin])) { result=""; return; }
            int stop=end.compareTo(BigInteger.valueOf(length))>=0?length:end.intValue();
            if(stop<length&&!leadingByte(bytes[stop])) stop=length;
            result=new String(bytes,begin,stop-begin,StandardCharsets.UTF_8); return;
        }
        boolean inRange=position.compareTo(BigInteger.valueOf(length))<0;
        if(f.intrinsic==STR_BYTE) {
            require(ERASED.equals(c),"String byte proof requires erased placeholder");
            require(inRange,"UTF-8 byte index outside String");
            scalarResult=Byte.toUnsignedInt(bytes[position.intValue()]); return;
        }
        if(f.intrinsic==STR_SET) {
            int replacement=codePoint(c);
            if(!inRange||!leadingByte(bytes[position.intValue()])) { result=a; return; }
            int p=position.intValue(),width=utf8Width(bytes[p]);
            result=new String(bytes,0,p,StandardCharsets.UTF_8)+new String(Character.toChars(replacement))
                    +new String(bytes,p+width,length-p-width,StandardCharsets.UTF_8); return;
        }
        scalarResult=inRange&&leadingByte(bytes[position.intValue()])?utf8CodePoint(bytes,position.intValue()):65;
    }
    private void stringIntrinsic(Function f,Object a,Object b,Object c) {
        if(f.intrinsic>=STR_END&&f.intrinsic<=STR_EXTRACT||f.intrinsic==STR_BYTE||f.intrinsic==STR_SET) {
            stringPositionIntrinsic(f,a,b,c); return;
        }
        if(f.intrinsic==STR_LENGTH) { String s=text(a); utf8(s); result=Long.valueOf(s.codePointCount(0,s.length())); return; }
        if(f.intrinsic==STR_CONTAINS) { String s=text(a); utf8(s); scalarResult=s.indexOf(codePoint(b))>=0?1:0; return; }
        byte[] x=utf8(a),y=utf8(b); int cmp=Arrays.compareUnsigned(x,y);
        if(f.intrinsic==STR_EQ) scalarResult=cmp==0?1:0;
        else if(f.intrinsic==STR_LT) scalarResult=cmp<0?1:0;
        else scalarResult=cmp<0?0:cmp==0?1:2;
    }
    /** Pinned lean_del_object ignores tagged immediates; heap deletion transfers
     * already-extracted field credits and must not recursively decrement them. */
    private void deleteShell(Object value) {
        if(value instanceof Long) return;
        Node n=node(value); unique(n); n.dead=true; Arrays.fill(n.fields,null); shellDeletes++;
    }
    private static boolean borrowedStringPositionPrimitive(int op) {
        return op==STR_GET||op==STR_NEXT||op==STR_EXTRACT;
    }
    /** Modern proof-carrying Pos is an erased wrapper around a Nat byte offset.
     * Unlike legacy Raw.set, this exact ABI owns its position and proves non-end.
     * Java String is immutable, so native in-place ASCII identity is not claimed. */
    private void stringPosSet(Object source,Object position,Object replacement,Object proof) {
        require(ERASED.equals(proof),"String.Pos.set proof requires erased placeholder");
        byte[] bytes=utf8(source); BigInteger offset=nat(position); int cp=codePoint(replacement);
        require(offset.compareTo(BigInteger.valueOf(bytes.length))<0,"String.Pos.set requires a non-end position");
        int p=offset.intValue();
        require(leadingByte(bytes[p]),"String.Pos.set requires a valid UTF-8 scalar position");
        int oldWidth=utf8Width(bytes[p]); int newWidth=cp<128?1:cp<2048?2:cp<65536?3:4;
        require((long)bytes.length-oldWidth+newWidth<=MAX_STRING_OUTPUT_BYTES,
                "String.Pos.set output outside bounded runtime profile");
        String changed=new String(bytes,0,p,StandardCharsets.UTF_8)+new String(Character.toChars(cp))
                +new String(bytes,p+oldWidth,bytes.length-p-oldWidth,StandardCharsets.UTF_8);
        result=changed; releaseQuiet(source,1); releaseQuiet(position,1);
    }
    private static boolean borrowedStringCompletionPrimitive(int op) { return op==STR_MEMCMP; }
    /** Proof-backed equality of raw UTF-8 byte ranges; neither positions nor
     * length may be narrowed until the complete range has been validated. */
    private void stringMemcmp(Object left,Object right,Object leftStart,Object rightStart,Object size,Object leftProof,Object rightProof) {
        require(ERASED.equals(leftProof)&&ERASED.equals(rightProof),"String memcmp proofs require erased placeholders");
        byte[] a=utf8(left),b=utf8(right);
        BigInteger x=nat(leftStart),y=nat(rightStart),n=nat(size);
        require(x.compareTo(BigInteger.valueOf(a.length))<=0&&y.compareTo(BigInteger.valueOf(b.length))<=0
                &&n.compareTo(BigInteger.valueOf(a.length).subtract(x))<=0
                &&n.compareTo(BigInteger.valueOf(b.length).subtract(y))<=0,
                "String memcmp range outside bounded source domain");
        int from=x.intValue(),other=y.intValue(),count=n.intValue();
        scalarResult=Arrays.equals(a,from,from+count,b,other,other+count)?1:0;
    }
    private static int repairedStringPosition(byte[] bytes,BigInteger position) {
        if(position.compareTo(BigInteger.valueOf(bytes.length))>=0) return bytes.length;
        int p=position.intValue(); return leadingByte(bytes[p])?p:bytes.length;
    }
    /** Transient validated view, never retained by an engine or guest Node. */
    private static final class SubstringView {
        final Node owner;
        final byte[] bytes;
        final int start,size;
        SubstringView(Node owner,byte[] bytes,int start,int size) {
            this.owner=owner; this.bytes=bytes; this.start=start; this.size=size;
        }
    }
    private SubstringView substringView(Object value) {
        Node n=constructorNode(value);
        require(n.closure==null&&n.tag==0&&n.fields.length==3&&n.scalars.length==0,"Expected Substring.Raw constructor");
        byte[] bytes=utf8(n.fields[0]); BigInteger begin=nat(n.fields[1]),end=nat(n.fields[2]);
        int start=repairedStringPosition(bytes,begin),stop=repairedStringPosition(bytes,end);
        return new SubstringView(n,bytes,start,Math.max(0,stop-start));
    }
    private void stringCompletionIntrinsic(Function f,Object a,Object b,Object c) {
        if(f.intrinsic==STR_SUBSTRING_EQ) {
            // Validate BOTH owned operands before consuming either container.
            SubstringView x=substringView(a),y=substringView(b);
            long same=x.size==y.size&&Arrays.equals(x.bytes,x.start,x.start+x.size,y.bytes,y.start,y.start+y.size)?1:0;
            releaseQuiet(x.owner,1); releaseQuiet(y.owner,1); scalarResult=same; return;
        }
        if(f.intrinsic==STR_POS_OF) {
            byte[] bytes=utf8(a); int cp=codePoint(b),p=0;
            while(p<bytes.length&&utf8CodePoint(bytes,p)!=cp) p+=utf8Width(bytes[p]);
            result=Long.valueOf(p); releaseQuiet(a,1); return;
        }
        if(f.intrinsic==STR_OFFSET_OF_POS) {
            byte[] bytes=utf8(a); BigInteger position=nat(b);
            int stop=position.compareTo(BigInteger.valueOf(bytes.length))>=0?bytes.length:position.intValue();
            int p=0,count=0;
            while(p<stop) { p+=utf8Width(bytes[p]); count++; }
            result=Long.valueOf(count); releaseQuiet(a,1); releaseQuiet(b,1); return;
        }
        require(f.intrinsic==STR_PUSHN,"Invalid String completion intrinsic");
        String source=text(a);
        require(source.length()<=MAX_STRING_OUTPUT_BYTES,"String.pushn output outside bounded runtime profile");
        int cp=codePoint(b); BigInteger repetitions=nat(c); byte[] bytes=utf8(source);
        int width=cp<0x80?1:cp<0x800?2:cp<0x10000?3:4;
        require(bytes.length<=MAX_STRING_OUTPUT_BYTES
                &&repetitions.compareTo(BigInteger.valueOf((MAX_STRING_OUTPUT_BYTES-bytes.length)/width))<=0,
                "String.pushn output outside bounded runtime profile");
        int count=repetitions.intValue();
        if(count==0) { result=source; releaseQuiet(c,1); return; }
        int chars=Math.addExact(source.length(),Math.multiplyExact(Character.charCount(cp),count));
        StringBuilder output=new StringBuilder(chars); output.append(source);
        for(int i=0;i<count;i++) output.appendCodePoint(cp);
        result=output.toString(); releaseQuiet(a,1); releaseQuiet(c,1);
    }
    private static boolean borrowedIntPrimitive(int op) { return op>=INT_NEG&&op<=INT_LE; }
    private static BigInteger signedInteger(Object value) {
        if(value instanceof Long) return BigInteger.valueOf((Long)value);
        if(value instanceof BigInteger) return (BigInteger)value;
        throw error("Expected exact signed Int carrier");
    }
    private static Object normalizeSigned(BigInteger value) {
        return value.bitLength()<=63?Long.valueOf(value.longValue()):value;
    }
    private void intIntrinsic(Function f,Object a,Object b) {
        // Int carriers are mathematical values. Native small-object thresholds and
        // raw tagged object words are deliberately not part of this profile.
        if(a instanceof Long) {
            long x=(Long)a;
            if(f.intrinsic==INT_OF_NAT||f.intrinsic==INT_NEG_SUCC) {
                require(x>=0,"Invalid Nat"); result=f.intrinsic==INT_OF_NAT?a:Long.valueOf(-x-1); return;
            }
            if(f.intrinsic==INT_NEG||f.intrinsic==INT_ABS) {
                if(x!=Long.MIN_VALUE) { result=Long.valueOf(f.intrinsic==INT_NEG?-x:Math.abs(x)); return; }
            } else if(b instanceof Long) {
                long y=(Long)b;
                switch(f.intrinsic) {
                    case INT_EQ: scalarResult=x==y?1:0; return;
                    case INT_LT: scalarResult=x<y?1:0; return;
                    case INT_LE: scalarResult=x<=y?1:0; return;
                    case INT_ADD:
                        try { result=Long.valueOf(Math.addExact(x,y)); return; }
                        catch(ArithmeticException overflow) { break; }
                    case INT_SUB:
                        try { result=Long.valueOf(Math.subtractExact(x,y)); return; }
                        catch(ArithmeticException overflow) { break; }
                    default: throw error("Invalid signed Int intrinsic");
                }
            }
        }
        if(f.intrinsic==INT_OF_NAT) { result=normalizeSigned(nat(a)); return; }
        if(f.intrinsic==INT_NEG_SUCC) { result=normalizeSigned(nat(a).add(BigInteger.ONE).negate()); return; }
        BigInteger x=signedInteger(a);
        if(f.intrinsic==INT_NEG) { result=normalizeSigned(x.negate()); return; }
        if(f.intrinsic==INT_ABS) { result=normalize(x.abs()); return; }
        BigInteger y=signedInteger(b);
        switch(f.intrinsic) {
            case INT_ADD: result=normalizeSigned(x.add(y)); return;
            case INT_SUB: result=normalizeSigned(x.subtract(y)); return;
            case INT_EQ: scalarResult=x.equals(y)?1:0; return;
            case INT_LT: scalarResult=x.compareTo(y)<0?1:0; return;
            case INT_LE: scalarResult=x.compareTo(y)<=0?1:0; return;
            default: throw error("Invalid signed Int intrinsic");
        }
    }
    private static boolean borrowedBytePrimitive(int op) { return op==BYTE_GET||op==BYTE_SIZE; }
    private Node byteArray(Object value) {
        Node n=node(value);
        require(isByteArray(n)&&!n.array&&!n.ref&&!n.readyTask&&n.closure==null&&n.tag==248
                &&n.fields.length==0,"Expected ByteArray");
        int size=((ByteArrayState)kindMetadata(n)).size;
        require(size>=0&&size<=n.scalars.length,"ByteArray live size outside capacity"); return n;
    }
    private Node newByteArray(int size,int capacity) {
        require(size>=0&&capacity>=size&&capacity<=MAX_BYTE_CAPACITY,"ByteArray capacity outside bounded runtime profile");
        Node out=new Node(248,0,capacity); out.metadata=new ByteArrayState(size); allocations++; return out;
    }
    private void byteArrayIntrinsic(Function f,Object a,Object b,Object c) {
        if(f.intrinsic==BYTE_MK) {
            Node input=array(a); int size=arrayState(input).size;
            require(size<=MAX_BYTE_CAPACITY,"ByteArray capacity outside bounded runtime profile");
            // Validate the whole live prefix before allocation or consumption.
            for(int i=0;i<size;i++) inputScalar(input.fields[i],U8);
            Node out=newByteArray(size,size);
            for(int i=0;i<size;i++) out.scalars[i]=(byte)inputScalar(input.fields[i],U8);
            releaseQuiet(input,1); result=out; return;
        }
        Node input=byteArray(a); ByteArrayState state=(ByteArrayState)kindMetadata(input);
        if(f.intrinsic==BYTE_SIZE) { result=Long.valueOf(state.size); return; }
        if(f.intrinsic==BYTE_GET) {
            require(ERASED.equals(c),"ByteArray proof requires erased placeholder");
            BigInteger index=nat(b);
            require(index.compareTo(BigInteger.valueOf(state.size))<0,"ByteArray index outside live size");
            scalarResult=Byte.toUnsignedInt(input.scalars[index.intValue()]); return;
        }
        require(f.intrinsic==BYTE_PUSH,"Invalid ByteArray intrinsic");
        long value=inputScalar(b,U8); int next=Math.addExact(state.size,1);
        int capacity=next<=input.scalars.length?input.scalars.length:Math.multiplyExact(next,2);
        require(capacity<=MAX_BYTE_CAPACITY,"ByteArray capacity outside bounded runtime profile");
        Node out=input;
        if(!exclusive(input)||capacity!=input.scalars.length) {
            out=newByteArray(state.size,capacity);
            System.arraycopy(input.scalars,0,out.scalars,0,state.size); releaseQuiet(input,1);
        }
        ByteArrayState target=(ByteArrayState)kindMetadata(out);
        out.scalars[target.size++]=(byte)value; stores++; result=out;
    }
    private String text(Object value) { require(value instanceof String,"Expected immutable String"); return (String)value; }
    private byte[] utf8(Object value) {
        String s=text(value);
        if(utf8Key!=null&&utf8Key.get()==s) return utf8Bytes;
        for(int i=0;i<s.length();i++) {
            char ch=s.charAt(i);
            if(Character.isHighSurrogate(ch)) {
                require(i+1<s.length()&&Character.isLowSurrogate(s.charAt(i+1)),"Invalid Unicode String"); i++;
            } else require(!Character.isLowSurrogate(ch),"Invalid Unicode String");
        }
        byte[] bytes=s.getBytes(StandardCharsets.UTF_8);
        if(bytes.length<=1_048_576) { utf8Key=new WeakReference<>(s); utf8Bytes=bytes; }
        return bytes;
    }
    private int codePoint(Object value) {
        long cp=inputScalar(value,U32);
        require(cp<=0x10ffff&&(cp<0xd800||cp>0xdfff),"Invalid Unicode scalar");
        return (int)cp;
    }
    private Object[] listElements(Object list) {
        ArrayList<Object> values=new ArrayList<>();
        Object cursor=list;
        while(!(cursor instanceof Long&&(Long)cursor==0)) {
            Node n=node(cursor);
            require(!n.ref&&!n.array&&!isByteArray(n)&&n.closure==null&&n.tag==1&&n.fields.length==2&&n.scalars.length==0,"Expected List cons");
            if(values.size()>=1_000_000) throw error("List traversal limit");
            values.add(n.fields[0]); cursor=n.fields[1];
        }
        return values.toArray();
    }
    private Node array(Object value) { Node n=node(value); require(n.array&&!n.ref&&n.closure==null,"Expected Array"); return n; }
    private Node ioUnit() { Node n=new Node(0,1,0); n.fields[0]=ERASED; allocations++; return n; }
    private Node stdout() {
        if(stdoutRoot==null) {
            Node stream=new Node(0,6,0); allocations++;
            for(int i=0;i<6;i++) {
                int arity=i==1||i==2||i==4?2:1;
                int[] parameters=new int[arity],paramTypes=new int[arity];
                for(int p=0;p<arity;p++) parameters[p]=p+1;
                Function f=new Function("<captured-stream."+i+">",-1,parameters,paramTypes,
                                        OBJ,STREAM_FLUSH+i,null,runtimeIdentity);
                stream.fields[i]=closure(f,new Object[0]);
            }
            stdoutRoot=stream;
        }
        inc(stdoutRoot,1); return stdoutRoot;
    }
    public String capturedStdout() { return output.toString(); }
    /** Validate the current Name head, without a recursive prefix/hash audit.
     * A well-founded parent chain and valid Unicode are trusted value invariants. */
    private Node nameNode(Object value) {
        if(value instanceof Long&&((Long)value)==0) return null;
        require(value instanceof Node,"Expected Lean.Name anonymous zero or constructor");
        Node name=constructorNode(value);
        require(name.closure==null&&(name.tag==1||name.tag==2)&&name.fields.length==2&&name.scalars.length==8,
                "Expected Lean.Name constructor layout");
        Object leaf=name.fields[1];
        if(name.tag==1) require(leaf instanceof String,"Expected Lean.Name String component");
        else require(leaf instanceof Long&&((Long)leaf)>=0
                        ||leaf instanceof BigInteger&&((BigInteger)leaf).signum()>=0,
                     "Expected Lean.Name Nat component");
        return name;
    }
    private boolean nameEquals(Object left,Object right) {
        Node a=nameNode(left),b=nameNode(right);
        if(a==null||b==null) return a==b;
        if(a==b) return true;
        if(readScalar(a,0,U64)!=readScalar(b,0,U64)) return false;
        for(int steps=0;steps<MAX_NAME_COMPARISON_STEPS;steps++) {
            if(a.tag!=b.tag) return false;
            Object x=a.fields[1],y=b.fields[1];
            if(a.tag==1) {
                if(!((String)x).equals((String)y)) return false;
            } else if(x instanceof Long&&y instanceof Long) {
                if(((Long)x).longValue()!=((Long)y).longValue()) return false;
            } else if(!nat(x).equals(nat(y))) return false;
            a=nameNode(a.fields[0]); b=nameNode(b.fields[0]);
            if(a==null||b==null) return a==b;
            if(a==b) return true;
            // Native lean_name_eq deliberately omits repeated parent hash tests.
        }
        throw error("Name equality depth/cycle outside bounded runtime profile");
    }
    private static boolean taskPrimitive(int op) { return op>=PROMISE_NEW&&op<=IO_AS_TASK; }
    private static boolean isPromise(Node node) {
        NodeMetadata metadata=kindMetadata(node);
        return metadata instanceof TaskMetadata&&((TaskMetadata)metadata).kind==PROMISE_KIND;
    }
    private static boolean runtimeTask(Node node) {
        NodeMetadata metadata=kindMetadata(node);
        return metadata instanceof TaskMetadata&&((TaskMetadata)metadata).kind==TASK_KIND;
    }
    private Node taskNode(Object value) {
        Node task=node(value);
        require(task.readyTask&&!task.array&&!task.ref&&task.closure==null&&task.tag==252&&task.scalars.length==0
                &&(task.fields.length==1||runtimeTask(task)&&task.fields.length==3),taskRuntime==null?"Expected engine ready Task":"Expected engine Task");
        if(runtimeTask(task)) require(task.rc>0,"Runtime-created Task cannot be persistent");
        return task;
    }
    private TaskRecord pendingRecord(Node task) {
        TaskRecord record=taskRecords.get(task);
        require(record!=null&&record.task==task&&!record.deactivated&&task.fields[0]==null,"Missing pending Task record");
        return record;
    }
    private Node promiseNode(Object value) {
        Node promise=node(value);
        require(isPromise(promise)&&promise.tag==244&&!promise.ref&&!promise.array&&promise.closure==null
                &&promise.fields.length==1&&promise.scalars.length==0,"Expected engine Promise");
        require(promise.rc>0,"Runtime-created Promise cannot be persistent");
        taskNode(promise.fields[0]); return promise;
    }
    private Node newPendingTask(boolean promised) {
        Node task=new Node(252,3,0); task.readyTask=true;
        task.metadata=new SharingMetadata(new TaskMetadata(TASK_KIND,runtimeIdentity,promised?1:0));
        TaskRecord record=new TaskRecord(); record.task=task;
        taskRecords.put(task,record); allocations++; return task;
    }
    private static void unlink(Registration registration) {
        DependencyList list=registration.list;
        if(list==null) return;
        if(registration.previous==null) list.head=registration.next; else registration.previous.next=registration.next;
        if(registration.next!=null) registration.next.previous=registration.previous;
        registration.list=null; registration.previous=null; registration.next=null;
        if(registration.dependent.waiting==registration) registration.dependent.waiting=null;
    }
    private void register(TaskRecord source,TaskRecord dependent) {
        Registration registration=new Registration();
        registration.source=source; registration.dependent=dependent; registration.list=source.dependents;
        registration.next=source.dependents.head;
        if(registration.next!=null) registration.next.previous=registration;
        source.dependents.head=registration; dependent.waiting=registration;
    }
    private void retirePendingTask(Node task) {
        TaskRecord record=taskRecords.remove(task);
        require(record!=null&&record.task==task,"Missing retiring Task record");
        if(record.waiting!=null) unlink(record.waiting);
        record.deactivated=true; record.canceled=true;
        ((TaskMetadata)kindMetadata(task)).state=3;
        // Live dependents would each own this source and prevent its last DEC.
        require(record.dependents.head==null,"Retiring Task still has live dependent owners");
    }
    private void validateCallback(Object value,Node source,boolean io) {
        Node callback=node(value); acceptsClosure(callback);
        Function target=callback.closure; rootEntry(target); requireExecutableAbi(target);
        require(callback.tag==245&&!callback.array&&!callback.ref&&!callback.readyTask
                &&callback.scalars.length==0&&callback.fields.length<target.params.length,"Expected partial task callback closure");
        for(int type:target.paramTypes) require(type==OBJ,"Task callback requires boxed parameters");
        for(Object capture:callback.fields) validateHostObject(capture);
        if(callback.fields.length+(io?2:1)>=target.params.length) preflightCallable(target,true);
        IdentityHashMap<Node,Integer> credits=new IdentityHashMap<>();
        credits.put(callback,1); credits.put(source,credits.getOrDefault(source,0)+1);
        for(Object capture:callback.fields) if(capture instanceof Node)
            credits.put((Node)capture,credits.getOrDefault((Node)capture,0)+1);
        if(source.fields[0] instanceof Node) credits.put((Node)source.fields[0],credits.getOrDefault((Node)source.fields[0],0)+1);
        for(Map.Entry<Node,Integer> item:credits.entrySet())
            require(item.getKey().rc==0||item.getKey().rc>=item.getValue(),"Insufficient task argument/capture owner credits");
    }
    private void validateTaskOperation(Function function,Object[] args) {
        require(taskRuntime!=null,"Logical synchronous task runtime is inactive");
        int op=function.intrinsic;
        require(args!=null&&args.length==function.params.length,"Task native arity mismatch");
        for(int i=0;i<args.length;i++) {
            if(function.paramTypes[i]==OBJ) validateHostObject(args[i]); else readSavedScalar(args[i],function.paramTypes[i]);
            String lane=function.header==null?null:function.header.paramTypes[i];
            if(lane!=null&&(lane.equals("erased")||lane.equals("void")))
                require(ERASED.equals(args[i]),"Task erased/world parameters require canonical zero");
        }
        if(op==TASK_MAP||op==TASK_BIND||op==IO_TASK_MAP||op==IO_TASK_BIND) {
            require(ERASED.equals(args[0])&&ERASED.equals(args[1]),"Task erased placeholders required");
            if(args.length==7) require(ERASED.equals(args[6]),"Task world placeholder required");
            require(args[4] instanceof Long&&((Long)args[4])>=0&&((Long)args[4])<=8,"Task priority outside synchronous profile");
            require(readSavedScalar(args[5],U8)==1,"Async task dependency requires unsupported queued runtime");
            boolean bind=op==TASK_BIND||op==IO_TASK_BIND;
            Node source=taskNode(args[bind?2:3]);
            if(source.fields[0]==null) pendingRecord(source);
            validateCallback(args[bind?3:2],source,op==IO_TASK_MAP||op==IO_TASK_BIND);
        } else if(op==PROMISE_NEW) {
            require(ERASED.equals(args[0])&&ERASED.equals(args[1])&&ERASED.equals(args[2]),"Promise.new erased/world placeholders required");
        } else if(op==PROMISE_RESOLVE) {
            require(ERASED.equals(args[0])&&ERASED.equals(args[3]),"Promise.resolve erased/world placeholders required");
            promiseNode(args[2]);
        } else if(op==PROMISE_RESULT) {
            require(ERASED.equals(args[0]),"Promise.result? erased placeholder required"); promiseNode(args[1]);
        } else if(op==TASK_STATE||op==TASK_CANCEL||op==TASK_WAIT) {
            require(ERASED.equals(args[0])&&ERASED.equals(args[2]),"Task erased/world placeholders required");
            Node task=taskNode(args[1]);
            if(op==TASK_WAIT) require(task.fields[0]!=null,"Pending Task.get is unsupported in synchronous task scope");
        } else if(op==TASK_CANCELED) {
            require(ERASED.equals(args[0]),"Task world placeholder required");
        } else if(op==OPTION_BLOCK) {
            require(ERASED.equals(args[0])&&ERASED.equals(args[1]),"Option erased placeholders required");
            require(args[2] instanceof Node,"Option.getOrBlock! None panic/blocking is unsupported");
            Node some=constructorNode(args[2]);
            require(some.tag==1&&some.fields.length==1&&some.scalars.length==0,"Option.getOrBlock! None panic/blocking is unsupported");
            validateHostObject(some.fields[0]);
        } else throw error("Task spawn/asTask requires unsupported queued runtime");
    }
    private void startResolve(Node task,Object value,Body next) {
        RuntimeAction action=newAction(ACTION_RESOLVE,null,next,-1,ASSIGN,null);
        action.current=task; action.output=value;
        if(task.fields[0]==null) action.task=pendingRecord(task);
        publishAction(action);
    }
    private void stepResolve(RuntimeAction action) {
        if(action.stage==0) {
            if(action.current.fields[0]!=null) {
                action.stage=3; action.retiring=action.output;
                if(beginRelease(action.output,1,ACTION_BODY)) return;
            } else {
                DependencyList replacement=new DependencyList();
                markLogicalMT(action.output); action.current.fields[0]=action.output;
                ((TaskMetadata)kindMetadata(action.current)).state=2;
                action.batch=action.task.dependents; action.task.dependents=replacement;
                action.stage=1;
            }
        }
        if(action.stage==1) {
            Registration next=action.batch.head;
            if(next!=null) {
                TaskRecord dependent=next.dependent; unlink(next);
                if(!dependent.deactivated) {
                    if(action.task.canceled) dependent.canceled=true;
                    RuntimeAction run=newAction(ACTION_RUN_TASK,null,ACTION_BODY,-1,ASSIGN,null);
                    run.task=dependent; publishAction(run);
                }
                return;
            }
            taskRecords.remove(action.current); action.stage=3;
        }
        finishAction(action,ERASED);
    }
    private void stepTask(RuntimeAction action) {
        int op=action.function.intrinsic; Object[] args=action.arguments;
        if(action.stage==0) {
            if(op==PROMISE_NEW) {
                Node task=newPendingTask(true); action.output=task;
                Node promise=new Node(244,1,0);
                promise.metadata=new TaskMetadata(PROMISE_KIND,runtimeIdentity,0); promise.fields[0]=task; allocations++;
                finishAction(action,promise); return;
            }
            if(op==PROMISE_RESULT) { Object task=promiseNode(args[1]).fields[0]; inc(task,1); finishAction(action,task); return; }
            if(op==PROMISE_RESOLVE) {
                Node some=new Node(1,1,0); some.fields[0]=args[1]; allocations++; action.output=some;
                action.stage=10; startResolve((Node)promiseNode(args[2]).fields[0],some,ACTION_BODY); return;
            }
            if(op==TASK_STATE) {
                Node task=taskNode(args[1]); int state=task.fields[0]!=null?2:((TaskMetadata)kindMetadata(task)).state;
                finishAction(action,Long.valueOf(state)); return;
            }
            if(op==TASK_CANCEL) {
                Node task=taskNode(args[1]); if(task.fields[0]==null) pendingRecord(task).canceled=true;
                finishAction(action,ERASED); return;
            }
            if(op==TASK_CANCELED) { finishAction(action,Long.valueOf(currentTask!=null&&currentTask.canceled?1:0)); return; }
            if(op==TASK_WAIT) { finishAction(action,getReadyTaskOwned(readyTaskNode(args[1]))); return; }
            if(op==OPTION_BLOCK) {
                Node some=constructorNode(args[2]); Object value=some.fields[0]; inc(value,1); releaseQuiet(some,1);
                finishAction(action,value); return;
            }
            boolean bind=op==TASK_BIND||op==IO_TASK_BIND,io=op==IO_TASK_MAP||op==IO_TASK_BIND;
            Node source=taskNode(args[bind?2:3]); Object callback=args[bind?3:2];
            if(source.fields[0]==null) {
                TaskRecord parent=pendingRecord(source);
                Node task=newPendingTask(false); action.output=task; TaskRecord record=pendingRecord(task);
                record.bind=bind; record.io=io; record.keepalive=io;
                // Match native wrapper capture ordering exactly.
                task.fields[1]=bind?source:callback; task.fields[2]=bind?callback:source;
                markLogicalMT(source); markLogicalMT(callback);
                if(io) inc(task,1);
                register(parent,record); finishAction(action,task); return;
            }
            Object value=source.fields[0]; inc(value,1); action.output=value;
            releaseQuiet(source,1); // sole VALUE retained: local no-finalizer proof
            action.arguments=io?new Object[]{callback,value,ERASED}:new Object[]{callback,value};
            action.stage=1;
        }
        if(action.stage==1) {
            action.stage=2; Object[] packet=action.arguments;
            applyExplicit(packet[0],Arrays.copyOfRange(packet,1,packet.length),ACTION_BODY,action.slot); return;
        }
        if(action.stage==2) {
            Object value=objects[action.slot]; action.output=value; objects[action.slot]=null;
            if(op==TASK_BIND||op==IO_TASK_BIND) { taskNode(value); finishAction(action,value); }
            else finishAction(action,newReadyTask(value));
            return;
        }
        require(action.stage==10,"Invalid task operation continuation"); finishAction(action,ERASED);
    }
    private void stepRunTask(RuntimeAction action) {
        TaskRecord record=action.task; Node task=record.task;
        if(action.stage==0) {
            action.scope=currentTask; currentTask=record; record.running=true;
            ((TaskMetadata)kindMetadata(task)).state=1;
            boolean bind=record.bind;
            Node source=taskNode(task.fields[record.forward?1:bind?1:2]);
            Object callback=record.forward?null:task.fields[bind?2:1];
            Object value=source.fields[0]; require(value!=null,"Dependent source is not finished");
            if(!record.forward) action.arguments=record.io?new Object[]{callback,value,ERASED}:new Object[]{callback,value};
            inc(value,1); action.output=value; action.retiring=source; action.releaseClaimed=false;
            task.fields[1]=null; task.fields[2]=null;
            releaseQuiet(source,1); // ready source VALUE has just been retained
            if(record.forward) action.stage=3; else action.stage=1;
        }
        if(action.stage==1) {
            action.stage=2; Object[] packet=action.arguments;
            applyExplicit(packet[0],Arrays.copyOfRange(packet,1,packet.length),ACTION_BODY,action.slot); return;
        }
        if(action.stage==2) {
            Object answer=objects[action.slot]; action.output=answer; objects[action.slot]=null;
            if(record.bind) {
                Node nested=taskNode(answer);
                if(nested.fields[0]==null) {
                    require(!record.deactivated,"Deactivated running bind returned pending Task: native leaked-capture boundary is unsupported");
                    TaskRecord parent=pendingRecord(nested);
                    markLogicalMT(nested); task.fields[1]=nested; record.forward=true; record.running=false;
                    ((TaskMetadata)kindMetadata(task)).state=0;
                    currentTask=action.scope; register(parent,record); finishAction(action,ERASED); return;
                }
                action.output=getReadyTaskOwned(nested);
            }
            action.stage=3;
        }
        if(action.stage==3) {
            action.stage=4;
            if(record.keepalive) {
                record.keepalive=false; action.retiring=task;
                if(beginRelease(task,1,ACTION_BODY)) return;
            }
        }
        if(action.stage==4) {
            currentTask=action.scope; record.running=false; action.stage=5;
            if(record.deactivated) {
                action.retiring=action.output;
                if(beginRelease(action.output,1,ACTION_BODY)) return;
            } else { startResolve(task,action.output,ACTION_BODY); return; }
        }
        finishAction(action,ERASED);
    }
    private Node readyTaskNode(Object value) {
        Node task=taskNode(value);
        require(task.fields[0]!=null,taskRuntime==null?"Pending Task outside ready-only runtime profile":"Pending Task.get outside supported synchronous runtime");
        validateHostObject(task.fields[0]); return task;
    }
    private Node newReadyTask(Object value) {
        validateHostObject(value); Node task=new Node(252,1,0); task.readyTask=true;
        task.fields[0]=value; allocations++; return task;
    }
    private Object getReadyTaskOwned(Node task) {
        Object value=task.fields[0]; inc(value,1); releaseQuiet(task,1); return value;
    }
    private void validateTaskMap(Object[] args) {
        require(args!=null&&args.length==6,"Task.map requires six ABI arguments");
        require(ERASED.equals(args[0])&&ERASED.equals(args[1]),"Task.map erased placeholders required");
        require(args[4] instanceof Long&&((Long)args[4])>=0,"Task.map requires immediate nonnegative priority");
        require(inputScalar(args[5],U8)<=1,"Task.map sync must be Bool zero or one");
        Node callback=node(args[2]); acceptsClosure(callback);
        Function target=callback.closure; rootEntry(target); requireExecutableAbi(target);
        require(callback.tag==245&&!callback.array&&!callback.ref&&!callback.readyTask
                &&callback.scalars.length==0&&callback.fields.length<target.params.length,"Expected partial callback closure");
        for(int lane:target.paramTypes) require(lane==OBJ,"Task.map callback requires boxed object parameters");
        Node task=readyTaskNode(args[3]);
        for(Object capture:callback.fields) validateHostObject(capture);
        if(callback.fields.length+1>=target.params.length) {
            preflightCallable(target,explicit);
            if(!explicit&&target.hostExtern!=null) throw error("Host callback requires explicit driver");
            if(buildIdentityPrimitive(target.intrinsic)) requireBuildUnit(task.fields[0]);
        }
        // These are known input/capture/field owner occurrences, not a heap audit.
        IdentityHashMap<Node,Integer> credits=new IdentityHashMap<>();
        credits.put(callback,1); credits.put(task,1);
        Object payload=task.fields[0];
        if(payload instanceof Node) credits.put((Node)payload,credits.getOrDefault((Node)payload,0)+1);
        for(Object capture:callback.fields) if(capture instanceof Node)
            credits.put((Node)capture,credits.getOrDefault((Node)capture,0)+1);
        for(Map.Entry<Node,Integer> credit:credits.entrySet())
            require(credit.getKey().rc==0||credit.getKey().rc>=credit.getValue(),"Insufficient Task.map owner credits");
    }
    private Object[] taskMapArguments(int[] slots) {
        require(slots.length==6,"Task.map requires six ABI arguments");
        return new Object[]{obj(slots[0]),obj(slots[1]),obj(slots[2]),obj(slots[3]),obj(slots[4]),
                            externalScalar(numbers[bp+slots[5]],U8)};
    }
    private void taskMapRecursive(Object[] args) {
        validateTaskMap(args);
        Object value=getReadyTaskOwned((Node)args[3]);
        result=newReadyTask(apply(args[2],new Object[]{value}));
    }
    /** A private, forkable continuation: all guest refs remain in objects[].
     * Slots1/2/3 hold callback/task/result;4 retains get's acquired payload;
     * 5 is a borrowed capture snapshot;6 is AP's argument vector. Stage7 records
     * retained(1), release-started(2), consumed(3), AP-started(4), published(5).
     * Snapshots/stale aliases acquire no guest credits. Failure remains terminal. */
    private void enterTaskMap(Function function,int[] slots,Object[] args,Body next,int dest,int kind,Object[] surplus) {
        require(function.intrinsic==TASK_MAP,"Expected Task.map runtime entry");
        Object[] actual=slots==null?args:taskMapArguments(slots); validateTaskMap(actual);
        if(continuationDepth>=65536) throw error("Continuation depth limit");
        int newSp=Math.addExact(sp,TASK_MAP_LAYOUT.width);
        if(newSp>8_000_000) throw error("Explicit stack limit");
        ensure(newSp,jsp);
        if(continuationDepth==continuations.length) continuations=Arrays.copyOf(continuations,continuations.length*2);
        Continuation k=continuations[continuationDepth];
        if(k==null) continuations[continuationDepth]=k=new Continuation();
        Object[] captures=((Node)actual[2]).fields.clone(),argument=new Object[1];
        k.caller=active; k.callerPrepared=activePrepared; k.next=next; k.bp=bp; k.sp=sp; k.jbp=jbp; k.jsp=jsp;
        k.dest=dest; k.kind=kind; k.surplus=surplus;
        Arrays.fill(objects,sp,newSp,null);
        objects[sp+1]=actual[2]; objects[sp+2]=actual[3]; objects[sp+5]=captures; objects[sp+6]=argument;
        numbers[sp+7]=0; continuationDepth++;
        bp=sp; sp=newSp; jbp=jsp; active=function; activePrepared=TASK_MAP_LAYOUT; pc=TASK_MAP_LAYOUT.body;
    }
    private void requireTaskMapFrame(Body state) {
        require(activePrepared==TASK_MAP_LAYOUT&&active!=null&&active.intrinsic==TASK_MAP
                &&(state==TASK_MAP_LAYOUT.body||state==TASK_MAP_LAYOUT.body.next),"Invalid private Task.map runtime frame");
    }
    private void runtimeIntrinsic(Function f,Object a,Object b,Object c) {
        if(f.intrinsic>=STR_SUBSTRING_EQ&&f.intrinsic<=STR_PUSHN) { stringCompletionIntrinsic(f,a,b,c); return; }
        if(f.intrinsic>=INT_OF_NAT&&f.intrinsic<=INT_LE) { intIntrinsic(f,a,b); return; }
        if(f.intrinsic==NAME_EQ) { scalarResult=nameEquals(a,b)?1:0; return; }
        if(buildIdentityPrimitive(f.intrinsic)) {
            requireBuildIdentity(); requireBuildUnit(a);
            result=f.intrinsic==BUILD_GITHASH?buildIdentity.githash():buildIdentity.target(); return;
        }
        if(f.intrinsic>=BYTE_MK&&f.intrinsic<=BYTE_PUSH) { byteArrayIntrinsic(f,a,b,c); return; }
        if(f.intrinsic==IO_INITIALIZING) {
            require(ERASED.equals(a),"IO.initializing world parameter requires erased placeholder");
            scalarResult=initializing?1:0; return;
        }
        if(f.intrinsic==TASK_PURE||f.intrinsic==TASK_GET) {
            require(ERASED.equals(a),"Task erased parameter requires erased placeholder");
            if(f.intrinsic==TASK_PURE) { result=newReadyTask(b); return; }
            result=getReadyTaskOwned(readyTaskNode(b)); return;
        }
        if(f.intrinsic>=STR_END&&f.intrinsic<=STR_SET) { stringIntrinsic(f,a,b,c); return; }
        switch(f.intrinsic) {
            case STR_PUSH: utf8(a); result=text(a)+new String(Character.toChars(codePoint(b))); break;
            case STR_APPEND: utf8(a); utf8(b); result=text(a)+text(b); break;
            case STR_SIZE: result=Long.valueOf(utf8(a).length); break;
            case STR_GET: case STR_NEXT: {
                require(ERASED.equals(c),"String position proof requires erased placeholder");
                byte[] bytes=utf8(a); BigInteger index=nat(b);
                require(index.bitLength()<=31,"UTF-8 position outside String");
                int p=index.intValue();
                require(p<bytes.length&&(bytes[p]&0xc0)!=0x80,"Expected in-range UTF-8 scalar position");
                int first=Byte.toUnsignedInt(bytes[p]);
                int width=first<128?1:first<224?2:first<240?3:4;
                if(f.intrinsic==STR_NEXT) result=Long.valueOf(p+width);
                else {
                    int cp=width==1?first:first&((1<<(7-width))-1);
                    for(int i=1;i<width;i++) cp=(cp<<6)|(bytes[p+i]&63);
                    scalarResult=cp;
                } break;
            }
            case STR_LIST: {
                Object[] chars=listElements(a); StringBuilder builder=new StringBuilder();
                for(Object ch:chars) builder.appendCodePoint(codePoint(ch));
                String s=builder.toString(); releaseQuiet(a,1); result=s; break;
            }
            case ARRAY_MK: {
                Object[] elements=listElements(b); Node n=newArray(elements.length,elements.length);
                for(int i=0;i<elements.length;i++) { inc(elements[i],1); n.fields[i]=elements[i]; }
                releaseQuiet(b,1); result=n; break;
            }
            case ARRAY_SIZE: result=Long.valueOf(arrayState(array(b)).size); break;
            case ARRAY_GET: {
                Node n=array(b); BigInteger index=nat(c);
                require(index.compareTo(BigInteger.valueOf(arrayState(n).size))<0,"Array index outside bounds");
                result=n.fields[index.intValue()]; break; // Borrowed: caller IR owns the inc.
            }
            case GET_STDOUT: result=stdout(); break;
            case STREAM_FLUSH: result=ioUnit(); break;
            case STREAM_PUT: utf8(a); output.append(text(a)); result=ioUnit(); break;
            case STREAM_TTY: result=ERASED; break;
            case STREAM_READ: case STREAM_WRITE: case STREAM_LINE:
                throw new UnsupportedOperationException("Captured-output stream operation not implemented: "+f.label);
            case PANIC: throw new UnsupportedOperationException("panicCore default-return policy outside captured-output profile: "+text(c));
            default: throw error("Invalid runtime intrinsic");
        }
    }
    /** Pinned lean_expr_data reads the first scalar word after the object
     * fields. Validate only the known storage family; do not infer AST flags. */
    private long exprCachedData(Object value) {
        Node node=constructorNode(value);
        require(node.closure==null,"Closure is not an Expr constructor");
        int expected;
        switch(node.tag) {
            case 0: case 1: case 2: case 3: case 9: expected=1; break;
            case 4: case 5: case 10: expected=2; break;
            case 6: case 7: case 11: expected=3; break;
            case 8: expected=4; break;
            default: throw error("Unsupported Expr cached-data constructor tag");
        }
        int semantic=node.tag>=6&&node.tag<=8?9:8;
        require(node.fields.length==expected&&(node.scalars.length==semantic
                ||node.scalars.length==((semantic+7)&~7)),"Unexpected Expr cached-data storage layout");
        return readScalar(node,0,U64);
    }
    /** Native scalar caches only: no Expr/Level object representation is implied.
     * Successful owning Nat arguments fit native immediate bounds. Their accepted
     * Long/BigInteger carriers are uncounted, so consumption needs no DEC callback.
     * All domains are checked before publishing the result. */
    private void exprData(long hash,Object range,long depth,long a,long b,long c,long d) {
        BigInteger value=nat(range);
        require(depth>=0&&depth<=0xffffffffL,"Expr.mkData approximate depth outside UInt32 lane");
        require(a>=0&&a<=1&&b>=0&&b<=1&&c>=0&&c<=1&&d>=0&&d<=1,
                "Expr.mkData flags require Bool zero or one");
        require(value.compareTo(BigInteger.valueOf(1048575))<=0,"Expr.mkData range outside native 20-bit bound");
        scalarResult=(hash&0xffffffffL)|(Math.min(255,depth)<<32)|(a<<40)|(b<<41)|(c<<42)|(d<<43)|(value.longValue()<<44);
    }
    private void levelData(long hash,Object depth,long hasMVar,long hasParam) {
        BigInteger value=nat(depth);
        require(hasMVar>=0&&hasMVar<=1&&hasParam>=0&&hasParam<=1,"Level.mkData flags require Bool zero or one");
        require(value.compareTo(BigInteger.valueOf(16777215))<=0,"Level.mkData depth outside native 24-bit bound");
        scalarResult=(hash&0xffffffffL)|(hasMVar<<32)|(hasParam<<33)|(value.longValue()<<40);
    }
    private void exprAppData(long fData,long aData) {
        long depth=Math.min(255,Math.max((fData>>>32)&255,(aData>>>32)&255)+1);
        long range=Math.max(fData>>>44,aData>>>44);
        scalarResult=((fData|aData)&(15L<<40))|(mixHash(fData,aData)&0xffffffffL)|(depth<<32)|(range<<44);
    }
    private static long mixHash(long hash,long key) {
        long m=0xc6a4a7935bd1e995L;
        key*=m; key^=key>>>47; key^=m; // Deliberately XOR, unlike Murmur's second multiply.
        return (hash^key)*m;
    }
    private static long stringHash(byte[] bytes) {
        long m=0xc6a4a7935bd1e995L,hash=11L^((long)bytes.length*m);
        int end=bytes.length&~7;
        for(int offset=0;offset<end;offset+=8) {
            long key=0;
            for(int i=0;i<8;i++) key|=(long)Byte.toUnsignedInt(bytes[offset+i])<<(i*8);
            key*=m; key^=key>>>47; key*=m; hash^=key; hash*=m;
        }
        if(end<bytes.length) {
            for(int i=end;i<bytes.length;i++) hash^=(long)Byte.toUnsignedInt(bytes[i])<<((i-end)*8);
            hash*=m;
        }
        hash^=hash>>>47; hash*=m; hash^=hash>>>47; return hash;
    }
    /** Explicit membership: later IDs need not lie beside the original scalar group. */
    private static boolean u64ScalarPrimitive(int op) {
        switch(op) {
            case STR_HASH: case U64_MIX: case U64_NAT: case U64_SHR: case U64_XOR: case U64_USIZE:
            case U64_LT: case U64_EQ: case U64_OWNED_NAT: case U64_TO_U32:
            case BOOL_U64: case U64_ADD: case U64_SUB: case U64_MUL: case U64_DIV: case U64_MOD:
            case U64_AND: case U64_OR: case U64_NOT: case U64_NEG: case U64_LOG2: case U64_SHL: case U64_LE:
            case U8_TO_U64: case U32_TO_U64: case USIZE_TO_U64:
                return true;
            default: return false;
        }
    }
    private static void requireBoolScalar(Object value) {
        require(inputScalar(value,U8)<=1,"Bool.toUInt64 requires canonical Bool 0 or 1");
    }
    private void scalarIntrinsic(Function f,Object a,Object b) {
        switch(f.intrinsic) {
            case USIZE_NAT:
                if(f.params.length>1) require(ERASED.equals(b),"USize conversion proof requires erased placeholder");
                scalarResult=nat(a).longValue(); break;
            case USIZE_REPR: result=Long.toUnsignedString((Long)a); break;
            case U32_NAT: result=a; break;
            case U32_EQ: scalarResult=((Long)a).longValue()==((Long)b).longValue()?1:0; break;
            case U32_LE: scalarResult=(Long)a<=(Long)b?1:0; break;
            case PLATFORM_BITS: require(a instanceof Long&&(Long)a==0,"Expected Unit for platform bits"); result=Long.valueOf(64); break;
            case USIZE_LT: scalarResult=Long.compareUnsigned((Long)a,(Long)b)<0?1:0; break;
            case USIZE_LE: scalarResult=Long.compareUnsigned((Long)a,(Long)b)<=0?1:0; break;
            case USIZE_EQ: case U8_EQ: scalarResult=((Long)a).longValue()==((Long)b).longValue()?1:0; break;
            case USIZE_ADD: scalarResult=(Long)a+(Long)b; break;
            case USIZE_SUB: scalarResult=(Long)a-(Long)b; break;
            case USIZE_MUL: scalarResult=(Long)a*(Long)b; break;
            case USIZE_TO_NAT: result=externalScalar((Long)a,USIZE); break;
            case USIZE_SHR: scalarResult=(Long)a>>>(Long)b; break;
            case USIZE_SHL: scalarResult=(Long)a<<(Long)b; break;
            case USIZE_AND: case U8_AND: scalarResult=(Long)a&(Long)b; break;
            case U8_NAT: result=a; break;
            case U8_LE: scalarResult=(Long)a<=(Long)b?1:0; break;
            case U32_FROM_NAT:
                require(ERASED.equals(b),"UInt32 conversion proof requires erased placeholder");
                scalarResult=nat(a).longValue()&0xffffffffL; break;
            case U32_TO_U8: scalarResult=(Long)a&255; break;
            case U32_ADD: scalarResult=((Long)a+(Long)b)&0xffffffffL; break;
            case STR_HASH: scalarResult=stringHash(utf8(a)); break;
            case U8_TO_U64: case U32_TO_U64: case USIZE_TO_U64: scalarResult=(Long)a; break;
            case BOOL_U64: requireBoolScalar(a); scalarResult=(Long)a; break;
            case U64_ADD: scalarResult=(Long)a+(Long)b; break;
            case U64_SUB: scalarResult=(Long)a-(Long)b; break;
            case U64_MUL: scalarResult=(Long)a*(Long)b; break;
            case U64_DIV: scalarResult=(Long)b==0?0:Long.divideUnsigned((Long)a,(Long)b); break;
            case U64_MOD: scalarResult=(Long)b==0?(Long)a:Long.remainderUnsigned((Long)a,(Long)b); break;
            case U64_AND: scalarResult=(Long)a&(Long)b; break;
            case U64_OR: scalarResult=(Long)a|(Long)b; break;
            case U64_NOT: scalarResult=~(Long)a; break;
            case U64_NEG: scalarResult=-(Long)a; break;
            case U64_LOG2: scalarResult=(Long)a==0?0:63-Long.numberOfLeadingZeros((Long)a); break;
            case U64_SHL: scalarResult=(Long)a<<(Long)b; break;
            case U64_LE: scalarResult=Long.compareUnsigned((Long)a,(Long)b)<=0?1:0; break;
            case U64_MIX: scalarResult=mixHash((Long)a,(Long)b); break;
            case U64_NAT:
                if(f.params.length>1) require(ERASED.equals(b),"UInt64 conversion proof requires erased placeholder");
                scalarResult=nat(a).longValue(); break;
            case U64_OWNED_NAT: scalarResult=nat(a).longValue(); releaseQuiet(a,1); break;
            case U64_SHR: scalarResult=(Long)a>>>(Long)b; break;
            case U64_XOR: scalarResult=(Long)a^(Long)b; break;
            case U64_USIZE: scalarResult=(Long)a; break;
            case U64_TO_U32: scalarResult=(Long)a&0xffffffffL; break;
            case U64_LT: scalarResult=Long.compareUnsigned((Long)a,(Long)b)<0?1:0; break;
            case U64_EQ: scalarResult=((Long)a).longValue()==((Long)b).longValue()?1:0; break;
            default: throw error("Invalid scalar intrinsic");
        }
    }
    private static Object natPow(BigInteger base,BigInteger exponent) {
        // Pinned lean_nat_pow rejects > UINT_MAX, even for bases zero and one.
        if(exponent.bitLength()>32) throw error("Nat.pow exponent is too big");
        long n=exponent.longValue();
        BigInteger answer=BigInteger.ONE;
        while(n!=0) {
            if((n&1)!=0) answer=answer.multiply(base);
            n>>>=1;
            if(n!=0) base=base.multiply(base);
        }
        return normalize(answer);
    }
    private static Object natShiftLeft(BigInteger value,BigInteger exponent) {
        if(value.signum()==0) return ERASED;
        if(exponent.signum()==0) return normalize(value);
        require(exponent.compareTo(BigInteger.valueOf(MAX_SHIFT_RESULT_BITS))<=0
                &&(long)value.bitLength()+exponent.longValue()<=MAX_SHIFT_RESULT_BITS,
                "Nat.shiftLeft result outside bounded runtime bit limit");
        return normalize(value.shiftLeft(exponent.intValue()));
    }
    private void intrinsic(Function f,Object a,Object b) {
        if(a instanceof Long && b instanceof Long && (Long)a>=0 && (Long)b>=0) {
            long x=(Long)a,y=(Long)b;
            switch(f.intrinsic) {
                case ADD: result=x<=Long.MAX_VALUE-y?Long.valueOf(x+y):BigInteger.valueOf(x).add(BigInteger.valueOf(y)); break;
                case SUB: result=Long.valueOf(x<y?0:x-y); break;
                case MOD: result=Long.valueOf(y==0?x:x%y); break;
                case MUL: result=x==0||y<=Long.MAX_VALUE/x?Long.valueOf(x*y):BigInteger.valueOf(x).multiply(BigInteger.valueOf(y)); break;
                case DIV: result=Long.valueOf(y==0?0:x/y); break;
                case POW: result=natPow(BigInteger.valueOf(x),BigInteger.valueOf(y)); break;
                case EQ: scalarResult=x==y?1:0; break;
                case LT: scalarResult=x<y?1:0; break;
                case NAT_LE: scalarResult=x<=y?1:0; break;
                case NAT_LOG2: result=Long.valueOf(Math.max(0,63-Long.numberOfLeadingZeros(x))); break;
                case NAT_OR: result=Long.valueOf(x|y); break;
                case NAT_SHL: result=natShiftLeft(BigInteger.valueOf(x),BigInteger.valueOf(y)); break;
                case NAT_SHR: result=Long.valueOf(y>=63?0:x>>>y); break;
                default: throw error("Invalid intrinsic");
            }
        } else {
            BigInteger x=nat(a),y=nat(b);
            switch(f.intrinsic) {
                case ADD: result=normalize(x.add(y)); break;
                case SUB: result=normalize(x.compareTo(y)<0?BigInteger.ZERO:x.subtract(y)); break;
                case MOD: result=normalize(y.signum()==0?x:x.remainder(y)); break;
                case MUL: result=normalize(x.multiply(y)); break;
                case DIV: result=normalize(y.signum()==0?BigInteger.ZERO:x.divide(y)); break;
                case POW: result=natPow(x,y); break;
                case EQ: scalarResult=x.equals(y)?1:0; break;
                case LT: scalarResult=x.compareTo(y)<0?1:0; break;
                case NAT_LE: scalarResult=x.compareTo(y)<=0?1:0; break;
                case NAT_LOG2: result=Long.valueOf(Math.max(0,x.bitLength()-1)); break;
                case NAT_OR: result=normalize(x.or(y)); break;
                case NAT_SHL: result=natShiftLeft(x,y); break;
                case NAT_SHR: result=y.compareTo(BigInteger.valueOf(x.bitLength()))>=0?ERASED:normalize(x.shiftRight(y.intValue())); break;
                default: throw error("Invalid intrinsic");
            }
        }
    }
    private void load(Function f) {
        require(!constantRetired[f.id],"Initialized cache owner has been retired: "+f.label);
        if(constantReady[f.id]) {
            if(f.resultType==OBJ) result=constants[f.id];
            else scalarResult=(Long)constants[f.id];
            return;
        }
        call(f,new int[0]);
        // Pinned 4.33.1 load returns a borrowed cache-owned value. Explicit
        // IR inc instructions or an external owned entry acquire ownership.
        if(f.resultType==OBJ) constants[f.id]=result;
        else constants[f.id]=Long.valueOf(scalarResult);
        constantReady[f.id]=true;
    }
    private static void requireExecutableAbi(Function function) {
        Header header=function.header;
        if(header==null) return;
        if(function.resultType<0) throw error("Unsupported execution lane "+header.resultType+" in "+function.label+" ["+header.originalSha256+"]");
        for(int i=0;i<function.paramTypes.length;i++) if(function.paramTypes[i]<0)
            throw error("Unsupported execution lane "+header.paramTypes[i]+" in "+function.label+" ["+header.originalSha256+"]");
    }
    private static boolean buildIdentityPrimitive(int op) { return op==BUILD_GITHASH||op==BUILD_TARGET; }
    private void requireBuildIdentity() { require(buildIdentity!=null,"Producer build identity unavailable"); }
    private static void requireBuildUnit(Object value) {
        require(value instanceof Long&&((Long)value).longValue()==0,"Build identity requires canonical Unit zero");
    }
    private Function executionTarget(Function function) {
        if(function.intrinsic!=0||function.hostExtern!=null) return function;
        Header header=function.header;
        if(header==null||!header.kind.equals("extern")) return function;
        require(function.id>=0&&function.id<program.functions.length&&program.functions[function.id]==function,
                "Export origin outside current Program");
        Function target=program.guestExports[function.id];
        return target==null?function:target;
    }
    private Function preflightCallable(Function function) { return preflightCallable(function,false); }
    private Function preflightCallable(Function function,boolean allowCodeRequest) {
        requireExecutableAbi(function);
        require(!disposed,"Disposed task runtime cannot enter guest code");
        require(function.id<0||!constantRetired[function.id],"Initialized cache owner has been retired: "+function.label);
        Function target=executionTarget(function);
        if(target!=function) { requireExecutableAbi(target); function=target; }
        require(function.id<0||!constantRetired[function.id],"Initialized cache owner has been retired: "+function.label);
        if(function.intrinsic==PROFILE_IT) profilingGetter(function);
        if(buildIdentityPrimitive(function.intrinsic)) requireBuildIdentity();
        if(taskPrimitive(function.intrinsic)) require(taskRuntime!=null,"Logical synchronous task runtime is inactive");
        if(function.params.length==0&&constantReady[function.id]) return function;
        Header header=function.header;
        if(header!=null&&header.initialized()) throw error("Initialized global is unavailable: "+function.label);
        if(function.hostExtern!=null||function.intrinsic!=0) return function;
        if(header!=null&&header.kind.equals("extern")) throw error("Extern implementation unavailable: "+function.label);
        if(allowCodeRequest&&header!=null&&program.preparedBodies[function.id]==null) return function;
        preparedBody(function); return function;
    }
    private PreparedBody preparedBody(Function function) {
        require(function.id>=0&&function.id<program.functions.length
                &&program.functions[function.id]==function,"Function outside current Program");
        PreparedBody prepared=program.preparedBodies[function.id];
        if(prepared==null) throw error("Unprepared executable body: "+function.label);
        return prepared;
    }
    private void call(Function f,int[] args) {
        f=preflightCallable(f);
        if(f.hostExtern!=null) throw new UnsupportedOperationException("Host extern requires explicit driver: "+f.hostExtern.symbol);
        if(args.length!=f.params.length) throw error("Arity mismatch: "+f.label);
        if(f.intrinsic==TASK_MAP) { taskMapRecursive(taskMapArguments(args)); return; }
        if(f.intrinsic!=0) { intrinsicSlots(f,args); return; }
        PreparedBody prepared=preparedBody(f);
        int oldBp=bp,oldSp=sp,oldJbp=jbp,oldJsp=jsp;
        ensure(sp+prepared.width,jsp+prepared.joinWidth);
        for(int i=0;i<args.length;i++) {
            int source=oldBp+args[i],dest=oldSp+f.params[i];
            if(f.paramTypes[i]==OBJ) objects[dest]=obj(args[i]); else numbers[dest]=numbers[source];
        }
        bp=oldSp; sp+=prepared.width; jbp=oldJsp; jsp+=prepared.joinWidth;
        try { eval(f,prepared); }
        finally { Arrays.fill(objects,oldSp,sp,null); Arrays.fill(joins,oldJsp,jsp,null); bp=oldBp;sp=oldSp;jbp=oldJbp;jsp=oldJsp; }
    }
    private void enter(Function f,Object[] args) {
        f=preflightCallable(f);
        if(f.hostExtern!=null) throw new UnsupportedOperationException("Host extern requires explicit driver: "+f.hostExtern.symbol);
        if(args.length!=f.params.length) throw error("Arity mismatch: "+f.label);
        if(f.intrinsic==TASK_MAP) { taskMapRecursive(args); return; }
        if(f.intrinsic!=0) { intrinsicExternal(f,args); return; }
        PreparedBody prepared=preparedBody(f);
        int oldBp=bp,oldSp=sp,oldJbp=jbp,oldJsp=jsp;
        ensure(sp+prepared.width,jsp+prepared.joinWidth);
        for(int i=0;i<args.length;i++) if(f.paramTypes[i]!=OBJ) readSavedScalar(args[i],f.paramTypes[i]);
        for(int i=0;i<args.length;i++) { int dest=sp+f.params[i]; if(f.paramTypes[i]==OBJ) objects[dest]=args[i]; else numbers[dest]=readSavedScalar(args[i],f.paramTypes[i]); }
        bp=oldSp;sp+=prepared.width;jbp=oldJsp;jsp+=prepared.joinWidth;
        try { eval(f,prepared); }
        finally { Arrays.fill(objects,oldSp,sp,null); Arrays.fill(joins,oldJsp,jsp,null); bp=oldBp;sp=oldSp;jbp=oldJbp;jsp=oldJsp; }
    }
    private Object apply(Object value,Object[] args) {
        Node closure=node(value); if(closure.closure==null) throw error("Expected closure");
        acceptsClosure(closure);
        Function f=closure.closure,called=f;
        rootEntry(f);
        requireExecutableAbi(f);
        if(closure.fields.length+args.length>=f.params.length) {
            called=preflightCallable(f);
            if(buildIdentityPrimitive(f.intrinsic)) requireBuildUnit(closure.fields.length==0?args[0]:closure.fields[0]);
            if(f.intrinsic==BOOL_U64) requireBoolScalar(closure.fields.length==0?args[0]:closure.fields[0]);
        }
        Object[] combined=new Object[closure.fields.length+args.length];
        System.arraycopy(closure.fields,0,combined,0,closure.fields.length);
        // A shared closure keeps ownership of its captured arguments.
        if(!exclusive(closure)) for(Object a:closure.fields) inc(a,1);
        System.arraycopy(args,0,combined,closure.fields.length,args.length);
        if(exclusive(closure)) { closure.dead=true; Arrays.fill(closure.fields,null); shellDeletes++; }
        else releaseQuiet(closure,1);
        if(combined.length<f.params.length) return closure(f,combined);
        Object[] actual=combined.length==f.params.length?combined:Arrays.copyOf(combined,f.params.length);
        enter(called,actual); Object answer=called.resultType==OBJ?result:boxScalar(scalarResult,called.resultType);
        return combined.length==f.params.length?answer:apply(answer,Arrays.copyOfRange(combined,f.params.length,combined.length));
    }
    private Node closure(Function f,Object[] captured) {
        Node n=new Node(245,captured.length,0); n.closure=f; n.metadata=program.generation; System.arraycopy(captured,0,n.fields,0,captured.length); allocations++; return n;
    }
    private void expression(Expr e,int type,int dest,PreparedBody prepared) {
        switch(e.op) {
            case CTOR: {
                if(e.size==0&&e.scalarBytes==0) objects[dest]=Long.valueOf(e.tag);
                else { Node n=new Node(e.tag,e.size,e.scalarBytes); for(int i=0;i<e.size;i++) n.fields[i]=obj(e.args[i]); objects[dest]=n; allocations++; } break;
            }
            case PROJ: objects[dest]=constructorNode(obj(e.a)).fields[e.b]; break;
            case SPROJ: { Node n=constructorNode(obj(e.a)); numbers[dest]=readScalar(n,rawOffset(n,e.size,e.b),type); break; }
            case UPROJ: { Node n=constructorNode(obj(e.a)); numbers[dest]=readScalar(n,rawOffset(n,e.b,0),USIZE); break; }
            case FAP:
                if(e.target.intrinsic==POINTER_IDENTITY) pointerIdentity(e.target,e.args,prepared,e);
                else if(e.args.length==0) load(e.target); else call(e.target,e.args);
                if(type==OBJ) objects[dest]=result; else numbers[dest]=scalarResult; break;
            case PAP: { Object[] captured=new Object[e.args.length]; for(int i=0;i<captured.length;i++) captured[i]=obj(e.args[i]); objects[dest]=closure(e.target,captured); break; }
            case AP: { Object value=obj(e.a); Object[] args=new Object[e.args.length]; for(int i=0;i<args.length;i++) args[i]=obj(e.args[i]); objects[dest]=apply(value,args); break; }
            case BOX: objects[dest]=boxScalar(numbers[bp+e.a],e.b); break;
            case UNBOX: numbers[dest]=unboxScalar(obj(e.a),type); break;
            case LIT: if(type==OBJ) objects[dest]=e.literal; else numbers[dest]=(Long)e.literal; break;
            case SHARED: numbers[dest]=exclusive(node(obj(e.a)))?0:1; break;
            default: throw error("Invalid expression opcode");
        }
    }
    private void tick() { if(--callsLeft<0) throw error("Call/loop budget exhausted"); if((callsLeft&1023)==0&&Thread.currentThread().isInterrupted()) throw error("Interrupted"); }
    private void eval(Function f,PreparedBody prepared) {
        tick(); Body b=prepared.body;
        while(true) {
            switch(b.op) {
                case VDECL: {
                    Expr e=b.expr;
                    if(e.op==FAP&&executionTarget(e.target)==f&&b.next.op==RET&&b.next.a==b.a) {
                        int scratch=sp; ensure(sp+e.args.length,jsp);
                        for(int i=0;i<e.args.length;i++) { objects[scratch+i]=obj(e.args[i]); numbers[scratch+i]=numbers[bp+e.args[i]]; }
                        for(int i=0;i<e.args.length;i++) { objects[bp+f.params[i]]=objects[scratch+i]; numbers[bp+f.params[i]]=numbers[scratch+i]; objects[scratch+i]=null; }
                        tick(); b=prepared.body; break;
                    }
                    expression(e,b.type,bp+b.a,prepared); b=b.next; break;
                }
                case JDECL: joins[jbp+b.a]=b; b=b.next; break;
                case JMP: {
                    Body join=joins[jbp+b.a]; if(join==null||join.args.length!=b.args.length) throw error("Invalid join");
                    // Same sequential assignments as the pinned interpreter.
                    for(int i=0;i<b.args.length;i++) { int dest=bp+join.args[i],source=bp+b.args[i]; objects[dest]=obj(b.args[i]); numbers[dest]=numbers[source]; }
                    b=join.body; break;
                }
                case SET: { Node n=node(obj(b.a)); unique(n); n.fields[b.b]=obj(b.args[0]); stores++; b=b.next; break; }
                case SSET: { Node n=node(obj(b.a)); unique(n); writeScalar(n,rawOffset(n,b.tags[0],b.b),b.type,numbers[bp+b.args[0]]); stores++; b=b.next; break; }
                case USET: { Node n=node(obj(b.a)); unique(n); writeScalar(n,rawOffset(n,b.b,0),USIZE,numbers[bp+b.args[0]]); stores++; b=b.next; break; }
                case SETTAG: { Node n=node(obj(b.a)); unique(n); n.tag=b.b; b=b.next; break; }
                case INC: inc(obj(b.a),b.b); b=b.next; break;
                case DEC: releaseQuiet(obj(b.a),b.b); b=b.next; break;
                case DEL: deleteShell(obj(b.a)); b=b.next; break;
                case CASE: {
                    long tag=caseTag(b);
                    Body selected=null;
                    for(int i=0;i<b.tags.length;i++) if(b.tags[i]==tag||b.tags[i]==-1) { selected=b.alternatives[i]; break; }
                    if(selected==null) throw error("Incomplete case"); b=selected; break;
                }
                case RET: if(f.resultType==OBJ) result=obj(b.a); else scalarResult=numbers[bp+b.a]; return;
                case UNREACHABLE: throw error("Unreachable");
                default: throw error("Invalid body opcode");
            }
        }
    }

    /** Require actual ancestor/current image identity, never matching names or
     * coincident IDs. Private runtime functions retain the engine-owner guard. */
    private void acceptsClosure(Node closure) {
        Function function=closure.closure;
        require(function!=null,"Expected closure");
        require(!borrowedTaskPrimitive(function.intrinsic),"Borrowed task primitive requires owned guest wrapper");
        require(function.intrinsic!=NAME_EQ,"Borrowed Name equality cannot be admitted as a first-class closure");
        require(function.intrinsic!=EXPR_CACHE,"Borrowed Expr data requires an owned guest wrapper");
        require(function.intrinsic!=POINTER_IDENTITY,"Pointer identity cannot be admitted as a first-class closure");
        if(!(kindMetadata(closure) instanceof Generation)||!program.generation.accepts((Generation)kindMetadata(closure))) throw error("Closure belongs to another code image");
        if(function.privateOwner!=null) {
            if(function.privateOwner!=runtimeIdentity) throw error("Host closure belongs to another interpreter");
        } else require(function.id>=0&&function.id<program.functions.length&&program.functions[function.id]==function,
                       "Closure function identity differs from current code generation");
    }
    private void generationBoundary(String operation) {
        if(closed||disposed||advancing||untrackedFailure||(phase!=IDLE&&phase!=HOST_CALL&&phase!=CODE_CALL)||(!explicit&&sp!=0))
            throw new IllegalStateException(operation+" requires an open idle, host-call or code-call boundary");
    }
    /** Install only an actual descendant. Preserve all initialized cache owners
     * and readiness; new slots start unready. Both arrays are allocated before
     * the thread-confined publication, with no guest calls or initializer replay. */
    public void installProgram(Program descendant) {
        generationBoundary("Program installation");
        validateDescendant(descendant);
        if(descendant==program) return;
        Object[] nextConstants=Arrays.copyOf(constants,descendant.functions.length);
        boolean[] nextReady=Arrays.copyOf(constantReady,descendant.functions.length);
        boolean[] nextRetired=Arrays.copyOf(constantRetired,descendant.functions.length);
        constants=nextConstants; constantReady=nextReady; constantRetired=nextRetired; program=descendant;
    }
    private void validateDescendant(Program descendant) {
        require(descendant!=null,"Actual descendant Program required");
        require(descendant.generation.accepts(program.generation),"Program is not a descendant of the installed generation");
        require(descendant.functions.length>=program.functions.length,"Descendant function table shrank");
        for(int i=0;i<program.functions.length;i++) {
            require(descendant.functions[i]==program.functions[i],"Descendant replaced an inherited function");
            require(program.guestExports[i]==null||descendant.guestExports[i]==program.guestExports[i],
                    "Descendant replaced an inherited guest export binding");
            require(program.preparedBodies[i]==null||descendant.preparedBodies[i]==program.preparedBodies[i],
                    "Descendant replaced an inherited prepared body");
        }
    }
    private static int graphPosition(GraphRef reference,Map<Long,Integer> positions) {
        Integer position=positions.get(reference.sourceId);
        if(position==null) throw error("Prepared graph reference has no source object: "+reference.sourceId);
        return position;
    }
    private static void checkGraphReferences(Object[] values,Map<Long,Integer> positions) {
        for(Object value:values) if(value instanceof GraphRef) graphPosition((GraphRef)value,positions);
    }
    private static void enqueueGraphValues(Object[] values,Map<Long,Integer> positions,boolean[] visited,ArrayDeque<Integer> pending) {
        for(Object value:values) if(value instanceof GraphRef) {
            int position=graphPosition((GraphRef)value,positions);
            if(!visited[position]) { visited[position]=true; pending.addLast(position); }
        }
    }
    private static Object importedGraphValue(Object value,Map<Long,Integer> positions,Node[] shells) {
        if(value instanceof GraphRef) return shells[graphPosition((GraphRef)value,positions)];
        return value instanceof GraphInt?((GraphInt)value).runtimeValue:value;
    }
    private static void countGraphOwners(Object[] values,ImportNode[] nodes,Map<Long,Integer> positions,int[] owners) {
        for(Object value:values) if(value instanceof GraphRef) {
            int position=graphPosition((GraphRef)value,positions);
            if(nodes[position].sourceRC>0) owners[position]=Math.addExact(owners[position],1);
        }
    }
    /** Transactional default-RC0 or explicit selected-owner import at an open idle boundary. Returned
     * roots are independently OWNED values. Count each graph/cache/output
     * occurrence for source-positive nodes; source RC0 remains persistent.
     * Source-positive numeric counts are never copied or treated as bounds.
     * Closed cycles preserve native RC behavior, without cycle collection.
     * No guest code, body forcing, existing-node mutation or initializer runs.
     * One bootstrap graph per engine, including an empty graph; forks preserve
     * this marker. This is not incremental import of an overlapping snapshot.
     * Limits: 100k nodes/globals/owned roots, 1m total value occurrences,
     * 16 MiB each of scalar bytes and conservative immutable-carrier bytes.
     * Only wired values and lightweight per-global source provenance escape. */
    public Object[] installGraph(PreparedGraph graph) {
        if(closed||disposed||advancing||untrackedFailure||phase!=IDLE||pendingOwnedResult||sp!=0)
            throw new IllegalStateException("Prepared graph installation requires an open idle engine");
        require(graph!=null,"Actual PreparedGraph required");
        require(!graphInstalled,"Prepared graph has already been installed in this engine");
        Map<Long,Integer> positions=new HashMap<>();
        for(int i=0;i<graph.nodes.length;i++) {
            ImportNode node=graph.nodes[i];
            require(node.sourceRC>=0&&(graph.selectedOwners||node.sourceRC==0),
                    "Prepared graph source count differs from selected profile");
            require(positions.put(node.sourceId,i)==null,"Duplicate prepared graph source ID");
        }
        Function[] closureTargets=new Function[graph.nodes.length];
        for(int i=0;i<graph.nodes.length;i++) {
            ImportNode recipe=graph.nodes[i]; checkGraphReferences(recipe.fields,positions);
            if(recipe.kind==ImportNode.CLOSURE) {
                require(recipe.header.source==graph.binding,"Prepared closure source binding differs");
                Function target=program.functions[program.functionId(recipe.header)];
                requireExecutableAbi(target);
                require(target.resultType==OBJ,"Prepared closure requires boxed result");
                for(int lane:target.paramTypes) require(lane==OBJ,"Prepared closure requires boxed parameters");
                require(recipe.fields.length<target.params.length,"Invalid prepared partial application");
                require(!borrowedTaskPrimitive(target.intrinsic),"Borrowed task primitive requires owned guest wrapper");
                require(!borrowedArrayPrimitive(target.intrinsic),
                        "Borrowed array primitive requires owned closure wrapper");
                require(!borrowedIntPrimitive(target.intrinsic),"Borrowed Int primitive requires owned closure wrapper");
                require(!borrowedStringPositionPrimitive(target.intrinsic),"Borrowed String position primitive requires owned closure wrapper");
                require(target.intrinsic!=PROFILE_IT,"Borrowed profiling primitive requires an owned guest wrapper");
                require(!borrowedStringCompletionPrimitive(target.intrinsic),"Borrowed String range primitive requires owned closure wrapper");
                require(!borrowedBytePrimitive(target.intrinsic),"Borrowed ByteArray primitive requires owned closure wrapper");
                require(target.intrinsic!=NAME_EQ,"Borrowed Name equality requires an owned guest wrapper");
                require(target.intrinsic!=EXPR_CACHE,"Borrowed Expr data requires an owned guest wrapper");
                require(target.intrinsic!=POINTER_IDENTITY,"Pointer identity requires a certified direct FAP site");
                require(!borrowedRefPrimitive(target.intrinsic),"Borrowed ref primitive requires owned closure wrapper");
                closureTargets[i]=target;
            }
        }
        checkGraphReferences(graph.globalValues,positions); checkGraphReferences(graph.ownedRoots,positions);
        int[] globalIds=new int[graph.globals.length]; Set<Integer> uniqueGlobals=new HashSet<>();
        for(int i=0;i<globalIds.length;i++) {
            Header header=graph.globals[i];
            require(header.source==graph.binding,"Prepared global source binding differs");
            int id=program.functionId(header); Function function=program.functions[id];
            requireExecutableAbi(function);
            require(header.initialized()&&function.params.length==0&&function.resultType==OBJ,
                    "Prepared global requires an original boxed nullary initialized Header");
            require(uniqueGlobals.add(id),"Duplicate prepared global slot");
            require(!constantReady[id]&&!constantRetired[id],"Prepared global slot is occupied or retired"); globalIds[i]=id;
        }
        boolean[] visited=new boolean[graph.nodes.length]; ArrayDeque<Integer> pending=new ArrayDeque<>();
        enqueueGraphValues(graph.globalValues,positions,visited,pending);
        enqueueGraphValues(graph.ownedRoots,positions,visited,pending);
        while(!pending.isEmpty()) enqueueGraphValues(graph.nodes[pending.removeFirst()].fields,positions,visited,pending);
        for(boolean reachable:visited) require(reachable,"Unreachable object in prepared graph envelope");
        int[] owners=new int[graph.nodes.length];
        if(graph.selectedOwners) {
            for(ImportNode node:graph.nodes) countGraphOwners(node.fields,graph.nodes,positions,owners);
            countGraphOwners(graph.globalValues,graph.nodes,positions,owners);
            countGraphOwners(graph.ownedRoots,graph.nodes,positions,owners);
            for(int i=0;i<owners.length;i++) if(graph.nodes[i].sourceRC>0)
                require(owners[i]>0,"Source-positive object has no selected owning occurrence");
        }
        Node[] shells=new Node[graph.nodes.length];
        for(int i=0;i<shells.length;i++) {
            ImportNode recipe=graph.nodes[i]; Node shell=new Node(recipe.tag,recipe.fields.length,recipe.scalars.length);
            shell.rc=recipe.sourceRC==0?0:owners[i]; shell.array=recipe.kind==ImportNode.ARRAY; if(shell.array) shell.metadata=new ArrayState(recipe.fields.length); shell.ref=recipe.kind==ImportNode.REF;
            if(recipe.kind==ImportNode.BYTE_ARRAY) shell.metadata=new ByteArrayState(recipe.scalars.length);
            if(recipe.kind==ImportNode.CLOSURE) { shell.closure=closureTargets[i]; shell.metadata=program.generation; }
            System.arraycopy(recipe.scalars,0,shell.scalars,0,recipe.scalars.length); shells[i]=shell;
        }
        for(int i=0;i<shells.length;i++) for(int field=0;field<shells[i].fields.length;field++)
            shells[i].fields[field]=importedGraphValue(graph.nodes[i].fields[field],positions,shells);
        Object[] nextConstants=constants.clone(); boolean[] nextReady=constantReady.clone();
        Object[] outputs=new Object[graph.ownedRoots.length];
        for(int i=0;i<outputs.length;i++) outputs[i]=importedGraphValue(graph.ownedRoots[i],positions,shells);
        for(int i=0;i<globalIds.length;i++) {
            nextConstants[globalIds[i]]=importedGraphValue(graph.globalValues[i],positions,shells); nextReady[globalIds[i]]=true;
        }
        Map<Integer,PreparedGlobalSource> sources=new HashMap<>(preparedGlobalSources);
        PreparedGlobalSource source=new PreparedGlobalSource(graph.binding,graph.acceptedStateToken);
        for(int id:globalIds) sources.put(id,source);
        Map<Integer,PreparedGlobalSource> nextSources=Collections.unmodifiableMap(sources);
        long nextAllocations=Math.addExact(allocations,shells.length);
        constants=nextConstants; constantReady=nextReady; preparedGlobalSources=nextSources;
        allocations=nextAllocations; graphInstalled=true;
        return outputs;
    }

    /** Host-boundary PAP construction, not function execution. The caller
     * transfers capture credits once; array copying never retains the values.
     * Zero-arity/full/unboxed targets require their proper invocation/wrapper. */
    public Node makeClosure(int function,Object[] captures) {
        generationBoundary("Closure construction");
        require(captures!=null,"Explicit closure captures required");
        Function target=program.functions[function];
        requireExecutableAbi(target);
        require(captures.length<target.params.length,"Invalid partial application");
        require(!borrowedTaskPrimitive(target.intrinsic),"Borrowed task primitive requires owned guest wrapper");
                require(!borrowedArrayPrimitive(target.intrinsic),
                "Borrowed array primitive requires owned closure wrapper");
        require(!borrowedIntPrimitive(target.intrinsic),"Borrowed Int primitive requires owned closure wrapper");
        require(!borrowedStringPositionPrimitive(target.intrinsic),"Borrowed String position primitive requires owned closure wrapper");
        require(target.intrinsic!=PROFILE_IT,"Borrowed profiling primitive requires an owned guest wrapper");
        require(!borrowedStringCompletionPrimitive(target.intrinsic),"Borrowed String range primitive requires owned closure wrapper");
        require(!borrowedBytePrimitive(target.intrinsic),"Borrowed ByteArray primitive requires owned closure wrapper");
        require(target.intrinsic!=NAME_EQ,"Borrowed Name equality requires an owned guest wrapper");
        require(target.intrinsic!=EXPR_CACHE,"Borrowed Expr data requires an owned guest wrapper");
        require(target.intrinsic!=POINTER_IDENTITY,"Pointer identity requires a certified direct FAP site");
        require(!borrowedRefPrimitive(target.intrinsic),"Borrowed ref primitive requires owned closure wrapper");
        for(int lane:target.paramTypes) require(lane==OBJ,"Unboxed partial target unsupported; boxed wrapper required");
        Object[] captured=captures.clone();
        IdentityHashMap<Node,Integer> owners=new IdentityHashMap<>();
        for(Object value:captured) {
            validateHostObject(value);
            if(value instanceof Node) {
                Node node=(Node)value; owners.put(node,owners.getOrDefault(node,0)+1);
            }
        }
        for(Map.Entry<Node,Integer> credit:owners.entrySet())
            require(credit.getKey().rc==0||credit.getKey().rc>=credit.getValue(),"Insufficient owned closure capture credits");
        return closure(target,captured);
    }

    private void validateHostObject(Object value) {
        if(value instanceof Node) {
            Node n=node(value);
            require(n.rc>=0,"Invalid host object reference count");
            if(n.closure!=null) acceptsClosure(n);
        } else require(value instanceof Long||value instanceof BigInteger||value instanceof String,
                       "Host object outside baseline value profile");
    }
    private void suspendHost(Function f,Object[] args,Body next,int dest,int kind,Object[] surplus,boolean facade) {
        if(!explicit||hostRequest!=null) throw new IllegalStateException("Invalid nested host suspension");
        HostCall call=new HostCall();
        call.function=f; call.arguments=args.clone(); call.next=next; call.dest=dest;
        call.kind=kind; call.surplus=surplus; call.facade=facade;
        for(int i=0;i<call.arguments.length;i++) {
            if(f.paramTypes[i]==OBJ) validateHostObject(call.arguments[i]);
            else call.arguments[i]=saveScalar(readSavedScalar(call.arguments[i],f.paramTypes[i]),f.paramTypes[i]);
        }
        hostRequest=new HostRequest(runtimeIdentity,call); pc=next; phase=HOST_CALL; applicationEntry(kind);
    }
    /** A pending request is engine identity, not a serializable host capability. */
    public HostRequest pendingHostRequest() { return phase==HOST_CALL?hostRequest:null; }
    public HostRequest failureRequest() { return failedHostRequest; }
    public Throwable hostFailure() { return hostFailure; }
    /** Bounded text observer; returning the cause itself does not print its graph. */
    public String hostFailureMessage() {
        if(hostFailure==null) return null;
        String message;
        try { message=hostFailure.getMessage(); }
        catch(Throwable ignored) { message="Host failure message unavailable"; }
        if(message==null) message=hostFailure.getClass().getName();
        return message.substring(0,Math.min(900,message.length()));
    }
    /** One-time independent policy capture at an idle boundary. Source/catalogue
     * authentication belongs to the trusted adapter selecting these Headers. */
    public void configureHostGuestCalls(HostGuestPolicy policy) {
        explicitOnly();
        if(taskRuntime==null||advancing||disposed||untrackedFailure||phase!=IDLE||pendingOwnedResult||sp!=0
                ||continuationDepth!=0||runtimeAction!=null||hostGuestRecord!=null||hostGuestPolicy!=null)
            throw new IllegalStateException("Host guest policy requires an idle active runtime and may be configured once");
        require(policy!=null,"Actual host guest policy required");
        for(Header header:policy.outerHeaders) {
            Function function=program.functions[program.functionId(header)];
            require(function.header==header&&function.hostExtern!=null,"Allowed outer must be an actual captured Host Header");
        }
        for(Header header:policy.helperHeaders) validateHostGuestHelper(header);
        hostGuestPolicy=policy;
    }
    private Function validateHostGuestHelper(Header header) {
        require(header!=null,"Actual helper Header required");
        Function function=program.functions[program.functionId(header)];
        require(function.header==header&&header.kind.equals("fdecl")&&!header.initialized()
                &&function.intrinsic==0&&function.hostExtern==null&&function.params.length>0&&function.params.length<=64
                &&function.resultType==OBJ,"Host guest helper requires ordinary non-nullary boxed fdecl");
        for(int i=0;i<function.params.length;i++)
            require(function.paramTypes[i]==OBJ&&!header.borrowed[i],"Host guest helper requires owned boxed parameters; use an original boxed wrapper");
        return function;
    }
    private HostCall requireHostGuestOuter(HostRequest outer) {
        HostCall call=requireHostRequest(outer);
        require(taskRuntime!=null&&hostGuestPolicy!=null&&hostGuestPolicy.outer(call.function.header),"Host guest outer Header is not authorized");
        int depth=0;
        for(HostGuestRecord r=hostGuestRecord;r!=null;r=r.parent)
            require(++depth<1024,"Host guest operation nesting limit");
        return call;
    }
    private static void addCredit(IdentityHashMap<Node,Integer> credits,Object value,int count) {
        if(value instanceof Node&&count!=0) {
            Node node=(Node)value; credits.put(node,Math.addExact(credits.getOrDefault(node,0),count));
        }
    }
    private void reserveHostCall(HostCall call,IdentityHashMap<Node,Integer> credits,Set<Node> borrowed,boolean unclaimed,
                                 boolean[] moved) {
        for(int i=0;i<call.arguments.length;i++) if(call.function.paramTypes[i]==OBJ&&call.arguments[i] instanceof Node) {
            boolean transferred=call.argumentTransferred!=null&&call.argumentTransferred[i]||moved!=null&&moved[i];
            if(call.function.hostExtern.borrowed[i]) {
                if(call.facade) {
                    if(i>=call.borrowedCursor&&!(i==call.borrowedCursor&&call.adapterReleaseStarted)) addCredit(credits,call.arguments[i],1);
                } else if(unclaimed) borrowed.add((Node)call.arguments[i]);
            } else if(unclaimed&&!transferred) addCredit(credits,call.arguments[i],1);
        }
        if(!unclaimed&&call.resultOwned) addCredit(credits,call.completionResult,1);
    }
    /** Account only known reserved occurrences plus a distinct-node protection
     * floor for repeated FAP borrowed views. This is not an owner-graph proof. */
    private IdentityHashMap<Node,Integer> hostGuestReservations(HostCall outer,boolean[] moved) {
        IdentityHashMap<Node,Integer> credits=new IdentityHashMap<>();
        Set<Node> borrowed=Collections.newSetFromMap(new IdentityHashMap<Node,Boolean>());
        reserveHostCall(outer,credits,borrowed,true,moved);
        for(HostGuestRecord r=hostGuestRecord;r!=null;r=r.parent) {
            reserveHostCall(r.outer.call,credits,borrowed,true,null);
            if(r.argumentsOwned) for(Object value:r.arguments) addCredit(credits,value,r.release?r.count:1);
            if(r.resultOwned) addCredit(credits,r.result,1);
        }
        for(HostCall call=hostCompletion;call!=null;call=call.previousCompletion)
            reserveHostCall(call,credits,borrowed,false,null);
        for(Node value:borrowed) if(!credits.containsKey(value)) credits.put(value,1);
        return credits;
    }
    private Object[] preflightHostGuestArguments(HostRequest outer,HostGuestArgument[] descriptors,int count,
                                                boolean release,boolean[] moved) {
        require(descriptors!=null&&descriptors.length<=64,"Explicit host guest arguments required");
        Object[] values=new Object[descriptors.length]; HostCall call=outer.call;
        for(int i=0;i<values.length;i++) {
            HostGuestArgument descriptor=descriptors[i]; require(descriptor!=null,"Actual credit descriptor required");
            Object value;
            if(descriptor.outer!=null) {
                int index=descriptor.index;
                require(descriptor.outer==outer&&descriptor.outer.owner==runtimeIdentity&&index<call.arguments.length,
                        "Stale/foreign host argument transfer");
                require(!call.function.hostExtern.borrowed[index]&&call.function.paramTypes[index]==OBJ,
                        "Only an owned boxed outer argument can transfer");
                require(!moved[index]&&(call.argumentTransferred==null||!call.argumentTransferred[index]),"Host argument credit was already transferred");
                require(!release||count==1,"An outer slot supplies exactly one release credit");
                moved[index]=true; value=call.arguments[index];
            } else value=descriptor.value;
            validateHostObject(value); values[i]=value;
        }
        IdentityHashMap<Node,Integer> credits=hostGuestReservations(call,moved);
        for(Object value:values) addCredit(credits,value,release?count:1);
        for(Map.Entry<Node,Integer> entry:credits.entrySet()) {
            Node value=entry.getKey(); validateHostObject(value);
            require(value.rc==0||value.rc>=entry.getValue(),"Insufficient unreserved host guest owner credits");
        }
        return values;
    }
    private HostGuestRecord prepareHostGuestOperation(HostRequest outer,Header helper,Object[] args,int[] slots,
                                                     boolean release,int count) {
        HostGuestRecord record=new HostGuestRecord();
        record.outer=outer; record.helper=helper; record.arguments=args; record.movedSlots=slots;
        record.release=release; record.count=count; record.argumentsOwned=true;
        record.caller=active; record.callerPrepared=activePrepared; record.savedPc=pc;
        record.bp=bp; record.sp=sp; record.jbp=jbp; record.jsp=jsp; record.depth=continuationDepth;
        record.scope=currentTask; record.completionBase=hostCompletion;
        record.token=new HostGuestOperation(runtimeIdentity,record);
        record.action=newAction(ACTION_HOST_GUEST,null,null,-1,ASSIGN,null); record.action.guest=record;
        return record;
    }
    private void parkHostGuestOperation(HostGuestRecord record,boolean[] moved) {
        HostCall call=record.outer.call;
        // Allocate bookkeeping before parking or transferring any credit.
        boolean[] transferred=call.argumentTransferred==null?new boolean[call.arguments.length]:call.argumentTransferred.clone();
        for(int i=0;i<moved.length;i++) if(moved[i]) transferred[i]=true;
        record.parent=hostGuestRecord; hostGuestRecord=record; call.argumentTransferred=transferred;
        hostRequest=null; phase=RUNNING; publishAction(record.action);
    }
    public HostGuestOperation startHostGuestCall(HostRequest outer,Header helper,HostGuestArgument[] arguments) {
        HostCall call=requireHostGuestOuter(outer);
        require(hostGuestPolicy.helper(helper),"Host guest helper Header is not authorized");
        Function function=validateHostGuestHelper(helper);
        require(arguments!=null&&arguments.length==function.params.length,"Host guest helper arity mismatch");
        boolean[] moved=new boolean[call.arguments.length];
        Object[] values=preflightHostGuestArguments(outer,arguments,1,false,moved);
        validateEntryArguments(function,values);
        int[] slots=new int[values.length]; Arrays.fill(slots,-1);
        for(int i=0;i<values.length;i++) if(arguments[i].outer!=null) slots[i]=arguments[i].index;
        HostGuestRecord record=prepareHostGuestOperation(outer,helper,values,slots,false,1); record.function=function;
        parkHostGuestOperation(record,moved); return record.token;
    }
    public HostGuestOperation startHostRelease(HostRequest outer,HostGuestArgument argument,int count) {
        HostCall call=requireHostGuestOuter(outer); require(count>=0,"Negative host release count");
        boolean[] moved=new boolean[call.arguments.length];
        Object[] values=preflightHostGuestArguments(outer,new HostGuestArgument[]{argument},count,true,moved);
        int[] slots=new int[]{argument.outer==null?-1:argument.index};
        HostGuestRecord record=prepareHostGuestOperation(outer,null,values,slots,true,count);
        parkHostGuestOperation(record,moved); return record.token;
    }
    /** Current token also exposes the child's parked outer identity after fork. */
    public HostGuestOperation currentHostGuestOperation() { return hostGuestRecord==null?null:hostGuestRecord.token; }
    public HostGuestOperation pendingHostGuestResult() { return phase==HOST_GUEST_RESULT?currentHostGuestOperation():null; }
    public Object takeHostGuestResult(HostRequest outer,HostGuestOperation operation) {
        explicitOnly();
        if(advancing||operation==null||operation.owner!=runtimeIdentity||hostGuestRecord!=operation.record
                ||phase!=HOST_GUEST_RESULT||operation.record.outer!=outer||!operation.record.complete||operation.record.taken)
            throw new IllegalStateException("Stale/foreign host guest result claim");
        HostGuestRecord record=operation.record; Object value=record.result;
        record.taken=true; record.resultOwned=false; hostGuestRecord=record.parent;
        hostRequest=record.outer; phase=HOST_CALL;
        record.parent=null; record.result=null; record.arguments=null; record.scope=null; record.completionBase=null;
        record.action=null; record.function=null; record.caller=null; record.callerPrepared=null; record.savedPc=null;
        return value;
    }
    private void hostGuestEntry(Function function,Object[] args) {
        HostGuestRecord record=hostGuestRecord;
        if(record!=null&&record.action==runtimeAction&&record.function==function&&record.arguments==args&&!record.entered) {
            record.entered=true; record.argumentsOwned=false;
        }
    }
    private void stepHostGuest(RuntimeAction action) {
        HostGuestRecord record=action.guest;
        require(record!=null&&hostGuestRecord==record,"Host guest operation order differs");
        if(action.stage==0) {
            action.stage=1;
            if(record.release) {
                boolean dispatched=beginRelease(record.arguments[0],record.count,ACTION_BODY,true);
                record.releaseClaimed=true; record.argumentsOwned=false;
                if(dispatched) return;
            } else {
                enterExplicit(record.function,null,record.arguments,ACTION_BODY,action.slot,ASSIGN,null); return;
            }
        }
        record.result=record.release?ERASED:objects[action.slot]; record.resultOwned=true;
        require(active==record.caller&&activePrepared==record.callerPrepared&&bp==record.bp&&jbp==record.jbp&&jsp==record.jsp
                &&continuationDepth==record.depth&&currentTask==record.scope&&hostCompletion==record.completionBase,
                "Host guest return did not restore its control prefix");
        objects[action.slot]=null; sp=action.savedSp; runtimeAction=action.parent; pc=record.savedPc;
        record.complete=true; phase=HOST_GUEST_RESULT;
    }

    private HostCall requireHostRequest(HostRequest request) {
        explicitOnly();
        if(advancing) throw new IllegalStateException("Reentrant host completion");
        if(request==null||request.owner!=runtimeIdentity||phase!=HOST_CALL||hostRequest!=request||request.call.replyClaimed)
            throw new IllegalStateException("Stale or foreign host request");
        return request.call;
    }
    /** Check only known adapter and reply credits, never infer ownership from
     * stale registers. Persistent nodes have the existing unlimited-credit rule. */
    private void preflightHostCompletion(HostCall call,Object reply) {
        IdentityHashMap<Node,Integer> owners;
        if(hostGuestRecord!=null) {
            // Owned current-call inputs remain the handler's obligations and
            // may transfer as its reply. Parked ancestor escrows may not.
            boolean[] transferred=new boolean[call.arguments.length]; Arrays.fill(transferred,true);
            owners=hostGuestReservations(call,transferred);
        } else {
            owners=new IdentityHashMap<>();
            if(call.facade) for(int i=call.borrowedCursor;i<call.arguments.length;i++)
                if(call.function.hostExtern.borrowed[i]&&call.arguments[i] instanceof Node)
                    addCredit(owners,node(call.arguments[i]),1);
        }
        if(call.function.resultType==OBJ&&reply instanceof Node) {
            Node value=node(reply); owners.put(value,owners.getOrDefault(value,0)+1);
        }
        for(Map.Entry<Node,Integer> credit:owners.entrySet()) {
            Node value=node(credit.getKey());
            require(value.rc==0||value.rc>=credit.getValue(),
                    "Insufficient host reply or reserved owner credits");
        }
    }
    private void markHostFailure(HostRequest request,Throwable cause) {
        hostRequest=null; failedHostRequest=request; hostCompletion=request.call;
        hostFailure=cause; pendingOwnedResult=false; phase=FAILED;
    }
    /** Consume one valid reply. Object replies transfer ONE owned result; an
     * owned argument may be returned by transfer. No owned argument is released
     * automatically. Release only the root/AP adapter's known borrowed credits.
     * Invalid identity/lane/credit replies leave the suspension unchanged. Any
     * error after claim is terminal with request/result/cursor diagnostics. */
    public void resumeHost(HostRequest request,Object reply) {
        HostCall call=requireHostRequest(request);
        long scalar=0;
        if(call.function.resultType==OBJ) validateHostObject(reply);
        else scalar=inputScalar(reply,call.function.resultType);
        preflightHostCompletion(call,reply);
        RuntimeAction action=taskRuntime==null?null:newAction(ACTION_HOST,call.function,call.next,call.dest,call.kind,call.surplus);
        call.replyClaimed=true; call.completionResult=reply; call.completionScalar=scalar;
        call.resultOwned=call.function.resultType==OBJ;
        call.previousCompletion=hostCompletion;
        hostRequest=null; hostCompletion=call;
        if(action!=null) { action.completion=call; action.request=request; publishAction(action); phase=RUNNING; return; }
        advancing=true;
        try {
            if(call.facade) while(call.borrowedCursor<call.arguments.length) {
                int index=call.borrowedCursor;
                if(call.function.hostExtern.borrowed[index]) {
                    call.adapterReleaseStarted=true;
                    releaseQuiet(call.arguments[index],1);
                    call.adapterReleaseStarted=false;
                }
                call.borrowedCursor++;
            }
            phase=RUNNING;
            if((call.kind&ROOT)!=0) {
                if(call.function.resultType==OBJ) result=reply; else scalarResult=scalar;
                call.resultOwned=false; pendingOwnedResult=true; phase=COMPLETE;
            } else if((call.kind&APPLY)!=0) {
                Object answer=call.function.resultType==OBJ?reply:boxScalar(scalar,call.function.resultType);
                call.completionResult=answer; call.resultOwned=true;
                if(call.surplus==null) { objects[call.dest]=answer; pc=call.next; call.resultOwned=false; }
                else {
                    // Validate the AP receiver before beginning its owned transfer.
                    Node closure=node(answer);
                    require(closure.closure!=null,"Expected closure");
                    acceptsClosure(closure);
                    call.resultTransferStarted=true; call.resultOwned=false;
                    applyExplicit(answer,call.surplus,call.next,call.dest);
                }
            } else {
                if(call.function.resultType==OBJ) objects[call.dest]=reply; else numbers[call.dest]=scalar;
                pc=call.next; call.resultOwned=false;
            }
            hostCompletion=call.previousCompletion;
        } catch(Throwable failure) { markHostFailure(request,failure); throw failure; }
        finally { advancing=false; }
    }
    /** Terminal external failure preserves all outstanding argument/facade
     * obligations and frames. No host effect, argument release, or replay occurs. */
    public void failHost(HostRequest request,Throwable cause) {
        requireHostRequest(request);
        if(cause==null) throw error("Host failure cause required");
        request.call.replyClaimed=true;
        request.call.previousCompletion=hostCompletion;
        markHostFailure(request,cause);
    }

    private void suspendCode(Function function,int[] slots,Object[] args,Body next,int dest,int kind,Object[] surplus) {
        if(!explicit||codeRequest!=null||hostRequest!=null) throw new IllegalStateException("Invalid nested code suspension");
        require(function.header!=null&&function.header.kind.equals("fdecl"),"Source fdecl Header required for code demand");
        CodeActivation activation=new CodeActivation();
        activation.function=function; activation.next=next; activation.dest=dest; activation.kind=kind;
        activation.surplus=surplus;
        if(slots==null) {
            activation.arguments=args.clone();
            for(int i=0;i<args.length;i++) if(function.paramTypes[i]!=OBJ)
                activation.arguments[i]=saveScalar(readSavedScalar(args[i],function.paramTypes[i]),function.paramTypes[i]);
        }
        else {
            activation.arguments=new Object[slots.length];
            for(int i=0;i<slots.length;i++) activation.arguments[i]=function.paramTypes[i]==OBJ
                    ?obj(slots[i]):saveScalar(numbers[bp+slots[i]],function.paramTypes[i]);
        }
        codeRequest=new CodeRequest(runtimeIdentity,activation); pc=next; phase=CODE_CALL; applicationEntry(kind); hostGuestEntry(function,args);
    }
    public CodeRequest pendingCodeRequest() { return phase==CODE_CALL?codeRequest:null; }
    public CodeRequest failureCodeRequest() { return failedCodeRequest; }
    public Throwable codeFailure() { return codeFailure; }
    public String codeFailureMessage() {
        if(codeFailure==null) return null;
        String message;
        try { message=codeFailure.getMessage(); }
        catch(Throwable ignored) { message="Code failure message unavailable"; }
        if(message==null) message=codeFailure.getClass().getName();
        return message.substring(0,Math.min(900,message.length()));
    }
    private CodeActivation requireCodeRequest(CodeRequest request) {
        explicitOnly();
        if(advancing) throw new IllegalStateException("Reentrant code completion");
        if(request==null||request.owner!=runtimeIdentity||phase!=CODE_CALL||codeRequest!=request||request.activation.claimed)
            throw new IllegalStateException("Stale or foreign code request");
        return request.activation;
    }
    private void markCodeFailure(CodeRequest request,Throwable cause) {
        codeRequest=null; failedCodeRequest=request; codeFailure=cause;
        pendingOwnedResult=false; phase=FAILED;
    }
    /** Install an actual materialized descendant and enter the saved activation
     * once. Every rejection before claim preserves Program, request and owners.
     * Postclaim entry failure is terminal, with activation diagnostics retained. */
    public void resumeCode(CodeRequest request,Program descendant) {
        CodeActivation activation=requireCodeRequest(request);
        validateDescendant(descendant);
        Function function=activation.function;
        require(function.id<descendant.functions.length&&descendant.functions[function.id]==function
                &&function.header==request.header(),"Code reply changed the requested Header");
        PreparedBody prepared=descendant.preparedBodies[function.id];
        require(prepared!=null&&prepared.body!=null,"Code reply has no requested prepared body");
        requireExecutableAbi(function);
        validateEntryArguments(function,activation.arguments,true);
        if(continuationDepth>=65536) throw error("Continuation depth limit");
        int newSp=Math.addExact(sp,prepared.width),newJsp=Math.addExact(jsp,prepared.joinWidth);
        if(newSp>8_000_000||newJsp>2_000_000) throw error("Explicit stack limit");
        Object[] nextConstants=constants; boolean[] nextReady=constantReady,nextRetired=constantRetired;
        if(descendant!=program) {
            nextConstants=Arrays.copyOf(constants,descendant.functions.length);
            nextReady=Arrays.copyOf(constantReady,descendant.functions.length);
            nextRetired=Arrays.copyOf(constantRetired,descendant.functions.length);
        }
        Object[] nextObjects=objects; long[] nextNumbers=numbers; Body[] nextJoins=joins;
        if(newSp>objects.length) {
            int capacity=Math.max(newSp,objects.length*2);
            nextObjects=Arrays.copyOf(objects,capacity); nextNumbers=Arrays.copyOf(numbers,capacity);
        }
        if(newJsp>joins.length) nextJoins=Arrays.copyOf(joins,Math.max(newJsp,joins.length*2));
        Continuation[] nextContinuations=continuations;
        if(continuationDepth==continuations.length)
            nextContinuations=Arrays.copyOf(continuations,continuations.length*2);
        if(nextContinuations[continuationDepth]==null) {
            if(nextContinuations==continuations) nextContinuations=continuations.clone();
            nextContinuations[continuationDepth]=new Continuation();
        }
        activation.claimed=true; codeRequest=null; advancing=true;
        try {
            constants=nextConstants; constantReady=nextReady; constantRetired=nextRetired; program=descendant;
            objects=nextObjects; numbers=nextNumbers; joins=nextJoins; continuations=nextContinuations;
            phase=RUNNING;
            enterExplicit(function,null,activation.arguments,activation.next,activation.dest,activation.kind,activation.surplus);
        } catch(Throwable failure) { markCodeFailure(request,failure); throw failure; }
        finally { advancing=false; }
    }
    /** No replay or blanket cleanup: original argument obligations remain. */
    public void failCode(CodeRequest request,Throwable cause) {
        requireCodeRequest(request);
        if(cause==null) throw error("Code failure cause required");
        request.activation.claimed=true; markCodeFailure(request,cause);
    }

    private void explicitOnly() {
        if(!explicit) throw new IllegalStateException("Explicit mode required");
        if(closed) throw new IllegalStateException("Interpreter closed");
    }
    /** No automatic queued work is implied; pending pure dependencies may still
     * exist. Root completion alone does not discharge BaseIO keepalive credits. */
    public boolean taskRuntimeQuiescent() {
        if(untrackedFailure||phase==FAILED||phase==RUNNING||hostGuestRecord!=null||runtimeAction!=null||currentTask!=null||hostCompletion!=null||hostRequest!=null||codeRequest!=null) return false;
        for(TaskRecord record:taskRecords.values()) if(record.keepalive) return false;
        return true;
    }
    public String phase() { return new String[]{"idle","running","complete","failed","host-call","code-call","waiting","host-guest-result"}[phase]; }
    public int continuationDepth() { return continuationDepth; }
    public long instructionCount() { return instructions; }
    public String activeFunction() { return active==null?null:active.label; }

    /** Both drivers reject invalid input closures before publishing frames,
     * taking owned arguments, or running any guest operation. */
    private void validateEntryArguments(Function function,Object[] args) { validateEntryArguments(function,args,false); }
    private void validateEntryArguments(Function function,Object[] args,boolean saved) {
        if(args==null||args.length!=function.params.length) throw error("Arity mismatch: "+function.label);
        if(buildIdentityPrimitive(function.intrinsic)) requireBuildUnit(args[0]);
        if(function.intrinsic==BOOL_U64) requireBoolScalar(args[0]);
        if(function.intrinsic==TASK_MAP&&taskRuntime==null) validateTaskMap(args);
        if(taskRuntime!=null&&function.intrinsic==TASK_PURE) {
            require(ERASED.equals(args[0]),"Task.pure erased placeholder required"); validateHostObject(args[1]);
        }
        if(taskRuntime!=null&&function.intrinsic==TASK_GET) {
            require(ERASED.equals(args[0]),"Task.get erased placeholder required"); readyTaskNode(args[1]);
        }
        if(actionPrimitive(function)) validateNative(function,args);
        for(int i=0;i<args.length;i++) {
            if(function.paramTypes[i]!=OBJ) { if(saved) readSavedScalar(args[i],function.paramTypes[i]); else inputScalar(args[i],function.paramTypes[i]); }
            else if(args[i] instanceof Double||args[i] instanceof F64Bits) throw error("Float scalar is not an OBJ value");
            else if(args[i] instanceof Node) {
                Node value=node(args[i]);
                if(value.closure!=null) acceptsClosure(value);
            }
        }
    }

    /** Bind an owned external invocation, without executing its body. */
    public void start(int function,Object[] args) {
        explicitOnly();
        if(advancing||phase!=IDLE||(taskRuntime!=null&&(disposed||untrackedFailure))) throw new IllegalStateException("Take the result or finish the current execution before start");
        Function f=program.functions[function];
        rootEntry(f);
        f=preflightCallable(f,true);
        validateEntryArguments(f,args);
        if(f.params.length==0&&constantReady[f.id]) {
            if(f.resultType==OBJ) { result=constants[f.id]; inc(result,1); }
            else scalarResult=(Long)constants[f.id];
            callsLeft=10_000_000; instructions=0;
            entry=f; phase=COMPLETE; pendingOwnedResult=true; return;
        }
        if(actionPrimitive(f)) {
            enterNative(f,args,null,0,ROOT,null);
            callsLeft=10_000_000; instructions=0; entry=f; phase=RUNNING; return;
        }
        if(f.intrinsic==TASK_MAP) {
            enterTaskMap(f,null,args,null,0,ROOT,null);
            callsLeft=10_000_000; instructions=0; entry=f; phase=RUNNING; return;
        }
        if(f.hostExtern!=null) {
            for(int i=0;i<args.length;i++) if(f.paramTypes[i]==OBJ) validateHostObject(args[i]);
            callsLeft=10_000_000; instructions=0; entry=f;
            suspendHost(f,args,null,0,ROOT,null,true); return;
        }
        if(f.intrinsic!=0) {
            try { intrinsicExternal(f,args); }
            catch(Throwable failure) { untrackedFailure=true; throw failure; }
            callsLeft=10_000_000; instructions=0;
            entry=f; phase=COMPLETE; pendingOwnedResult=true; return;
        }
        callsLeft=10_000_000; instructions=0;
        entry=f; phase=RUNNING;
        try { enterExplicit(f,null,args,null,0,ROOT|(f.params.length==0?CACHE:0),null); }
        catch(Throwable failure) { phase=FAILED; throw failure; }
    }

    private void enterExplicit(Function f,int[] slots,Object[] args,Body next,int dest,int kind,Object[] surplus) {
        if(continuationDepth>=65536) throw error("Continuation depth limit");
        f=preflightCallable(f,true);
        if(program.preparedBodies[f.id]==null) {
            suspendCode(f,slots,args,next,dest,kind,surplus); return;
        }
        PreparedBody prepared=preparedBody(f);
        int newSp=Math.addExact(sp,prepared.width),newJsp=Math.addExact(jsp,prepared.joinWidth);
        if(newSp>8_000_000||newJsp>2_000_000) throw error("Explicit stack limit");
        ensure(newSp,newJsp);
        if(continuationDepth==continuations.length) continuations=Arrays.copyOf(continuations,continuations.length*2);
        Continuation k=continuations[continuationDepth];
        if(k==null) continuations[continuationDepth]=k=new Continuation();
        for(int i=0;i<f.params.length;i++) {
            int target=sp+f.params[i];
            if(slots!=null) {
                if(f.paramTypes[i]==OBJ) objects[target]=obj(slots[i]); else numbers[target]=numbers[bp+slots[i]];
            } else {
                if(f.paramTypes[i]==OBJ) objects[target]=args[i]; else numbers[target]=readSavedScalar(args[i],f.paramTypes[i]);
            }
        }
        k.caller=active; k.callerPrepared=activePrepared; k.next=next; k.bp=bp; k.sp=sp; k.jbp=jbp; k.jsp=jsp;
        k.dest=dest; k.kind=kind; k.surplus=surplus;
        continuationDepth++;
        bp=sp; sp=newSp; jbp=jsp; jsp=newJsp; active=f; activePrepared=prepared; pc=prepared.body; applicationEntry(kind); hostGuestEntry(f,args);
        tick();
    }

    /** Prepare and consume one AP exactly once; no guest execution here. */
    private boolean prepareExplicitApply(Object value,Object[] args) {
        Node closure=node(value); if(closure.closure==null) throw error("Expected closure");
        acceptsClosure(closure);
        Function f=closure.closure,called=f;
        rootEntry(f);
        requireExecutableAbi(f);
        if(closure.fields.length+args.length>=f.params.length) {
            called=preflightCallable(f,true);
            if(buildIdentityPrimitive(f.intrinsic)) requireBuildUnit(closure.fields.length==0?args[0]:closure.fields[0]);
            if(f.intrinsic==BOOL_U64) requireBoolScalar(closure.fields.length==0?args[0]:closure.fields[0]);
        }
        Object[] combined=new Object[closure.fields.length+args.length];
        System.arraycopy(closure.fields,0,combined,0,closure.fields.length);
        System.arraycopy(args,0,combined,closure.fields.length,args.length);
        if(combined.length>=f.params.length&&taskRuntime!=null) {
            Object[] actual=combined.length==f.params.length?combined:Arrays.copyOf(combined,f.params.length);
            if(actionPrimitive(f)) validateNative(f,actual);
            else if(f.intrinsic==TASK_GET||f.intrinsic==TASK_PURE) validateEntryArguments(f,actual,true);
        }
        if(taskRuntime!=null) {
            applicationArgs=combined; applicationCaptureCount=closure.fields.length;
            applicationRetainedCaptures=0; applicationArgumentsOwned=false;
        }
        if(!exclusive(closure)) for(Object capture:closure.fields) {
            inc(capture,1); if(taskRuntime!=null) applicationRetainedCaptures++;
        }
        if(taskRuntime!=null) applicationResultOwned=false;
        if(exclusive(closure)) { closure.dead=true; Arrays.fill(closure.fields,null); shellDeletes++; }
        else releaseQuiet(closure,1);
        if(taskRuntime!=null) applicationArgumentsOwned=true;
        if(combined.length<f.params.length) {
            result=closure(f,combined);
            if(taskRuntime!=null) { applicationArgumentsOwned=false; applicationResult=result; applicationResultOwned=true; }
            return false;
        }
        applicationTarget=called;
        applicationArgs=combined.length==f.params.length?combined:Arrays.copyOf(combined,f.params.length);
        applicationSurplus=combined.length==f.params.length?null:Arrays.copyOfRange(combined,f.params.length,combined.length);
        return true;
    }
    private void applyExplicit(Object value,Object[] args,Body next,int dest) {
        while(true) {
            if(taskRuntime!=null) {
                applicationResult=value; applicationResultOwned=true; applicationArgumentsOwned=true;
                applicationArgs=args; applicationSurplus=null; applicationTarget=null;
                applicationCaptureCount=0; applicationRetainedCaptures=0;
            }
            if(!prepareExplicitApply(value,args)) {
                objects[dest]=result; pc=next; if(taskRuntime!=null) clearApplication(); return;
            }
            Function f=applicationTarget; Object[] actual=applicationArgs,rest=applicationSurplus;
            if(taskRuntime==null) { applicationTarget=null; applicationArgs=null; applicationSurplus=null; }
            if(f.hostExtern!=null) {
                suspendHost(f,actual,next,dest,APPLY,rest,true); if(taskRuntime!=null) clearApplication(); return;
            }
            if(actionPrimitive(f)) { enterNative(f,actual,next,dest,APPLY,rest); clearApplication(); return; }
            if(f.intrinsic==TASK_MAP) { enterTaskMap(f,null,actual,next,dest,APPLY,rest); return; }
            if(f.intrinsic==0) {
                enterExplicit(f,null,actual,next,dest,APPLY,rest); if(taskRuntime!=null) clearApplication(); return;
            }
            intrinsicExternal(f,actual);
            if(taskRuntime!=null) applicationArgumentsOwned=false;
            value=f.resultType==OBJ?result:boxScalar(scalarResult,f.resultType);
            if(taskRuntime!=null) { applicationResult=value; applicationResultOwned=true; }
            if(rest==null) { objects[dest]=value; pc=next; if(taskRuntime!=null) clearApplication(); return; }
            args=rest;
        }
    }
    private void returnExplicit() {
        Function completed=active;
        Continuation k=continuations[--continuationDepth];
        int kind=k.kind,dest=k.dest; Body next=k.next; Object[] surplus=k.surplus;
        if((kind&CACHE)!=0) {
            constants[completed.id]=completed.resultType==OBJ?result:Long.valueOf(scalarResult);
            constantReady[completed.id]=true;
        }
        Arrays.fill(objects,k.sp,sp,null); Arrays.fill(joins,k.jsp,jsp,null);
        bp=k.bp; sp=k.sp; jbp=k.jbp; jsp=k.jsp; active=k.caller; activePrepared=k.callerPrepared; pc=next;
        k.clear();
        if((kind&ROOT)!=0) {
            if(entry.params.length==0&&entry.resultType==OBJ) inc(result,1);
            pendingOwnedResult=true; phase=COMPLETE; return;
        }
        if((kind&APPLY)!=0) {
            Object answer=completed.resultType==OBJ?result:boxScalar(scalarResult,completed.resultType);
            if(surplus==null) objects[dest]=answer; else applyExplicit(answer,surplus,next,dest);
        } else {
            if(completed.resultType==OBJ) objects[dest]=result; else numbers[dest]=scalarResult;
        }
    }

    /** New engine-level body-dispatch budget, not the legacy World fuel ABI.
     * Calls commit their continuation before pause; RET restoration is atomic.
     * Self-tail elimination consumes its VDECL and has no deferred RET frame.
     * A root release charges one field edge or shell transition/completion per
     * unit; it has no source Function, PC, or guest body instruction. */
    public boolean advance(long budget) {
        explicitOnly();
        if(budget<0) throw error("Negative instruction budget");
        if(advancing) throw new IllegalStateException("Reentrant advance");
        if(phase==COMPLETE) return true;
        if(phase==HOST_CALL||phase==CODE_CALL||phase==WAITING||phase==HOST_GUEST_RESULT) return false;
        if(phase!=RUNNING) throw new IllegalStateException("No resumable execution: "+phase());
        advancing=true;
        try {
            if(releaseTransaction!=null) runReleaseLoop(budget); else runExplicitLoop(budget);
            return phase==COMPLETE;
        }
        catch(Throwable failure) { phase=FAILED; throw failure; }
        finally { advancing=false; }
    }
    private void runExplicitLoop(long budget) {
        Body b=pc;
            while(phase==RUNNING&&budget-->0) {
                // Keep the dispatch cursor local. Publish the attempted body
                // for failures and let control-transfer helpers publish callees.
                pc=b; instructions++;
                if(b==ACTION_BODY) { stepAction(); b=pc; continue; }
                switch(b.op) {
                    case MAP_APPLY: {
                        requireTaskMapFrame(b); tick(); int base=bp;
                        Node task=(Node)objects[base+2]; Object value=task.fields[0];
                        inc(value,1); objects[base+4]=value; numbers[base+7]=1;
                        numbers[base+7]=2; releaseQuiet(task,1); objects[base+2]=null; numbers[base+7]=3;
                        Object[] args=(Object[])objects[base+6]; args[0]=value;
                        numbers[base+7]=4;
                        applyExplicit(objects[base+1],args,b.next,base+3);
                        objects[base+1]=null; objects[base+4]=null; objects[base+5]=null; objects[base+6]=null;
                        numbers[base+7]=5; b=pc; break;
                    }
                    case MAP_WRAP: {
                        requireTaskMapFrame(b);
                        Node task=newReadyTask(objects[bp+3]); objects[bp+3]=null;
                        result=task; numbers[bp+7]=6; returnExplicit(); b=pc; break;
                    }
                    case VDECL: {
                        Expr e=b.expr; int dest=bp+b.a;
                        if(e.op==FAP) {
                            Function f=executionTarget(e.target);
                            if(f!=active) f=preflightCallable(f,true);
                            if(f==active&&b.next.op==RET&&b.next.a==b.a) {
                                int scratch=sp; ensure(sp+e.args.length,jsp);
                                for(int i=0;i<e.args.length;i++) { objects[scratch+i]=obj(e.args[i]); numbers[scratch+i]=numbers[bp+e.args[i]]; }
                                for(int i=0;i<e.args.length;i++) { objects[bp+f.params[i]]=objects[scratch+i]; numbers[bp+f.params[i]]=numbers[scratch+i]; objects[scratch+i]=null; }
                                tick(); b=activePrepared.body;
                            } else if(e.args.length==0&&constantReady[f.id]) {
                                if(f.resultType==OBJ) objects[dest]=constants[f.id]; else numbers[dest]=(Long)constants[f.id];
                                b=b.next;
                            } else if(f.hostExtern!=null) {
                                Object[] args=new Object[e.args.length];
                                for(int i=0;i<args.length;i++) args[i]=f.paramTypes[i]==OBJ?obj(e.args[i]):saveScalar(numbers[bp+e.args[i]],f.paramTypes[i]);
                                suspendHost(f,args,b.next,dest,ASSIGN,null,false); b=pc;
                            } else if(actionPrimitive(f)) {
                                enterNative(f,savedArguments(f,e.args),b.next,dest,ASSIGN,null); b=pc;
                            } else if(f.intrinsic==TASK_MAP) {
                                enterTaskMap(f,e.args,null,b.next,dest,ASSIGN,null); b=pc;
                            } else if(f.intrinsic!=0) {
                                if(f.intrinsic==POINTER_IDENTITY) pointerIdentity(f,e.args,activePrepared,e);
                                else intrinsicSlots(f,e.args);
                                if(b.type==OBJ) objects[dest]=result; else numbers[dest]=scalarResult;
                                b=b.next;
                            } else { enterExplicit(f,e.args,null,b.next,dest,e.args.length==0?CACHE:ASSIGN,null); b=pc; }
                        } else if(e.op==AP) {
                            Object value=obj(e.a); Object[] args=new Object[e.args.length];
                            for(int i=0;i<args.length;i++) args[i]=obj(e.args[i]);
                            applyExplicit(value,args,b.next,dest);
                            b=pc;
                        } else { expression(e,b.type,dest,activePrepared); b=b.next; }
                        break;
                    }
                    case JDECL: joins[jbp+b.a]=b; b=b.next; break;
                    case JMP: {
                        Body join=joins[jbp+b.a]; if(join==null||join.args.length!=b.args.length) throw error("Invalid join");
                        for(int i=0;i<b.args.length;i++) { int dest=bp+join.args[i],source=bp+b.args[i]; objects[dest]=obj(b.args[i]); numbers[dest]=numbers[source]; }
                        b=join.body; break;
                    }
                    case SET: { Node n=node(obj(b.a)); unique(n); n.fields[b.b]=obj(b.args[0]); stores++; b=b.next; break; }
                    case SSET: { Node n=node(obj(b.a)); unique(n); writeScalar(n,rawOffset(n,b.tags[0],b.b),b.type,numbers[bp+b.args[0]]); stores++; b=b.next; break; }
                    case USET: { Node n=node(obj(b.a)); unique(n); writeScalar(n,rawOffset(n,b.b,0),USIZE,numbers[bp+b.args[0]]); stores++; b=b.next; break; }
                    case SETTAG: { Node n=node(obj(b.a)); unique(n); n.tag=b.b; b=b.next; break; }
                    case INC: inc(obj(b.a),b.b); b=b.next; break;
                    case DEC:
                        if(taskRuntime!=null) { if(beginRelease(obj(b.a),b.b,b.next)) b=pc; else b=b.next; }
                        else { releaseQuiet(obj(b.a),b.b); b=b.next; }
                        break;
                    case DEL: deleteShell(obj(b.a)); b=b.next; break;
                    case CASE: {
                        long tag=caseTag(b);
                        Body selected=null;
                        for(int i=0;i<b.tags.length;i++) if(b.tags[i]==tag||b.tags[i]==-1) { selected=b.alternatives[i]; break; }
                        if(selected==null) throw error("Incomplete case"); b=selected; break;
                    }
                    case RET: if(active.resultType==OBJ) result=obj(b.a); else scalarResult=numbers[bp+b.a]; returnExplicit(); b=pc; break;
                    case UNREACHABLE: throw error("Unreachable");
                    default: throw error("Invalid body opcode");
                }
            }
            pc=b;
    }
    /** Transfer the completed external result exactly once. */
    public Object takeResult() {
        explicitOnly();
        if(phase!=COMPLETE||!pendingOwnedResult) throw new IllegalStateException("No owned result available");
        Object value=releaseRoot?ERASED:entry.resultType==OBJ?result:externalScalar(scalarResult,entry.resultType);
        pendingOwnedResult=false; result=null; entry=null; releaseRoot=false; phase=IDLE;
        return value;
    }
    /** Internal borrowed array primitives need an owning wrapper at host entry. */
    private static boolean borrowedTaskPrimitive(int op) {
        return op==PROMISE_RESOLVE||op==PROMISE_RESULT||op==TASK_STATE||op==TASK_CANCEL;
    }
    private static void rootEntry(Function f) {
        require(f.intrinsic!=PROFILE_IT,"Borrowed profiling primitive requires an owned guest wrapper");
        require(!borrowedTaskPrimitive(f.intrinsic),"Borrowed task primitive requires owned guest wrapper");
        if(borrowedStringPositionPrimitive(f.intrinsic))
            throw new UnsupportedOperationException("Borrowed String position primitive requires owned guest wrapper at external entry");
        if(borrowedStringCompletionPrimitive(f.intrinsic))
            throw new UnsupportedOperationException("Borrowed String range primitive requires owned guest wrapper at external entry");
        if(borrowedIntPrimitive(f.intrinsic))
            throw new UnsupportedOperationException("Borrowed Int primitive requires owned guest wrapper at external entry");
        require(f.intrinsic!=NAME_EQ,"Borrowed Name equality requires an owned guest wrapper");
        require(f.intrinsic!=EXPR_CACHE,"Borrowed Expr data requires an owned guest wrapper");
        if(borrowedBytePrimitive(f.intrinsic))
            throw new UnsupportedOperationException("Borrowed ByteArray primitive requires owned guest wrapper at external entry");
        require(f.intrinsic!=POINTER_IDENTITY,"Pointer identity requires a certified direct FAP site");
        if(borrowedArrayPrimitive(f.intrinsic))
            throw new UnsupportedOperationException("Borrowed array primitive requires owned guest wrapper at external entry");
        if(borrowedRefPrimitive(f.intrinsic))
            throw new UnsupportedOperationException("Borrowed ref primitive requires owned guest wrapper at external entry");
    }
    /** Internal owned-argument typed entry, not Lean's generic call_boxed ABI. */
    public Object invoke(int function,Object[] args) {
        if(closed) throw error("Interpreter closed");
        if(explicit) {
            start(function,args); advance(Long.MAX_VALUE);
            if(phase==HOST_CALL) throw new IllegalStateException("Invocation suspended for host extern: "+hostRequest.symbol());
            if(phase==CODE_CALL) throw new IllegalStateException("Invocation suspended for code: "+codeRequest.header().name());
            return takeResult();
        }
        if(sp!=0) throw error("Reentrant external invocation unsupported");
        Function f=program.functions[function];
        rootEntry(f);
        if(f.hostExtern!=null) throw new UnsupportedOperationException("Host extern requires explicit driver: "+f.hostExtern.symbol);
        f=preflightCallable(f);
        validateEntryArguments(f,args);
        callsLeft=10_000_000;
        try {
            if(f.params.length==0) { load(f); if(f.resultType==OBJ) inc(result,1); }
            else enter(f,args);
            return f.resultType==OBJ?result:externalScalar(scalarResult,f.resultType);
        } catch(Throwable failure) { untrackedFailure=true; throw failure; }
    }
    public long rbmap(int make,int fold,int callback,int n) {
        Object cb=invoke(callback,new Object[0]);
        Object tree=invoke(make,new Object[]{Long.valueOf(n)});
        Object answer=invoke(fold,new Object[]{cb,tree,Long.valueOf(0)});
        return ((Number)answer).longValue();
    }
    /** Benchmark harness only; same adjacent-input batching as native Lean. */
    public long rbmapBatch(int make,int fold,int callback,int n,int repetitions) {
        if(n<0||repetitions<0) throw error("Invalid batch");
        long checksum=0;
        for(int i=0;i<repetitions;i++) checksum+=rbmap(make,fold,callback,n+i%2);
        return checksum;
    }
    @Override public void close() {
        if(closed) return;
        if(hostGuestRecord!=null) throw new IllegalStateException("Host guest operation requires explicit completion before close");
        if(taskRuntime!=null) {
            if(!disposed||stdoutRoot!=null||runtimeAction!=null||hostCompletion!=null||quietCurrent!=null||releasePending!=0)
                throw new IllegalStateException("Active runtime requires completed explicit disposal before close");
            for(boolean ready:constantReady) if(ready)
                throw new IllegalStateException("Explicit disposal left an initialized cache owner");
        }
        closed=true;
        if(explicit&&(phase==RUNNING||phase==FAILED||phase==HOST_CALL||phase==CODE_CALL||phase==WAITING)) {
            closed=false;
            throw new IllegalStateException("Active or failed explicit execution requires ownership cleanup before close");
        }
        boolean sourceOwnedResult=pendingOwnedResult&&!releaseRoot&&entry.resultType==OBJ;
        releaseRoot=false;
        if(sourceOwnedResult) releaseQuiet(result,1);
        pendingOwnedResult=false;
        if(stdoutRoot!=null) { releaseQuiet(stdoutRoot,1); stdoutRoot=null; }
        utf8Key=null; utf8Bytes=null;
        for(int i=0;i<constants.length;i++) if(constantReady[i]&&program.functions[i].resultType==OBJ) releaseQuiet(constants[i],1);
        Arrays.fill(constants,null); Arrays.fill(objects,null); result=null; taskRecords.clear();
    }
}
