/*
 * Experimental JVM port of Lean's lambda-RC interpreter, pinned to
 * 819816b2e0a3bf405af45ae5c7af2491d8f5bee6:src/library/ir_interpreter.cpp.
 * Upstream: Copyright (c) 2019 Microsoft Corporation. Apache-2.0.
 * Author of upstream interpreter: Sebastian Ullrich.
 *
 * Bounded object/uint8/uint16/uint32/usize/uint64/float profile (64-bit little-endian), not a public API.
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
    private static final int OBJ=0, U8=1, U32=2, USIZE=3, U64=4, F64=5, U16=6, F32=7;
    private static final int VDECL=0,JDECL=1,SET=2,SSET=3,INC=4,DEC=5,DEL=6,CASE=7,RET=8,JMP=9,UNREACHABLE=10,SETTAG=11,USET=12;
    private static final int MAP_APPLY=13,MAP_WRAP=14;
    private static final int CTOR=0,PROJ=1,SPROJ=2,FAP=3,PAP=4,AP=5,BOX=6,UNBOX=7,LIT=8,SHARED=9,UPROJ=10;
    private static final int ADD=1,SUB=2,MOD=3,EQ=4,LT=5,MUL=6,DIV=7,POW=8;
    private static final int U16_EQ=540,U16_NAT=541,MARK_PERSISTENT=542;
    private static final int MAX_PERSISTENT_NODES=300_000,MAX_PERSISTENT_EDGES=1_000_000;
    private static final int LAYOUT_FIELDS=531,LAYOUT_SCALARS=532,LAYOUT_TAG=533,LAYOUT_USIZE=534,U32_LT=535,U64_TO_NAT=536;
    private static final int USIZE_NAT=9,USIZE_REPR=10,U32_NAT=11,U32_EQ=12,U32_LE=13,PLATFORM_BITS=14;
    private static final int FLOAT_LE=543,BYTE_EMPTY=544;
    private static final int GET_STDIN=545,GET_STDERR=546,SET_STDIN=547,SET_STDOUT=548,SET_STDERR=549,STDERR_PUT=550;
    private static final int STR_TO_UTF8=553,STR_FROM_UTF8=554,STR_VALIDATE_UTF8=555,BYTE_COPY_SLICE=556;
    private static final int STR_POS_SET=260;
    private static final int VOID_MK=516,LEVEL_INSTANTIATE=517,EXPR_FIND_EXT=519;
    private static final int ARRAY_CHECKED_SET=518,SHARECOMMON_QUICK=520,EXPR_REPLACE=521,EXPR_ABSTRACT_RANGE=522,EXPR_ABSTRACT=523;
    private static final int EXPR_INSTANTIATE=524,EXPR_INSTANTIATE1=525,EXPR_INSTANTIATE_RANGE=526,EXPR_INSTANTIATE_REV=527,EXPR_INSTANTIATE_REV_RANGE=528,EXPR_LIFT=529,EXPR_INSTANTIATE_MVARS=530;
    private static final int EXPR_HAS_LOOSE=537,EXPR_LOWER=538,EXPR_QUICK_LT=539;
    private static final int EXPR_DATA=400,EXPR_APP_DATA=401,LEVEL_DATA=402,EXPR_CACHE=403,EXPR_EQV=404,EXPR_EQUAL=405,U8_TO_U32=406,U64_TO_U8=407,EXPR_FIND=408,LEVEL_EQUAL=409;
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
        register(registry,new ExternSpec("lean_get_max_ctor_fields",LAYOUT_FIELDS,"tobject",new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_get_max_ctor_scalars_size",LAYOUT_SCALARS,"tobject",new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_get_max_ctor_tag",LAYOUT_TAG,"tobject",new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_get_usize_size",LAYOUT_USIZE,"tobject",new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint32_dec_lt",U32_LT,"uint8",new String[]{"uint32","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_to_nat",U64_TO_NAT,"tobject",new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint16_dec_eq",U16_EQ,"uint8",new String[]{"uint16","uint16"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint16_to_nat",U16_NAT,"tagged",new String[]{"uint16"},new boolean[]{false}));
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
        register(registry,new ExternSpec("lean_get_stdin",GET_STDIN,"object",new String[]{"void"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_get_stderr",GET_STDERR,"object",new String[]{"void"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_get_set_stdin",SET_STDIN,"object",new String[]{"object","void"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_get_set_stdout",SET_STDOUT,"object",new String[]{"object","void"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_get_set_stderr",SET_STDERR,"object",new String[]{"object","void"},new boolean[]{false,false}));
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
        register(registry,new ExternSpec("lean_array_set",ARRAY_CHECKED_SET,"object",
                new String[]{"erased","object","tobject","tobject"},new boolean[]{false,false,true,false}));
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
        register(registry,new ExternSpec("lean_runtime_mark_persistent",MARK_PERSISTENT,"tobject",
                new String[]{"erased","tobject","void"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_profileit",PROFILE_IT,"tobject",
                new String[]{"erased","object","object","tobject","tobject"},new boolean[]{false,true,true,false,false}));
        register(registry,new ExternSpec("lean_instantiate_level_mvars",LEVEL_INSTANTIATE,"object",
                new String[]{"object","tobject"},new boolean[]{false,false}));
        if(EXPR_INSTANTIATION_NATIVE_READY) register(registry,new ExternSpec("lean_instantiate_expr_mvars",EXPR_INSTANTIATE_MVARS,"object",
                new String[]{"object","object"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_void_mk",VOID_MK,"void",
                new String[]{"erased","tobject"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_find_ext_expr",EXPR_FIND_EXT,"tobject",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_sharecommon_quick",SHARECOMMON_QUICK,"tobject",
                new String[]{"erased","tobject"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_expr_instantiate",EXPR_INSTANTIATE,"object",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_instantiate1",EXPR_INSTANTIATE1,"object",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_instantiate_range",EXPR_INSTANTIATE_RANGE,"object",
                new String[]{"object","tobject","tobject","object"},new boolean[]{true,true,true,true}));
        register(registry,new ExternSpec("lean_expr_instantiate_rev",EXPR_INSTANTIATE_REV,"object",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_instantiate_rev_range",EXPR_INSTANTIATE_REV_RANGE,"object",
                new String[]{"object","tobject","tobject","object"},new boolean[]{true,true,true,true}));
        register(registry,new ExternSpec("lean_expr_lift_loose_bvars",EXPR_LIFT,"object",
                new String[]{"object","tobject","tobject"},new boolean[]{true,true,true}));
        register(registry,new ExternSpec("lean_replace_expr",EXPR_REPLACE,"object",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_abstract_range",EXPR_ABSTRACT_RANGE,"object",
                new String[]{"object","tobject","object"},new boolean[]{true,true,true}));
        register(registry,new ExternSpec("lean_expr_abstract",EXPR_ABSTRACT,"object",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_find_expr",EXPR_FIND,"tobject",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_eqv",EXPR_EQV,"uint8",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_level_eq",LEVEL_EQUAL,"uint8",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_equal",EXPR_EQUAL,"uint8",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_quick_lt",EXPR_QUICK_LT,"uint8",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_has_loose_bvar",EXPR_HAS_LOOSE,"uint8",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_lower_loose_bvars",EXPR_LOWER,"object",
                new String[]{"object","tobject","tobject"},new boolean[]{true,true,true}));
        register(registry,new ExternSpec("lean_expr_data",EXPR_CACHE,"uint64",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_expr_mk_data",EXPR_DATA,"uint64",
                new String[]{"uint64","tobject","uint32","uint8","uint8","uint8","uint8"},
                new boolean[]{false,false,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_expr_mk_app_data",EXPR_APP_DATA,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_level_mk_data",LEVEL_DATA,"uint64",
                new String[]{"uint64","tobject","uint8","uint8"},new boolean[]{false,false,false,false}));
        register(registry,new ExternSpec("lean_uint8_to_uint32",U8_TO_U32,"uint32",
                new String[]{"uint8"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_to_uint8",U64_TO_U8,"uint8",
                new String[]{"uint64"},new boolean[]{false}));
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
        register(registry,new ExternSpec("lean_string_to_utf8",STR_TO_UTF8,"object",
                new String[]{"object"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_string_to_utf8",STR_TO_UTF8,"object",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_string_from_utf8_unchecked",STR_FROM_UTF8,"object",
                new String[]{"object","erased"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_validate_utf8",STR_VALIDATE_UTF8,"uint8",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_byte_array_copy_slice",BYTE_COPY_SLICE,"object",
                new String[]{"object","tobject","object","tobject","tobject","uint8"},
                new boolean[]{true,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_mk_empty_byte_array",BYTE_EMPTY,"object",
                new String[]{"tobject"},new boolean[]{true}));
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
        register(registry,new ExternSpec("lean_float_decLe",FLOAT_LE,"uint8",new String[]{"float","float"},new boolean[]{false,false}));
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
    /** Pinned object.cpp lean_mark_persistent / io.cpp wrapper. Native RC zero
     * is a traversal stop, not an inferred transitive property of Ref contents.
     * Read-only bounded preflight precedes a nonthrowing rc-only commit so an
     * unsupported object, stale source closure, interrupt or bound cannot leave
     * a partially persistent graph. Runtime Task/Promise lifetime remains the
     * existing positive-RC policy; no waiting, callback or task execution occurs.
     */
    private ArrayList<Node> persistentPreflight(Object value) {
        validateHostObject(value);
        ArrayList<Node> commit=new ArrayList<>();
        if(!(value instanceof Node)) return commit;
        IdentityHashMap<Node,Boolean> seen=new IdentityHashMap<>();
        ArrayDeque<Node> todo=new ArrayDeque<>(); todo.push((Node)value);
        int edges=0;
        while(!todo.isEmpty()) {
            Node current=todo.pop(); validateHostObject(current);
            if(current.rc==0||seen.containsKey(current)) continue;
            require(seen.size()<MAX_PERSISTENT_NODES,"markPersistent node bound exceeded");
            seen.put(current,Boolean.TRUE);
            NodeMetadata kind=kindMetadata(current);
            require(!(kind instanceof TaskMetadata),"markPersistent rejects runtime-created Task/Promise lifecycle");
            if(current.array) {
                require(kind instanceof ArrayState&&!current.ref&&!current.readyTask&&current.closure==null,
                        "markPersistent unknown Array kind");
                array(current);
            } else if(isByteArray(current)) byteArray(current);
            else if(current.ref) reference(current);
            else if(current.readyTask) readyTaskNode(current);
            else if(current.closure!=null) {
                require(current.tag==245&&current.scalars.length==0,"markPersistent unknown closure kind");
                acceptsClosure(current);
            } else require(kind==null&&current.tag>=0&&current.tag<=243,
                           "markPersistent unsupported external/thunk/object kind");
            int live=owningFieldCount(current);
            require(live>=0&&live<=current.fields.length,"markPersistent invalid owning extent");
            require(edges<=MAX_PERSISTENT_EDGES-live,"markPersistent edge bound exceeded"); edges+=live;
            if(Thread.currentThread().isInterrupted()) throw error("markPersistent preflight interrupted");
            commit.add(current);
            for(int i=0;i<live;i++) {
                Object child=current.fields[i];
                if(child==null) { require(current.ref,"markPersistent absent owning field"); continue; }
                if(child instanceof Node) todo.push((Node)child); else validateHostObject(child);
            }
        }
        return commit;
    }
    private ArrayList<Node> validatePersistentArguments(Object erased,Object value,Object world) {
        require(ERASED.equals(erased)&&ERASED.equals(world),"markPersistent erased/world placeholders required");
        return persistentPreflight(value);
    }
    private void persistentIntrinsic(Object erased,Object value,Object world) {
        ArrayList<Node> commit=validatePersistentArguments(erased,value,world);
        // All allocation, source/shape validation and cancellation checks are
        // complete. Thread confinement forbids observation inside this commit.
        for(int i=0;i<commit.size();i++) commit.get(i).rc=0;
        result=value; // owned input is returned unchanged; no INC, DEC or MT mark
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
                &&(prepared.pointerHashSites==null||!prepared.pointerHashSites.contains(site)),
                "Pointer identity requires the exact certified FAP site");
        pointerIdentity(function,slots,prepared,site,null);
    }
    private void pointerIdentity(Function function,int[] slots,PreparedBody prepared,Expr site,Function caller) {
        boolean hash=prepared!=null&&prepared.pointerHashSites!=null&&prepared.pointerHashSites.contains(site);
        boolean equality=prepared!=null&&prepared.pointerSites!=null&&prepared.pointerSites.contains(site);
        require((hash||equality)&&site.op==FAP&&site.target==function&&site.args==slots&&function.intrinsic==POINTER_IDENTITY,
                "Pointer identity requires the exact certified FAP site");
        require(ERASED.equals(obj(slots[0])),"Pointer identity erased parameter requires erased placeholder");
        if(hash) {
            pointerHashEntry(caller,prepared,program);
            exprNode(obj(slots[1])); // live Expr-shaped roots only, before stamping
        }
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
    /* A typed Name remains a java.util.List key. These nodes have no source,
     * Program or guest ownership back-reference. Cache the Java List hash (not
     * Clojure hasheq); mixed old/new keys must work in either lookup direction. */
    private static final class CompactName extends AbstractList<Object> implements RandomAccess {
        private final int tag; // anonymous=0, str=1, num=2
        private final CompactName prefix;
        private final Object leaf;
        private final int listHash;
        private CompactName(int tag,CompactName prefix,Object leaf) {
            this.tag=tag; this.prefix=prefix; this.leaf=leaf;
            int hash=31+tagString().hashCode();
            if(tag!=0) { hash=31*hash+prefix.hashCode(); hash=31*hash+leaf.hashCode(); }
            listHash=hash;
        }
        private String tagString() { return tag==0?"anonymous":tag==1?"str":"num"; }
        @Override public int size() { return tag==0?1:3; }
        @Override public Object get(int index) {
            if(index==0) return tagString();
            if(tag!=0&&index==1) return prefix;
            if(tag!=0&&index==2) return leaf;
            throw new IndexOutOfBoundsException("Name index: "+index);
        }
        @Override public Object set(int index,Object value) { throw new UnsupportedOperationException(); }
        @Override public void add(int index,Object value) { throw new UnsupportedOperationException(); }
        @Override public Object remove(int index) { throw new UnsupportedOperationException(); }
        @Override public boolean remove(Object value) { throw new UnsupportedOperationException(); }
        @Override public boolean addAll(Collection<?> values) { throw new UnsupportedOperationException(); }
        @Override public boolean addAll(int index,Collection<?> values) { throw new UnsupportedOperationException(); }
        @Override public boolean removeAll(Collection<?> values) { throw new UnsupportedOperationException(); }
        @Override public boolean retainAll(Collection<?> values) { throw new UnsupportedOperationException(); }
        @Override public boolean removeIf(java.util.function.Predicate<? super Object> filter) { throw new UnsupportedOperationException(); }
        @Override public void replaceAll(java.util.function.UnaryOperator<Object> operator) { throw new UnsupportedOperationException(); }
        @Override public void sort(Comparator<? super Object> comparator) { throw new UnsupportedOperationException(); }
        @Override public void clear() { throw new UnsupportedOperationException(); }
        @Override public List<Object> subList(int from,int to) { return Collections.unmodifiableList(super.subList(from,to)); }
        @Override public int hashCode() { return listHash; }
        @Override public boolean equals(Object other) {
            if(other==this) return true;
            if(other instanceof CompactName) {
                CompactName name=(CompactName)other;
                return tag==name.tag&&listHash==name.listHash
                        &&(tag==0||(prefix.equals(name.prefix)&&leaf.equals(name.leaf)));
            }
            return super.equals(other);
        }
    }
    /* Strong interning lasts exactly as long as this source boundary. Neither
     * canonical node nor leaf retains the pool. Synchronize the entire traversal
     * so concurrent Header issuance shares prefix/leaf/node identity safely. */
    private static final class NamePool {
        private final Map<CompactName,CompactName> nodes=new HashMap<>();
        private final Map<String,String> strings=new HashMap<>();
        private String string(String value) {
            String old=strings.putIfAbsent(value,value); return old==null?value:old;
        }
        private CompactName intern(int tag,CompactName prefix,Object leaf) {
            CompactName candidate=new CompactName(tag,prefix,leaf);
            CompactName old=nodes.putIfAbsent(candidate,candidate); return old==null?candidate:old;
        }
        private CompactName compact(Object value) {
            if(!(value instanceof List)) return null;
            List<?> name=(List<?>)value;
            if(name.size()==1&&"anonymous".equals(name.get(0))) return intern(0,null,null);
            if(name.size()!=3) return null;
            Object tag=name.get(0),leaf=name.get(2);
            boolean str="str".equals(tag),num="num".equals(tag);
            // BigInteger is extensible: a subclass can override hash/equals or
            // retain arbitrary owners. Preserve its legacy freezer path instead
            // of caching its hash or retaining it in the source interner.
            Class<?> leafClass=leaf==null?null:leaf.getClass();
            boolean immutableNumber=leafClass==Long.class||leafClass==Integer.class||leafClass==Short.class
                    ||leafClass==Byte.class||leafClass==BigInteger.class;
            if(!(str||num)||!(leaf instanceof String||(num&&immutableNumber))) return null;
            CompactName prefix=compact(name.get(1));
            if(prefix==null) return null;
            return intern(str?1:2,prefix,leaf instanceof String?string((String)leaf):leaf);
        }
        private synchronized Object freeze(Object value) {
            CompactName compact=compact(value); return compact==null?frozenName(value):compact;
        }
        private synchronized Object metadata(Object value) {
            CompactName compact=compact(value);
            return compact==null?frozenMetadata(value,this):compact;
        }
    }
    /** Trusted-host source boundary, not a digest verifier. The adapter supplies
     * a lightweight immutable accepted catalogue/lease identity, verifies raw
     * bytes and extraction against it, then issues headers and supplies rows.
     * Do not pass a full parsed catalogue here or infer authority from a hash. */
    public static final class SourceBinding {
        private final NamePool names=new NamePool();
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
            exactName=source.names.freeze(row.get("name")); Interpreter.name(exactName);
            Map<String,Object> ir=map(row.get("ir"));
            require(ir.size()==1&&(ir.containsKey("fdecl")||ir.containsKey("extern")),"Invalid declaration header kind");
            kind=ir.containsKey("extern")?"extern":"fdecl";
            Map<String,Object> raw=map(ir.get(kind)),metadata=new LinkedHashMap<>(raw);
            require(exactName.equals(source.names.freeze(raw.get("f"))),"Declaration Name differs from exported row Name");
            metadata.remove("body");
            declaration=map(source.names.metadata(metadata));
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
            evidence=map(source.names.metadata(selected));
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
    private static Object frozenMetadata(Object value,NamePool names) {
        if(value==null||value instanceof String||value instanceof Boolean||value instanceof Long
                ||value instanceof Integer||value instanceof Short||value instanceof Byte||value instanceof BigInteger) return value;
        if(value instanceof List) {
            List<Object> out=new ArrayList<>();
            for(Object item:(List<?>)value) out.add(names.metadata(item));
            return Collections.unmodifiableList(out);
        }
        if(value instanceof Map) {
            Map<String,Object> out=new LinkedHashMap<>();
            for(Map.Entry<?,?> entry:((Map<?,?>)value).entrySet()) {
                require(entry.getKey() instanceof String,"Invalid metadata key");
                out.put((String)entry.getKey(),names.metadata(entry.getValue()));
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
    private enum GraphImportProfile { DEFAULT_RC0, SELECTED_OWNERS, PERSISTENT_REF_PAYLOAD_MT, MODULE_DATA_RC0 }
    /** Trusted adapter's accepted state recipe, not cryptographic admission.
     * Source/state tokens must be lightweight immutable authority/lease tokens.
     * Arrays and byte payloads are copied; no existing runtime Nodes are input.
     * The default constructor accepts only source RC0 and nonnegative carriers.
     * selectedOwners explicitly recomputes positive counts and permits GraphInt.
     * selectedOwnersWithPersistentRefPayloadSharing additionally derives logical
     * MT for the closed positive payload region of persistent Refs.
     * Persistence comes from trusted source metadata; it does not make refs
     * immutable, and no profile authenticates caller-supplied state facts. */
    public static final class PreparedGraph {
        private final SourceBinding binding;
        private final Object acceptedStateToken;
        private final ImportNode[] nodes;
        private final Header[] globals;
        private final Object[] globalValues,ownedRoots;
        private final GraphImportProfile profile;
        public PreparedGraph(SourceBinding binding,Object acceptedStateToken,ImportNode[] nodes,
                             Header[] globals,Object[] globalValues,Object[] ownedRoots) {
            this(binding,acceptedStateToken,nodes,globals,globalValues,ownedRoots,GraphImportProfile.DEFAULT_RC0);
        }
        public static PreparedGraph selectedOwners(SourceBinding binding,Object acceptedStateToken,ImportNode[] nodes,
                                                    Header[] globals,Object[] globalValues,Object[] ownedRoots) {
            return new PreparedGraph(binding,acceptedStateToken,nodes,globals,globalValues,ownedRoots,GraphImportProfile.SELECTED_OWNERS);
        }
        /** Explicit target sharing reconstruction, not evidence of historical native MT state.
         * Only persistent Ref slots may enter the positive graph; every positive
         * object must be in their transitive positive owning-field closure. */
        public static PreparedGraph selectedOwnersWithPersistentRefPayloadSharing(SourceBinding binding,Object acceptedStateToken,
                              ImportNode[] nodes,Header[] globals,Object[] globalValues,Object[] ownedRoots) {
            return new PreparedGraph(binding,acceptedStateToken,nodes,globals,globalValues,ownedRoots,GraphImportProfile.PERSISTENT_REF_PAYLOAD_MT);
        }
        /** Separate bounded source-data envelope for one complete ModuleData DAG.
         * No globals, closures, Refs, signed carriers or positive source RC.
         * Authentication and scalar-domain evidence belong to the trusted adapter.
         * This is not an increase to the ordinary runtime-companion import cap. */
        public static PreparedGraph moduleData(SourceBinding binding,Object acceptedStateToken,
                                               ImportNode[] nodes,Object[] ownedRoots) {
            require(nodes!=null&&ownedRoots!=null,"Explicit ModuleData nodes/roots required");
            require(ownedRoots.length==1,"ModuleData requires its authentic aggregate root");
            for(ImportNode node:nodes) {
                require(node!=null&&(node.kind==ImportNode.CONSTRUCTOR||node.kind==ImportNode.ARRAY),
                        "ModuleData only supports constructor/Array recipes");
                require(node.sourceRC==0,"ModuleData requires persistent source RC zero");
                requireDefaultGraphValues(node.fields);
            }
            requireDefaultGraphValues(ownedRoots);
            return new PreparedGraph(binding,acceptedStateToken,nodes,new Header[0],new Object[0],
                                     ownedRoots,GraphImportProfile.MODULE_DATA_RC0);
        }
        private PreparedGraph(SourceBinding binding,Object acceptedStateToken,ImportNode[] nodes,
                              Header[] globals,Object[] globalValues,Object[] ownedRoots,GraphImportProfile profile) {
            require(binding!=null&&acceptedStateToken!=null,"Actual accepted source/state tokens required");
            require(nodes!=null&&globals!=null&&globalValues!=null&&ownedRoots!=null,
                    "Explicit prepared graph tables and roots required");
            require(nodes.length<=(profile==GraphImportProfile.MODULE_DATA_RC0?150_000:MAX_IMPORT_NODES),"Prepared graph exceeds selected profile node limit");
            require(globals.length<=MAX_IMPORT_ROOTS&&ownedRoots.length<=MAX_IMPORT_ROOTS,"Prepared graph exceeds root/global limit");
            require(globals.length==globalValues.length,"Prepared global table length mismatch");
            checkGraphProfile(nodes,globalValues,ownedRoots,profile!=GraphImportProfile.DEFAULT_RC0&&profile!=GraphImportProfile.MODULE_DATA_RC0);
            checkGraphBudget(nodes,globalValues,ownedRoots);
            this.profile=profile;
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
        final boolean borrowedUtf8;
        final HostExtern hostExtern;
        final Header header;
        Function(String label,int id,int[] params,int[] paramTypes,int resultType,
                 int intrinsic,HostExtern hostExtern,Object privateOwner) {
            this(label,id,params,paramTypes,resultType,intrinsic,hostExtern,privateOwner,null);
        }
        Function(String label,int id,int[] params,int[] paramTypes,int resultType,
                 int intrinsic,HostExtern hostExtern,Object privateOwner,Header header) {
            this(label,id,params,paramTypes,resultType,intrinsic,hostExtern,privateOwner,header,
                    intrinsic==STR_TO_UTF8&&header!=null&&header.borrowed[0]);
        }
        Function(String label,int id,int[] params,int[] paramTypes,int resultType,
                 int intrinsic,HostExtern hostExtern,Object privateOwner,Header header,boolean borrowedUtf8) {
            this.borrowedUtf8=borrowedUtf8;
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
        final Set<Expr> pointerSites,pointerHashSites;
        final Function caller;
        private PreparedBody(Body runtimeMapBody) {
            body=runtimeMapBody; width=8; joinWidth=0; pointerSites=null; pointerHashSites=null; caller=null;
        }
        PreparedBody(Function caller,Body body,int width,int joinWidth) {
            this.body=body; this.width=width; this.joinWidth=joinWidth; this.caller=caller;
            PointerCertificates certificates=certifyPointerObservations(body); this.pointerSites=certificates.equality; this.pointerHashSites=certificates.hash;
        }
    }
    /** Local preparation state, never retained by a published Function or Program. */
    private static final class BodyBuilder {
        int width=1, joinWidth=1;
        final Function caller; Body body;
        BodyBuilder(Function function) {
            caller=function;
            for(int param:function.params) width=Math.max(width,param+1);
        }
        PreparedBody finish() { return new PreparedBody(caller,body,width,joinWidth); }
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

    /** Exact ordinary FoldConsts cohort. Headers and source tokens are immutable;
     * raw SHA labels are descriptive until the trusted loader verifies bytes and
     * the high-level empty-seed/input contract. Contains no guest/cache/resource. */
    public static final class PointerHashPolicy {
        private final Header[] roles;
        private PointerHashPolicy(Header[] roles) { this.roles=roles.clone(); }
        public static PointerHashPolicy originalFoldConsts(Header contains,Header insert,Header rehash) {
            Header[] roles={contains,insert,rehash};
            String[] hashes={"6b9720aa488a57b0a3698e5bde20ce1d17e178d928c9889eb1dbe9bec7784665","0f6b605d51998d2e76c3dc0c14b286767f37ab8647e58005e71be810b1f5ec9a","134fa49c228c361525b1760d52157bcdf494f8d7144106799145ab5a34ccc12c"};
            String[] names={"Std.DHashMap.Internal.Raw₀.contains._at_._private.Lean.Util.FoldConsts.0.Lean.Expr.FoldConstsImpl.fold.visit.spec_0._redArg","Std.DHashMap.Internal.Raw₀.insertIfNew._at_._private.Lean.Util.FoldConsts.0.Lean.Expr.FoldConstsImpl.fold.visit.spec_1._redArg","Std.DHashMap.Internal.AssocList.foldlM._at_._private.Std.Data.DHashMap.Internal.Defs.0.Std.DHashMap.Internal.Raw₀.expand.go._at_.Std.DHashMap.Internal.Raw₀.expand._at_.Std.DHashMap.Internal.Raw₀.insertIfNew._at_._private.Lean.Util.FoldConsts.0.Lean.Expr.FoldConstsImpl.fold.visit.spec_1.spec_2.spec_3.spec_4._redArg"};
            String[][] parameters={new String[]{"object","object"},new String[]{"object","object","tobject"},new String[]{"object","tobject"}};
            boolean[][] borrowed={new boolean[]{true,true},new boolean[]{false,false,false},new boolean[]{false,false}};
            String[] results={"uint8","object","object"};
            for(int role=0;role<roles.length;role++) {
                Header h=roles[role];
                require(h!=null&&h.kind.equals("fdecl")&&h.originalSha256.equals(hashes[role]),"Pointer hash role/source hash differs");
                require(h.source==contains.source,"Pointer hash roles have different source bindings");
                Object name=Arrays.asList("anonymous");
                // The exact three exported Names have numeric private-scope 0
                // components; every other printed segment is a string component.
                for(String segment:names[role].split("\\.")) name=Arrays.asList(segment.equals("0")?"num":"str",name,segment);
                require(h.exactName.equals(frozenName(name)),"Pointer hash typed role Name differs");
                Map<String,Object> d=h.declaration;
                require(d.keySet().equals(new HashSet<>(Arrays.asList("f","info","type","xs")))&&map(d.get("info")).isEmpty()
                        &&d.get("f").equals(h.exactName)&&results[role].equals(d.get("type"))&&results[role].equals(h.resultType),
                        "Pointer hash canonical role declaration differs");
                List<Object> xs=list(d.get("xs")); require(xs.size()==parameters[role].length,"Pointer hash raw role arity differs");
                for(int i=0;i<xs.size();i++) {
                    Map<String,Object> x=map(xs.get(i)),v=map(x.get("x"));
                    require(x.keySet().equals(new HashSet<>(Arrays.asList("borrow","ty","x")))&&v.keySet().equals(Collections.singleton("idx"))
                            &&number(v.get("idx"))==i+1&&parameters[role][i].equals(x.get("ty"))&&Boolean.valueOf(borrowed[role][i]).equals(x.get("borrow")),
                            "Pointer hash parameter lane/borrow/ID differs");
                }
                Map<String,Object> runtime=map(h.evidence.get("runtime"));
                require(runtime.keySet().equals(new HashSet<>(Arrays.asList("initializer","role")))&&runtime.get("initializer")==null
                        &&"ordinary".equals(runtime.get("role")),"Pointer hash role is not an ordinary original function");
            }
            return new PointerHashPolicy(roles);
        }
    }
    private PointerHashPolicy pointerHashPolicy;
    private static Function pointerHashRole(Program image,Header header) {
        int id=image.functionId(header); Function function=image.functions[id];
        require(function.header==header&&function.intrinsic==0&&function.hostExtern==null&&image.guestExports[id]==null,
                "Pointer hash role is not the actual ordinary Function");
        requireExecutableAbi(function); return function;
    }
    /** Once-only host admission; caller authenticates the source cohort and
     * target-built empty FoldConsts seed contract separately. Both drivers. */
    public void configurePointerHashes(PointerHashPolicy policy) {
        require(policy!=null,"Missing pointer hash source policy");
        if(closed||disposed||untrackedFailure||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||continuationDepth!=0||jsp!=0
                ||runtimeAction!=null||hostCompletion!=null||hostGuestRecord!=null||quietCurrent!=null||releasePending!=0
                ||releaseTransaction!=null||releaseRoot||pointerHashPolicy!=null)
            throw new IllegalStateException("Pointer hash configuration requires an open idle unconfigured engine");
        for(Header header:policy.roles) pointerHashRole(program,header);
        pointerHashPolicy=policy;
    }
    private void pointerHashEntry(Function caller,PreparedBody prepared,Program image) {
        if(prepared.pointerHashSites==null) return;
        require(pointerHashPolicy!=null,"Pointer hash execution requires the original FoldConsts policy");
        require(caller!=null&&prepared.caller==caller&&caller.header!=null&&caller.id>=0&&caller.id<image.functions.length
                &&image.functions[caller.id]==caller&&image.preparedBodies[caller.id]==prepared,
                "Pointer hash body is not the exact current caller/PreparedBody");
        boolean allowed=false; for(Header header:pointerHashPolicy.roles) if(caller.header==header) { allowed=true; break; }
        require(allowed,"Pointer hash body is outside the configured FoldConsts cohort");
        require(pointerHashRole(image,caller.header)==caller,"Pointer hash caller Function differs");
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
    /** Private stage-one policy. Source authentication is the research loader's
     * obligation; this immutable object only binds exact ordinary constructor roles. */
    private static final class ExprConstructorPolicy {
        final Header[] helpers;
        private ExprConstructorPolicy(Header[] helpers) { this.helpers=helpers.clone(); }
        static ExprConstructorPolicy originalHeaders(Header[] helpers) {
            require(helpers!=null&&helpers.length==9,"Nine original Expr constructor Headers required");
            String[] names={"Lean.Expr.bvar._override","Lean.Expr.sort._override","Lean.Expr.const._override","Lean.Expr.app._override","Lean.Expr.lam._override._boxed","Lean.Expr.forallE._override._boxed","Lean.Expr.letE._override._boxed","Lean.Expr.mdata._override","Lean.Expr.proj._override"};
            String[] hashes={"65c182e597519411555771e582645ee70b608f98413158d2cf3e525eaa689be1","7ef9c9c1c18da89d2811e3c31a516e05106d3ab6e0ac9a972cbe9eb6dde68f6d","729dc14162f591752d010053a082eedfb8d39d3c12db845d49ba2361a6e0bfe3","80d03ae09c95edb7d931e5f36dd67e6d0452a7efb9002b4cff43f5d7cc0d4ef4","6549605db438808e61e47fc97321040ecba177aa36bdf7146656d625f535b40f","93904f8bf3678937186f334bc847b417487ab0132964b32914497b30219bb9ad","3131e7471a4cb37f4cf7b468a3fcc8910ba1026c0f19d9e50b56689765e2dc5e","b0c8524c099135bec06dacbf9abc3eb0ab4b413ffc6004d55ac782290179a7f4","cf155c3f689c3251707318535264965a5482ed40177d2d255d6076331bc668ab"};
            String[][] parameters={new String[]{"tobject"},new String[]{"tobject"},new String[]{"tobject","tobject"},new String[]{"object","object"},new String[]{"tobject","object","object","tagged"},new String[]{"tobject","object","object","tagged"},new String[]{"tobject","object","object","object","tagged"},new String[]{"tobject","object"},new String[]{"tobject","tobject","object"}};
            for(int role=0;role<9;role++) {
                Header h=helpers[role];
                require(h!=null&&h.kind.equals("fdecl")&&h.originalSha256.equals(hashes[role]),"Expr constructor role/source hash differs");
                if(role!=0) require(h.source==helpers[0].source,"Expr constructors have different source bindings");
                Object name=Arrays.asList("anonymous");
                for(String segment:names[role].split("\\.")) name=Arrays.asList("str",name,segment);
                require(h.exactName.equals(frozenName(name)),"Expr constructor typed Name differs");
                Map<String,Object> d=h.declaration;
                require(d.keySet().equals(new HashSet<>(Arrays.asList("f","info","type","xs")))
                        &&map(d.get("info")).isEmpty()&&d.get("f").equals(h.exactName)
                        &&"object".equals(d.get("type")),"Expr constructor declaration differs");
                List<Object> xs=list(d.get("xs"));
                require(xs.size()==parameters[role].length,"Expr constructor raw arity differs");
                for(int i=0;i<xs.size();i++) {
                    Map<String,Object> p=map(xs.get(i)),x=map(p.get("x"));
                    require(p.keySet().equals(new HashSet<>(Arrays.asList("borrow","ty","x")))
                            &&x.keySet().equals(Collections.singleton("idx"))&&number(x.get("idx"))==i+1
                            &&Boolean.FALSE.equals(p.get("borrow"))&&parameters[role][i].equals(p.get("ty")),
                            "Expr constructor raw parameter differs");
                }
                Map<String,Object> runtime=map(h.evidence.get("runtime"));
                require(runtime.keySet().equals(new HashSet<>(Arrays.asList("initializer","role")))
                        &&runtime.get("initializer")==null&&"ordinary".equals(runtime.get("role")),"Expr constructor is not ordinary");
            }
            return new ExprConstructorPolicy(helpers);
        }
    }
    /** Immutable constructor-role binding for native expression transformations.
     * Source bytes remain the trusted loader's obligation, not a caller flag. */
    public static final class ExprTransformPolicy {
        private final ExprConstructorPolicy constructors;
        private ExprTransformPolicy(ExprConstructorPolicy constructors) { this.constructors=constructors; }
        public static ExprTransformPolicy originalHelpers(Header[] helpers) {
            return new ExprTransformPolicy(ExprConstructorPolicy.originalHeaders(helpers));
        }
    }
    private ExprTransformPolicy exprTransformPolicy;
    public void configureExprTransforms(ExprTransformPolicy policy) {
        explicitOnly();
        require(taskRuntime!=null&&policy!=null,"Expr transforms require active runtime and original constructor policy");
        if(closed||disposed||untrackedFailure||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||continuationDepth!=0
                ||runtimeAction!=null||hostCompletion!=null||hostGuestRecord!=null||quietCurrent!=null||releasePending!=0
                ||releaseTransaction!=null||releaseRoot)
            throw new IllegalStateException("Expr transform configuration requires an open idle engine");
        require(exprTransformPolicy==null,"Expr transform policy is already configured");
        for(int i=0;i<9;i++) exprConstructor(policy.constructors,i);
        exprTransformPolicy=policy;
    }
    private ExprConstructorPolicy exprTransformsProfile(Function nativeFunction) {
        require(explicit&&taskRuntime!=null&&exprTransformPolicy!=null,
                "Expr transforms require active explicit runtime and original constructor policy");
        ExprConstructorPolicy policy=exprTransformPolicy.constructors;
        require(nativeFunction!=null&&nativeFunction.header!=null
                &&nativeFunction.header.source==policy.helpers[0].source,"Expr transform native/constructor source differs");
        for(int i=0;i<9;i++) exprConstructor(policy,i);
        return policy;
    }
    private Function exprConstructor(ExprConstructorPolicy policy,int role) {
        Header header=policy.helpers[role]; int id=program.functionId(header); Function f=program.functions[id];
        require(f.header==header&&f.intrinsic==0&&f.hostExtern==null&&program.guestExports[id]==null,
                "Expr constructor is not the current exact ordinary Function");
        requireExecutableAbi(f); require(f.resultType==OBJ,"Expr constructor requires OBJ result");
        for(int lane:f.paramTypes) require(lane==OBJ,"Expr constructor requires OBJ parameters");
        return preflightCallable(f,true);
    }
    private static final int EXPR_LIFT_JOB=0,EXPR_SUBST_JOB=1,EXPR_BETA_JOB=2,EXPR_ABSTRACT_JOB=3,EXPR_CALLBACK_JOB=4,EXPR_LOWER_JOB=5;
    private static final int MAX_EXPR_JOB_FRAMES=100_000,MAX_EXPR_JOB_CACHE=100_000,MAX_EXPR_JOB_OFFSET=1_048_575;
    private static final boolean EXPR_MACHINERY_READY=true;
    private static final class ExprCredit {
        Object value; boolean owned;
        ExprCredit(Object value,boolean owned) { this.value=value; this.owned=owned; }
    }
    private abstract static class ExprJob {
        ExprCredit result,childResult; boolean completed; int cleanup;
    }
    private static final class ReplaceJob extends ExprJob {
        Object input; int mode,cutoff; long amount; Object[] substitutions;
        ExprSubstSlice slice;
        Node abstractArray; int prefixLength;
        final ArrayDeque<ExprReplaceFrame> frames=new ArrayDeque<>();
        final IdentityHashMap<Node,HashMap<Integer,ExprCredit>> cache=new IdentityHashMap<>();
        final IdentityHashMap<Node,ExprCredit> callbackCache=new IdentityHashMap<>();
        final ArrayList<ExprCredit> cacheValues=new ArrayList<>();
        final IdentityHashMap<Node,Boolean> active=new IdentityHashMap<>();
        int stage,reservedCacheEntries;
    }
    private static final class ExprReplaceFrame {
        Node original; int offset,stage,cursor,cleanup,abstractScan; boolean shared,active;
        ExprCredit[] children=new ExprCredit[3]; ExprCredit result;
        ExprReplaceFrame(Node original,int offset) { this.original=original; this.offset=offset; }
    }
    private static final class BetaJob extends ExprJob {
        ExprCredit function,temporary,accumulator,replacement;
        Object[] reverseArgs; int consumed,remaining,stage;
        final ArrayDeque<ExprBetaFrame> frames=new ArrayDeque<>();
    }
    private static final class ExprBetaFrame {
        ExprCredit expression;
        ExprBetaFrame(ExprCredit expression) { this.expression=expression; }
    }
    private static final class ExprPacket {
        Function function; Object[] arguments,expectedFields; boolean[] owned;
        int role,expectedTag,expectedFlag; boolean started,entered;
        ExprReplaceFrame replaceFrame; BetaJob beta; ExprDirectTask directTarget; DelayedTransformTask delayedTarget;
    }
    private static final int MAX_INSTANTIATION_WORK=1_000_000;
    private static final class InstantiationBudget { long work; }
    private static final class MVarContextCell { LevelCredit current; }
    private void instantiationWork(InstantiationBudget budget,long amount,String bound,String interrupted) {
        require(budget!=null,"Missing instantiation budget");
        require(amount>=0&&amount<=MAX_INSTANTIATION_WORK-budget.work,bound);
        long before=budget.work; budget.work+=amount;
        if((before>>>10)!=(budget.work>>>10)&&Thread.currentThread().isInterrupted()) throw error(interrupted);
    }
    private static final class ExprMachineryState {
        ExprConstructorPolicy policy;
        final ArrayDeque<ExprJob> jobs=new ArrayDeque<>();
        ExprCredit input,result,retiring; final ArrayList<ExprCredit> arguments=new ArrayList<>();
        Node borrowedPredicate; ExprCallbackPacket callback;
        ExprPacket call; InstantiationBudget budget; int stage,cleanup,liveFrames,liveCacheEntries;
    }
    /** Deliberately private reflection-only research orchestrator. This is not
     * a Lean native, source capability, generic invoke or public VM entry API. */
    private void startExprMachineryResearch(Header[] headers,int mode,Object input,Object[] reverseArgs,long cutoff,long amount) {
        explicitOnly();
        require(EXPR_MACHINERY_READY,"Private Expr machinery is not yet complete");
        require(taskRuntime!=null,"Private Expr machinery requires active explicit runtime");
        if(closed||disposed||untrackedFailure||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||continuationDepth!=0
                ||runtimeAction!=null||hostCompletion!=null||hostGuestRecord!=null||quietCurrent!=null||releasePending!=0
                ||releaseTransaction!=null||releaseRoot)
            throw new IllegalStateException("Private Expr machinery requires an open idle engine");
        require(mode>=EXPR_LIFT_JOB&&mode<=EXPR_BETA_JOB,"Unknown private Expr job mode");
        require(cutoff>=0&&cutoff<=MAX_EXPR_JOB_OFFSET&&amount>=0&&amount<=MAX_EXPR_JOB_OFFSET,"Private Expr offset/amount outside profile");
        require(reverseArgs!=null&&reverseArgs.length<=MAX_EXPR_JOB_FRAMES,"Private Expr substitution vector outside profile");
        if(mode==EXPR_LIFT_JOB) require(reverseArgs.length==0,"Lift job has no substitution arguments");
        if(mode!=EXPR_LIFT_JOB) require(cutoff==0&&amount==0,"Non-lift job has no cutoff/amount");
        ExprConstructorPolicy policy=ExprConstructorPolicy.originalHeaders(headers);
        for(int i=0;i<9;i++) exprConstructor(policy,i);
        IdentityHashMap<Node,Integer> owners=new IdentityHashMap<>();
        Node root=exprNode(input); owners.put(root,1);
        for(Object value:reverseArgs) owners.merge(exprNode(value),1,Integer::sum);
        for(Map.Entry<Node,Integer> item:owners.entrySet()) require(item.getKey().rc==0||item.getKey().rc>=item.getValue(),"Private Expr input alias credits differ");
        RuntimeAction action=newAction(ACTION_EXPR_MACHINERY,null,null,0,ROOT,null);
        ExprMachineryState state=new ExprMachineryState(); state.policy=policy; state.budget=new InstantiationBudget();
        state.input=new ExprCredit(input,true);
        for(Object value:reverseArgs) state.arguments.add(new ExprCredit(value,true));
        action.exprMachinery=state; publishAction(action); objects[action.slot]=null;
        callsLeft=10_000_000; instructions=0; phase=RUNNING;
        entry=null; result=null; releaseRoot=false;
        if(mode==EXPR_BETA_JOB) {
            BetaJob beta=new BetaJob(); beta.function=state.input; state.input=null;
            beta.reverseArgs=reverseArgs.clone(); state.jobs.addLast(beta);
        } else pushReplaceJob(state,mode,input,(int)cutoff,(int)amount,reverseArgs.clone());
    }
    private void exprJobWork(ExprMachineryState state,long amount) {
        instantiationWork(state.budget,amount,"Expr machinery work outside bounded profile","Expr machinery interrupted");
    }
    private static final int XR_ENTER=0,XR_CHILDREN=1,XR_LIFT_WAIT=2,XR_BUILD=3,XR_HELPER=4,XR_FINISH=5,XR_CLEAN=6,XR_ABSTRACT_SCAN=7,XR_CALLBACK_WAIT=8,XR_CALLBACK_NONE=9;
    private static int exprChildCount(int tag) {
        return tag==5||tag==6||tag==7?2:tag==8?3:tag==10||tag==11?1:0;
    }
    private static int exprChildField(int tag,int child) {
        return tag==5?child:tag==6||tag==7||tag==8?child+1:tag==10?1:2;
    }
    private static int exprCtorRole(int tag) {
        switch(tag) { case 0:return 0; case 3:return 1; case 4:return 2; case 5:return 3;
            case 6:return 4; case 7:return 5; case 8:return 6; case 10:return 7; case 11:return 8;
            default:throw error("Expr tag has no rebuilding constructor role"); }
    }
    private static final int[] EXPR_CTOR_TAGS={0,3,4,5,6,7,8,10,11};
    private ExprCredit exprCredit(Object value) { return new ExprCredit(value,false); }
    private void acquireExpr(ExprCredit credit) {
        require(credit!=null&&!credit.owned,"Expr credit already acquired"); inc(credit.value,1); credit.owned=true;
    }
    private void selectExpr(ExprReplaceFrame frame,Object value) {
        frame.result=exprCredit(value); acquireExpr(frame.result); frame.stage=XR_FINISH;
    }
    private boolean releaseExprCredit(RuntimeAction action,ExprMachineryState state,ExprCredit credit) {
        if(credit==null||!credit.owned) return false;
        state.retiring=credit; action.retiring=credit.value; action.releaseClaimed=false;
        boolean dispatch;
        try { dispatch=beginRelease(credit.value,1,ACTION_BODY); credit.owned=false; }
        finally { if(action.releaseClaimed) credit.owned=false; }
        if(!dispatch) { state.retiring=null; action.retiring=null; action.releaseClaimed=false; }
        return dispatch;
    }
    private void pushExprFrame(ExprMachineryState state,ReplaceJob job,Object input,int offset) {
        require(offset>=0&&offset<=MAX_EXPR_JOB_OFFSET,"Expr binder offset outside bounded profile");
        require(state.liveFrames<MAX_EXPR_JOB_FRAMES,"Expr machinery frame limit");
        Node node=exprNode(input); job.frames.addLast(new ExprReplaceFrame(node,offset)); state.liveFrames++;
    }
    private void pushReplaceJob(ExprMachineryState state,int mode,Object input,int cutoff,long amount,Object[] substitutions) {
        require(state.jobs.size()<MAX_EXPR_JOB_FRAMES,"Expr machinery job limit");
        ReplaceJob job=new ReplaceJob(); job.input=input; job.mode=mode; job.cutoff=cutoff; job.amount=amount;
        job.substitutions=substitutions; state.jobs.addLast(job);
    }
    private static boolean sameExprField(Object left,Object right) {
        return left==right||!(left instanceof Node)&&left!=null&&left.equals(right);
    }
    private ExprPacket prepareExprConstructorPacket(ExprConstructorPolicy policy,int role,Object[] values) {
        Function helper=exprConstructor(policy,role);
        require(helper.params.length==values.length,"Expr constructor packet arity differs");
        ExprPacket packet=new ExprPacket(); packet.function=helper; packet.role=role;
        packet.arguments=values.clone(); packet.owned=new boolean[values.length]; packet.expectedTag=EXPR_CTOR_TAGS[role]; packet.expectedFlag=-1;
        int fields=packet.expectedTag==6||packet.expectedTag==7?3:packet.expectedTag==8?4:values.length;
        packet.expectedFields=Arrays.copyOf(values,fields);
        if(packet.expectedTag>=6&&packet.expectedTag<=8) {
            require(values[fields] instanceof Long,"Expr constructor boxed flag requires Long");
            long flag=(Long)values[fields]; require(flag>=0&&flag<=(packet.expectedTag==8?1:4),"Expr constructor flag outside profile");
            packet.expectedFlag=(int)flag;
        }
        return packet;
    }
    private void acquireExprConstructorPacket(ExprPacket packet) {
        IdentityHashMap<Node,Integer> owners=new IdentityHashMap<>();
        for(int i=0;i<packet.arguments.length;i++) {
            Object value=packet.arguments[i]; validateHostObject(value); inc(value,1); packet.owned[i]=true;
            if(value instanceof Node) owners.merge((Node)value,1,Integer::sum);
        }
        for(Map.Entry<Node,Integer> entry:owners.entrySet())
            require(entry.getKey().rc==0||entry.getKey().rc>=entry.getValue(),"Expr constructor packet owner occurrences differ");
    }
    private ExprCredit takeExprConstructorResult(RuntimeAction action,ExprPacket packet) {
        Object value=objects[action.slot]; Node node=exprNode(value);
        require(node.tag==packet.expectedTag&&node.fields.length==packet.expectedFields.length,"Expr constructor returned unexpected head");
        for(int i=0;i<node.fields.length;i++) require(sameExprField(node.fields[i],packet.expectedFields[i]),"Expr constructor returned unexpected child");
        if(packet.expectedFlag>=0) require((node.scalars[8]&255)==packet.expectedFlag,"Expr constructor returned unexpected flag");
        ExprCredit credit=new ExprCredit(value,true); objects[action.slot]=null; return credit;
    }
    private void callExprConstructor(RuntimeAction action,ExprMachineryState state,int role,Object[] values,ExprReplaceFrame frame,BetaJob beta) {
        exprJobWork(state,1); require(state.call==null&&objects[action.slot]==null,"Expr constructor receiver occupied");
        ExprPacket packet=prepareExprConstructorPacket(state.policy,role,values); packet.replaceFrame=frame; packet.beta=beta;
        state.call=packet; acquireExprConstructorPacket(packet); packet.started=true;
        enterExplicit(packet.function,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Expr constructor did not publish frame or CodeRequest");
    }
    private void receiveExprConstructor(RuntimeAction action,ExprMachineryState state) {
        ExprPacket packet=state.call; require(packet.entered,"Expr constructor receiver precedes entry");
        require(packet.replaceFrame!=null||packet.beta!=null&&packet.beta.replacement==null,"Missing Expr beta receiver");
        ExprCredit credit=takeExprConstructorResult(action,packet);
        if(packet.replaceFrame!=null) { packet.replaceFrame.result=credit; packet.replaceFrame.stage=XR_FINISH; }
        else packet.beta.replacement=credit;
        state.call=null;
    }
    private void requestBVar(RuntimeAction action,ExprMachineryState state,ExprReplaceFrame frame,BigInteger index) {
        exprJobWork(state,1+(index.bitLength()+63L)/64);
        require(index.signum()>=0&&index.compareTo(BigInteger.valueOf(MAX_EXPR_JOB_OFFSET-1))<=0,"Expr bvar constructor range outside bounded profile");
        Object logical=index.bitLength()<=63?Long.valueOf(index.longValue()):index;
        frame.stage=XR_HELPER; callExprConstructor(action,state,0,new Object[]{logical},frame,null);
    }
    private void rebuildExpr(RuntimeAction action,ExprMachineryState state,ExprReplaceFrame frame) {
        Node original=frame.original; int count=exprChildCount(original.tag); boolean changed=false;
        Object[] fields=original.fields.clone();
        for(int i=0;i<count;i++) {
            require(frame.children[i]!=null&&frame.children[i].owned,"Expr replacement child result missing");
            int at=exprChildField(original.tag,i); fields[at]=frame.children[i].value;
            changed|=!sameExprField(fields[at],original.fields[at]);
        }
        if(!changed) { selectExpr(frame,original); return; }
        Object[] values=fields;
        if(original.tag>=6&&original.tag<=8) {
            values=Arrays.copyOf(fields,fields.length+1); values[fields.length]=Long.valueOf(original.scalars[8]&255);
        }
        frame.stage=XR_HELPER; callExprConstructor(action,state,exprCtorRole(original.tag),values,frame,null);
    }
    private void completeReplaceFrame(ExprMachineryState state,ReplaceJob job,ExprReplaceFrame frame) {
        require(frame.result!=null&&frame.result.owned,"Missing Expr replacement result owner");
        require(job.frames.peekLast()==frame,"Expr replacement frame order differs");
        Iterator<ExprReplaceFrame> ancestors=job.frames.descendingIterator(); ancestors.next();
        ExprReplaceFrame parent=ancestors.hasNext()?ancestors.next():null;
        if(parent!=null) require(parent.stage==XR_CHILDREN&&parent.cursor<parent.children.length&&parent.children[parent.cursor]==null,
                "Expr parent is not waiting for an empty child receiver");
        if(frame.active) job.active.remove(frame.original);
        if(parent==null) { job.result=frame.result; job.stage=2; job.cache.clear(); job.callbackCache.clear(); job.active.clear(); job.cleanup=0; }
        else parent.children[parent.cursor++]=frame.result;
        frame.result=null; job.frames.removeLast(); state.liveFrames--;
    }
    /** Borrowed view of caller-owned substitutions, never a guest Array or owner.
     * Direction is explicit: native reverse-empty still visits loose bvars. */
    private static final class ExprSubstSlice {
        final Node array;
        final Object single;
        final int begin,end;
        final boolean reverse;
        ExprSubstSlice(Node array,Object single,int begin,int end,boolean reverse) {
            this.array=array; this.single=single; this.begin=begin; this.end=end; this.reverse=reverse;
        }
        int size() { return end-begin; }
        Object at(int relative) {
            require(relative>=0&&relative<size(),"Expr substitution index outside selected slice");
            return array==null?single:array.fields[reverse?end-1-relative:begin+relative];
        }
    }
    private static int exprSubstitutionCount(ReplaceJob job) { return job.slice==null?job.substitutions.length:job.slice.size(); }
    private static Object exprSubstitutionAt(ReplaceJob job,int relative) { return job.slice==null?job.substitutions[relative]:job.slice.at(relative); }
    private static boolean pureExprTransform(int op) {
        return op==EXPR_INSTANTIATE||op==EXPR_INSTANTIATE1||op==EXPR_INSTANTIATE_RANGE
                ||op==EXPR_INSTANTIATE_REV||op==EXPR_INSTANTIATE_REV_RANGE||op==EXPR_LIFT||op==EXPR_LOWER;
    }
    private static final int MAX_EXPR_LOOSE_WORK=1_000_000,MAX_EXPR_LOOSE_STACK=100_000,MAX_EXPR_LOOSE_KEYS=100_000;
    private static final class LooseSearchFrame {
        final Node node; final int offset; final boolean exit;
        LooseSearchFrame(Node node,int offset,boolean exit) { this.node=node; this.offset=offset; this.exit=exit; }
    }
    /** Borrowed atomic search: no helper call, RC change or persisted memo.
     * Native likely-unshared is rc==1, deliberately ignoring logical MT. */
    private final class LooseBVarSearch {
        final ArrayDeque<LooseSearchFrame> stack=new ArrayDeque<>();
        final IdentityHashMap<Node,HashSet<Integer>> visited=new IdentityHashMap<>(),active=new IdentityHashMap<>();
        long work; int keys;
        void charge(long amount) {
            require(amount>=0&&amount<=MAX_EXPR_LOOSE_WORK-work,"Expr loose search work outside bounded runtime profile");
            long before=work; work+=amount;
            if((before>>>10)!=(work>>>10)&&Thread.currentThread().isInterrupted()) throw error("Expr loose search interrupted");
        }
        void push(Node node,int offset,boolean exit) {
            require(offset>=0&&offset<=MAX_EXPR_JOB_OFFSET,"Expr loose search binder offset outside profile");
            require(stack.size()<MAX_EXPR_LOOSE_STACK,"Expr loose search stack outside profile");
            stack.push(new LooseSearchFrame(node,offset,exit));
        }
        boolean apply(Object value,Object indexValue) {
            Node root=exprNode(value); BigInteger index=pureExprNat(indexValue);
            charge(1);
            if(index.compareTo(SMALL_MAX)>0||(exprCachedData(root)>>>44)==0) return false;
            long wanted=index.longValue()&0xffffffffL; push(root,0,false);
            while(!stack.isEmpty()) {
                charge(1); LooseSearchFrame frame=stack.pop(); Node node=exprNode(frame.node); int offset=frame.offset;
                if(frame.exit) {
                    HashSet<Integer> offsets=active.get(node);
                    require(offsets!=null&&offsets.remove(offset),"Expr loose search active ledger differs");
                    if(offsets.isEmpty()) active.remove(node); continue;
                }
                HashSet<Integer> current=active.get(node);
                require(current==null||!current.contains(offset),"Cyclic Expr loose search outside source profile");
                if(node.tag!=0&&node.tag!=3&&node.tag!=4&&node.rc!=1) {
                    HashSet<Integer> offsets=visited.get(node);
                    if(offsets!=null&&offsets.contains(offset)) continue;
                    require(keys<MAX_EXPR_LOOSE_KEYS,"Expr loose search visited key bound"); keys++; charge(1);
                    if(offsets==null) { offsets=new HashSet<>(); visited.put(node,offsets); }
                    offsets.add(offset);
                }
                long target=(wanted+offset)&0xffffffffL;
                if(target<wanted||target>=(exprCachedData(node)>>>44)) continue;
                if(node.tag==0) {
                    BigInteger actual=pureExprNat(node.fields[0]); charge(1+(actual.bitLength()+63L)/64);
                    if(actual.equals(BigInteger.valueOf(target))) return true;
                    continue;
                }
                int count=exprChildCount(node.tag); if(count==0) continue;
                if(current==null) { current=new HashSet<>(); active.put(node,current); }
                require(current.add(offset),"Expr loose search active duplicate");
                push(node,offset,true);
                for(int i=count-1;i>=0;i--) {
                    boolean body=(node.tag==6||node.tag==7)&&i==1||node.tag==8&&i==2;
                    require(!body||offset<MAX_EXPR_JOB_OFFSET,"Expr loose search binder offset bound");
                    push(exprNode(node.fields[exprChildField(node.tag,i)]),offset+(body?1:0),false);
                }
            }
            return false;
        }
    }
    private static boolean borrowedExprLooseQuery(int op) { return op==EXPR_HAS_LOOSE; }
    /** Preserve the full immediate comparison before C++ unsigned32 narrowing.
     * Only the continued assertion domain is rejected; earlier source identity
     * shortcuts remain identity even if narrowed cutoff<delta. */
    private long[] lowerExprParameters(Object input,Object cutoffValue,Object deltaValue) {
        BigInteger cutoff=pureExprNat(cutoffValue),delta=pureExprNat(deltaValue);
        long s=0,d=0;
        if(cutoff.compareTo(SMALL_MAX)<=0&&delta.compareTo(SMALL_MAX)<=0&&cutoff.compareTo(delta)>=0) {
            s=cutoff.longValue()&0xffffffffL; d=delta.longValue()&0xffffffffL;
            if(d==0||s>=(exprCachedData(input)>>>44)) { s=0; d=0; }
            else require(s>=d,"Expr lower narrowed assertion domain outside bounded profile");
        }
        return new long[]{s,d};
    }

    private static BigInteger pureExprNat(Object value) {
        require(!(value instanceof BigInteger)||value.getClass()==BigInteger.class,"Expr transform Nat requires exact immutable BigInteger");
        return nat(value);
    }
    private Node pureExprArray(Object value) {
        Node node=array(value);
        require(node.tag==246&&!node.readyTask&&node.scalars.length==0&&kindMetadata(node) instanceof ArrayState,
                "Invalid Expr substitution Array storage");
        int size=arrayState(node).size;
        require(size>=0&&size<=node.fields.length&&node.fields.length<=MAX_ARRAY_CAPACITY,"Invalid Expr substitution Array live extent");
        return node;
    }
    private ExprSubstSlice pureExprSlice(Function function,Object[] args) {
        int op=function.intrinsic;
        if(op==EXPR_INSTANTIATE1) return new ExprSubstSlice(null,exprNode(args[1]),0,1,false);
        boolean range=op==EXPR_INSTANTIATE_RANGE||op==EXPR_INSTANTIATE_REV_RANGE;
        Node substitutions=pureExprArray(args[range?3:1]); int begin=0,end=arrayState(substitutions).size;
        if(range) {
            BigInteger b=pureExprNat(args[1]),e=pureExprNat(args[2]);
            require(b.compareTo(SMALL_MAX)<=0&&e.compareTo(SMALL_MAX)<=0&&b.compareTo(e)<=0
                    &&e.compareTo(BigInteger.valueOf(end))<=0,"Expr instantiation range panic path outside bounded profile");
            begin=b.intValue(); end=e.intValue();
        }
        return new ExprSubstSlice(substitutions,null,begin,end,op==EXPR_INSTANTIATE_REV||op==EXPR_INSTANTIATE_REV_RANGE);
    }
    private void validatePureExprTransform(Function function,Object[] args) {
        exprTransformsProfile(function);
        int op=function.intrinsic,arity=op==EXPR_LIFT||op==EXPR_LOWER?3:op==EXPR_INSTANTIATE_RANGE||op==EXPR_INSTANTIATE_REV_RANGE?4:2;
        require(args!=null&&args.length==arity,"Pure Expr transform native arity mismatch");
        exprNode(args[0]);
        if(op==EXPR_LOWER) lowerExprParameters(args[0],args[1],args[2]);
        else if(op==EXPR_LIFT) { pureExprNat(args[1]); pureExprNat(args[2]); }
        else pureExprSlice(function,args);
    }
    private void preparePureExprTransform(RuntimeAction action,Function function,Object[] args) {
        ExprMachineryState state=new ExprMachineryState(); state.policy=exprTransformsProfile(function);
        state.budget=new InstantiationBudget();
        if(function.intrinsic==EXPR_LOWER) {
            long[] parameters=lowerExprParameters(args[0],args[1],args[2]);
            require(parameters[0]<=MAX_EXPR_JOB_OFFSET,"Expr lower continued cutoff outside profile");
            pushReplaceJob(state,EXPR_LOWER_JOB,args[0],(int)parameters[0],parameters[1],new Object[0]);
        } else if(function.intrinsic==EXPR_LIFT) {
            BigInteger cutoff=pureExprNat(args[1]),delta=pureExprNat(args[2]);
            long s=0,d=0;
            // Typed canonical Nat values above signed63 are native heap Nats.
            // Immediates narrow to unsigned32 in the pinned C++ function call.
            if(cutoff.compareTo(SMALL_MAX)<=0&&delta.compareTo(SMALL_MAX)<=0) {
                s=cutoff.longValue()&0xffffffffL; d=delta.longValue()&0xffffffffL;
                if(d==0||s>=(exprCachedData(args[0])>>>44)) { s=0; d=0; }
            }
            // Any continued cutoff is below the source20-bit cached range.
            require(s<=MAX_EXPR_JOB_OFFSET,"Expr lift cutoff exceeds continued visitor profile");
            pushReplaceJob(state,EXPR_LIFT_JOB,args[0],(int)s,d,new Object[0]);
        } else {
            ReplaceJob job=new ReplaceJob(); job.mode=EXPR_SUBST_JOB; job.input=args[0];
            job.substitutions=new Object[0]; job.slice=pureExprSlice(function,args); state.jobs.addLast(job);
        }
        action.exprMachinery=state; objects[action.slot]=null;
    }

    /** Borrowed original/current aliases; only flagged acquired credits and the
     * owned receiver/Option packet can own. AP becomes authoritative at start. */
    private static final class ExprCallbackPacket {
        ExprReplaceFrame frame;
        Object[] arguments;
        ExprCredit current,predicate,option;
        int stage;
        boolean started,receiverOwned;
    }
    private void validateExprReplaceCallback(Object value) {
        Node predicate=node(value); acceptsClosure(predicate);
        Function target=predicate.closure; rootEntry(target); requireExecutableAbi(target);
        require(predicate.tag==245&&!predicate.array&&!predicate.ref&&!predicate.readyTask&&predicate.scalars.length==0
                &&predicate.fields.length+1==target.params.length,"Expr.replace requires a one-argument partial predicate closure");
        for(int lane:target.paramTypes) require(lane==OBJ,"Expr.replace callback requires boxed parameters");
        require(target.resultType==OBJ,"Expr.replace callback requires boxed Option Expr result");
        for(Object capture:predicate.fields) validateHostObject(capture);
        preflightCallable(target,true);
    }
    private void validateExprReplace(Function function,Object[] args) {
        exprTransformsProfile(function);
        require(args!=null&&args.length==2,"Expr.replace native arity mismatch");
        validateExprReplaceCallback(args[0]);
        require(node(args[0]).rc>=0&&exprNode(args[1]).rc>=0,"Invalid Expr.replace borrowed owner count");
    }
    private void prepareExprReplaceCallback(ExprMachineryState state,ExprReplaceFrame frame) {
        require(state.callback==null&&state.borrowedPredicate!=null,"Expr.replace callback packet already occupied");
        validateExprReplaceCallback(state.borrowedPredicate);
        ExprCallbackPacket packet=new ExprCallbackPacket(); packet.frame=frame;
        packet.arguments=new Object[]{frame.original};
        packet.current=exprCredit(frame.original); packet.predicate=exprCredit(state.borrowedPredicate);
        state.callback=packet; frame.stage=XR_CALLBACK_WAIT;
    }
    private void stepExprReplaceCallback(RuntimeAction action,ExprMachineryState state) {
        ExprCallbackPacket packet=state.callback; require(packet!=null,"Missing Expr.replace callback packet");
        if(packet.stage==0) {
            // Pinned replace_fn, unlike Find: Expr INC precedes predicate INC.
            acquireExpr(packet.current); acquireExpr(packet.predicate);
            packet.stage=1; packet.started=true;
            packet.current.owned=false; packet.predicate.owned=false;
            applyExplicit(packet.predicate.value,packet.arguments,ACTION_BODY,action.slot); return;
        }
        if(packet.stage==1) {
            Object value=objects[action.slot]; packet.receiverOwned=true;
            if(ERASED.equals(value)) {
                objects[action.slot]=null; packet.receiverOwned=false;
                packet.frame.stage=XR_CALLBACK_NONE; state.callback=null; return;
            }
            Node option=constructorNode(value);
            require(option.closure==null&&option.tag==1&&option.fields.length==1&&option.scalars.length==0&&option.rc>=0,
                    "Expr.replace callback did not return canonical Option Expr");
            Node replacement=exprNode(option.fields[0]);
            // Allocate both escrows before acquiring or moving any owner.
            packet.frame.result=exprCredit(replacement); packet.option=exprCredit(option);
            acquireExpr(packet.frame.result);
            packet.option.owned=true; objects[action.slot]=null; packet.receiverOwned=false;
            packet.stage=2;
        }
        if(packet.stage==2) {
            packet.stage=3;
            if(releaseExprCredit(action,state,packet.option)) return;
        }
        require(packet.stage==3&&!packet.option.owned,"Expr.replace returned before Option cleanup");
        packet.frame.stage=XR_FINISH; state.callback=null;
    }

    private void stepReplaceJob(RuntimeAction action,ExprMachineryState state,ReplaceJob job) {
        if(job.stage==0) {
            if(job.mode==EXPR_CALLBACK_JOB) { job.stage=1; pushExprFrame(state,job,job.input,0); return; }
            Node input=exprNode(job.input); long range=exprCachedData(input)>>>44;
            boolean shortcut=job.mode==EXPR_ABSTRACT_JOB?!abstractFlags(input):
                    (job.mode==EXPR_LIFT_JOB||job.mode==EXPR_LOWER_JOB)?(job.amount==0||job.cutoff>=range):((exprSubstitutionCount(job)==0&&(job.slice==null||!job.slice.reverse))||range==0);
            if(shortcut) {
                job.result=exprCredit(input); acquireExpr(job.result); job.stage=2; return;
            }
            job.stage=1; pushExprFrame(state,job,input,0); return;
        }
        if(job.stage==2) {
            if(job.cleanup<job.cacheValues.size()) {
                ExprCredit credit=job.cacheValues.get(job.cacheValues.size()-1-job.cleanup++); releaseExprCredit(action,state,credit); return;
            }
            require(job.reservedCacheEntries==job.cacheValues.size()&&state.liveCacheEntries>=job.reservedCacheEntries,"Expr cache reservation ledger differs");
            state.liveCacheEntries-=job.reservedCacheEntries; job.reservedCacheEntries=0;
            job.cacheValues.clear(); job.input=null; job.substitutions=null; job.slice=null; job.abstractArray=null; job.completed=true; return;
        }
        ExprReplaceFrame frame=job.frames.peekLast(); require(frame!=null,"Missing Expr replacement frame"); Node node=frame.original;
        if(frame.stage==XR_ENTER) {
            // Public callback replace uses !exclusive; offset jobs retain the
            // distinct native likely-unshared RC hint, intentionally ignoring MT.
            frame.shared=job.mode==EXPR_CALLBACK_JOB?!exclusive(node):node.rc!=1;
            HashMap<Integer,ExprCredit> offsets=frame.shared&&job.mode!=EXPR_CALLBACK_JOB?job.cache.get(node):null;
            ExprCredit cached=frame.shared&&job.mode==EXPR_CALLBACK_JOB?job.callbackCache.get(node):offsets==null?null:offsets.get(frame.offset);
            if(cached!=null) { require(cached.owned,"Expr replacement cache owner missing"); selectExpr(frame,cached.value); frame.shared=false; return; }
            if(job.mode==EXPR_CALLBACK_JOB) { prepareExprReplaceCallback(state,frame); return; }
            if(job.mode==EXPR_ABSTRACT_JOB) {
                if(!abstractFlags(node)) { selectExpr(frame,node); return; }
                if(node.tag==1||node.tag==2) {
                    frame.abstractScan=job.prefixLength; frame.stage=XR_ABSTRACT_SCAN; return;
                }
            } else {
                long threshold=(long)job.cutoff+frame.offset;
                if(job.mode==EXPR_LOWER_JOB&&threshold>0xffffffffL) { selectExpr(frame,node); return; }
                if(threshold>=(exprCachedData(node)>>>44)) { selectExpr(frame,node); return; }
                if(node.tag==0) {
                    BigInteger index=nat(node.fields[0]); exprJobWork(state,1+(index.bitLength()+63L)/64);
                    if(index.compareTo(BigInteger.valueOf(threshold))>=0) {
                        if(job.mode==EXPR_LIFT_JOB) { requestBVar(action,state,frame,index.add(BigInteger.valueOf(job.amount))); return; }
                        if(job.mode==EXPR_LOWER_JOB) { requestBVar(action,state,frame,index.subtract(BigInteger.valueOf(job.amount))); return; }
                        BigInteger at=index.subtract(BigInteger.valueOf(frame.offset));
                        if(at.compareTo(BigInteger.valueOf(exprSubstitutionCount(job)))<0) {
                            frame.stage=XR_LIFT_WAIT;
                            pushReplaceJob(state,EXPR_LIFT_JOB,exprSubstitutionAt(job,at.intValue()),0,frame.offset,new Object[0]); return;
                        }
                        requestBVar(action,state,frame,index.subtract(BigInteger.valueOf(exprSubstitutionCount(job)))); return;
                    }
                }
            }
            startExprReplaceChildren(job,frame); return;
        }
        if(frame.stage==XR_CALLBACK_NONE) { startExprReplaceChildren(job,frame); return; }
        if(frame.stage==XR_ABSTRACT_SCAN) {
            if(frame.abstractScan==0) { selectExpr(frame,node); return; }
            int i=--frame.abstractScan; exprJobWork(state,1);
            Node candidate=exprNode(job.abstractArray.fields[i]);
            if(candidate.tag==node.tag&&abstractNamesEqual(state,node.fields[0],candidate.fields[0]))
                requestBVar(action,state,frame,BigInteger.valueOf((long)frame.offset+job.prefixLength-i-1));
            return;
        }
        if(frame.stage==XR_LIFT_WAIT) {
            require(job.childResult!=null&&job.childResult.owned,"Missing substituted lifted result");
            frame.result=job.childResult; job.childResult=null; frame.stage=XR_FINISH; return;
        }
        if(frame.stage==XR_CHILDREN) {
            int count=exprChildCount(node.tag);
            if(frame.cursor<count) {
                int offset=frame.offset;
                if(job.mode!=EXPR_CALLBACK_JOB&&((node.tag==6||node.tag==7)&&frame.cursor==1||node.tag==8&&frame.cursor==2)) offset=Math.addExact(offset,1);
                pushExprFrame(state,job,node.fields[exprChildField(node.tag,frame.cursor)],offset); return;
            }
            frame.stage=XR_BUILD;
        }
        if(frame.stage==XR_BUILD) { rebuildExpr(action,state,frame); return; }
        if(frame.stage==XR_FINISH) {
            if(frame.shared) {
                require(state.liveCacheEntries<MAX_EXPR_JOB_CACHE,"Expr machinery live cache entries outside bounded profile");
                state.liveCacheEntries++; job.reservedCacheEntries++;
                ExprCredit stored=exprCredit(frame.result.value); job.cacheValues.add(stored); acquireExpr(stored);
                if(job.mode==EXPR_CALLBACK_JOB) require(job.callbackCache.putIfAbsent(node,stored)==null,"Duplicate callback Expr cache entry");
                else {
                    HashMap<Integer,ExprCredit> offsets=job.cache.computeIfAbsent(node,key->new HashMap<>());
                    require(offsets.putIfAbsent(frame.offset,stored)==null,"Duplicate Expr replacement cache entry");
                }
            }
            frame.stage=XR_CLEAN; frame.cleanup=0;
        }
        if(frame.stage==XR_CLEAN) {
            if(frame.cleanup<3) { ExprCredit credit=frame.children[2-frame.cleanup++]; releaseExprCredit(action,state,credit); return; }
            completeReplaceFrame(state,job,frame); return;
        }
        throw error("Expr replacement constructor continuation did not return");
    }
    private void startExprReplaceChildren(ReplaceJob job,ExprReplaceFrame frame) {
        Node node=frame.original; int count=exprChildCount(node.tag);
        if(count==0) { selectExpr(frame,node); return; }
        require(!job.active.containsKey(node),"Expr replacement structural cycle outside profile");
        job.active.put(node,Boolean.TRUE); frame.active=true; frame.stage=XR_CHILDREN; frame.cursor=0;
    }
    private static final int XB_INIT=0,XB_DESCEND=1,XB_ZETA_WAIT=2,XB_LAST_WAIT=3,XB_BASE_WAIT=4,
            XB_APP=5,XB_APP_WAIT=6,XB_DRAIN_TEMP=7,XB_DRAIN_FRAMES=8,XB_DRAIN_FUNCTION=9,XB_DONE=10;
    private void pushBetaFrame(ExprMachineryState state,BetaJob job,ExprCredit credit,boolean acquire) {
        require(state.liveFrames<MAX_EXPR_JOB_FRAMES,"Expr machinery frame limit");
        job.frames.addLast(new ExprBetaFrame(credit)); state.liveFrames++;
        if(acquire) acquireExpr(credit); else require(credit.owned,"Beta child parameter lacks moved result owner");
    }
    private void stepBetaJob(RuntimeAction action,ExprMachineryState state,BetaJob job) {
        if(job.stage==XB_INIT) {
            require(job.function!=null&&job.function.owned,"Beta wrapper function owner missing");
            if(job.reverseArgs.length==0) { job.result=job.function; job.function=null; job.completed=true; return; }
            pushBetaFrame(state,job,exprCredit(job.function.value),true); job.stage=XB_DESCEND; return;
        }
        if(job.stage==XB_DESCEND) {
            ExprBetaFrame frame=job.frames.peekLast(); require(frame!=null&&frame.expression.owned,"Beta recursive parameter owner missing");
            Node expression=exprNode(frame.expression.value);
            if(expression.tag==6) {
                if(job.consumed+1<job.reverseArgs.length) {
                    job.consumed++; pushBetaFrame(state,job,exprCredit(expression.fields[2]),true); return;
                }
                job.stage=XB_LAST_WAIT; pushReplaceJob(state,EXPR_SUBST_JOB,expression.fields[2],0,0,job.reverseArgs); return;
            }
            if(expression.tag==8&&job.consumed<job.reverseArgs.length) {
                job.stage=XB_ZETA_WAIT;
                pushReplaceJob(state,EXPR_SUBST_JOB,expression.fields[3],0,0,new Object[]{expression.fields[2]}); return;
            }
            if(expression.tag==10) { pushBetaFrame(state,job,exprCredit(expression.fields[1]),true); return; }
            job.remaining=job.reverseArgs.length-job.consumed;
            job.stage=XB_BASE_WAIT;
            pushReplaceJob(state,EXPR_SUBST_JOB,expression,0,0,Arrays.copyOfRange(job.reverseArgs,job.remaining,job.reverseArgs.length)); return;
        }
        if(job.stage==XB_ZETA_WAIT) {
            require(job.childResult!=null&&job.childResult.owned,"Beta zeta replacement owner missing");
            ExprCredit child=job.childResult;
            // C++20 prvalue initializes the next by-value parameter directly.
            // Keep its receiver owner until the frame-cap preflight succeeds.
            pushBetaFrame(state,job,child,false); job.childResult=null; job.stage=XB_DESCEND; return;
        }
        if(job.stage==XB_LAST_WAIT) {
            require(job.childResult!=null&&job.childResult.owned,"Beta final substitution owner missing");
            job.result=job.childResult; job.childResult=null; job.stage=XB_DRAIN_FRAMES; return;
        }
        if(job.stage==XB_BASE_WAIT) {
            require(job.childResult!=null&&job.childResult.owned,"Beta application base owner missing");
            // The instantiate full-expression temporary anchors mk_rev_app's f,
            // independently from that function's owned accumulator r.
            job.temporary=job.childResult; job.childResult=null;
            job.accumulator=exprCredit(job.temporary.value); acquireExpr(job.accumulator); job.stage=XB_APP; return;
        }
        if(job.stage==XB_APP) {
            require(job.accumulator!=null&&job.accumulator.owned,"Beta application accumulator missing");
            if(job.remaining==0) { job.result=job.accumulator; job.accumulator=null; job.stage=XB_DRAIN_TEMP; return; }
            job.stage=XB_APP_WAIT;
            callExprConstructor(action,state,3,new Object[]{job.accumulator.value,job.reverseArgs[job.remaining-1]},null,job); return;
        }
        if(job.stage==XB_APP_WAIT) {
            require(job.replacement!=null&&job.replacement.owned,"Beta application constructor owner missing");
            ExprCredit old=job.accumulator; job.accumulator=job.replacement; job.replacement=null;
            job.remaining--; job.stage=XB_APP; releaseExprCredit(action,state,old); return;
        }
        if(job.stage==XB_DRAIN_TEMP) { job.stage=XB_DRAIN_FRAMES; releaseExprCredit(action,state,job.temporary); return; }
        if(job.stage==XB_DRAIN_FRAMES) {
            if(!job.frames.isEmpty()) {
                ExprBetaFrame frame=job.frames.removeLast(); state.liveFrames--;
                releaseExprCredit(action,state,frame.expression); return;
            }
            job.stage=XB_DRAIN_FUNCTION;
        }
        if(job.stage==XB_DRAIN_FUNCTION) { job.stage=XB_DONE; releaseExprCredit(action,state,job.function); return; }
        require(job.stage==XB_DONE&&job.result!=null&&job.result.owned,"Incomplete beta job result");
        job.function=null; job.temporary=null; job.accumulator=null; job.replacement=null; job.reverseArgs=null; job.completed=true;
    }
    private void stepExprMachinery(RuntimeAction action) {
        ExprMachineryState state=action.exprMachinery; require(state!=null,"Missing private Expr machinery state"); exprJobWork(state,1);
        if(state.retiring!=null) {
            require(!state.retiring.owned,"Expr cleanup returned without retiring owner claim");
            state.retiring=null; action.retiring=null; action.releaseClaimed=false;
        }
        if(state.call!=null) { receiveExprConstructor(action,state); return; }
        if(state.callback!=null) { stepExprReplaceCallback(action,state); return; }
        if(state.stage==0) {
            ExprJob job=state.jobs.peekLast(); require(job!=null,"Missing private Expr job");
            if(!job.completed) {
                if(job instanceof ReplaceJob) stepReplaceJob(action,state,(ReplaceJob)job);
                else stepBetaJob(action,state,(BetaJob)job);
                return;
            }
            require(job.result!=null&&job.result.owned,"Private Expr job completed without result owner");
            Iterator<ExprJob> ancestors=state.jobs.descendingIterator(); ancestors.next();
            ExprJob parent=ancestors.hasNext()?ancestors.next():null;
            if(parent!=null) require(parent.childResult==null,"Private Expr child receiver occupied");
            if(parent==null) { state.result=job.result; state.stage=1; }
            else parent.childResult=job.result;
            job.result=null; state.jobs.removeLast();
            return;
        }
        if(state.stage==1) { state.stage=2; state.cleanup=0; releaseExprCredit(action,state,state.input); return; }
        if(state.stage==2) {
            if(state.cleanup<state.arguments.size()) {
                ExprCredit credit=state.arguments.get(state.arguments.size()-1-state.cleanup++); releaseExprCredit(action,state,credit); return;
            }
            state.stage=3;
        }
        require(state.stage==3&&state.result!=null&&state.result.owned&&state.liveFrames==0&&state.liveCacheEntries==0,"Incomplete private Expr output");
        Object result=state.result.value; action.output=result; state.result.owned=false;
        state.input=null; state.result=null; state.arguments.clear(); state.borrowedPredicate=null; state.callback=null; action.arguments=null; action.exprMachinery=null;
        finishAction(action,result);
    }

    private static boolean abstractPrimitive(int op) { return op==EXPR_ABSTRACT_RANGE||op==EXPR_ABSTRACT; }
    private boolean abstractFlags(Node node) { return (exprCachedData(node)&(7L<<40))!=0; }
    private boolean abstractNamesEqual(ExprMachineryState state,Object left,Object right) {
        ExprEquality comparison=new ExprEquality(false); comparison.work=state.budget.work;
        try { return nameEquals(left,right,comparison); }
        finally { state.budget.work=comparison.work; }
    }
    private int abstractPrefix(Function function,Object[] args) {
        int arity=function.intrinsic==EXPR_ABSTRACT_RANGE?3:2;
        require(args!=null&&args.length==arity,"Expr abstraction native arity differs");
        exprNode(args[0]); Node values=array(args[arity-1]); int size=arrayState(values).size;
        int prefix=size;
        if(function.intrinsic==EXPR_ABSTRACT_RANGE) {
            Object count=args[1];
            require(count instanceof Long&&((Long)count)>=0||count instanceof BigInteger&&((BigInteger)count).signum()>=0,
                    "Expr abstraction requires nonnegative Nat range");
            // Native heap-Nat branch selects the whole array, even for a small MPZ.
            if(count instanceof Long) prefix=(int)Math.min((Long)count,(long)size);
        }
        require(prefix<=MAX_EXPR_JOB_FRAMES,"Expr abstraction prefix outside bounded profile");
        return prefix;
    }
    private void validateAbstractArguments(Function function,Object[] args) {
        exprTransformsProfile(function); abstractPrefix(function,args);
    }
    private void prepareAbstractAction(RuntimeAction action,Function function,Object[] args) {
        ExprMachineryState state=new ExprMachineryState(); state.policy=exprTransformsProfile(function);
        state.budget=new InstantiationBudget();
        ReplaceJob job=new ReplaceJob(); job.mode=EXPR_ABSTRACT_JOB; job.input=args[0];
        job.abstractArray=array(args[args.length-1]); job.prefixLength=abstractPrefix(function,args);
        state.jobs.addLast(job); action.exprMachinery=state; objects[action.slot]=null;
        // The parked native caller backs every borrowed input; no owned research
        // entry, argument vector, root reset or additional input INC is used.
    }

    /** Complete nineteen-role source binding for private pass-one research.
     * Descriptive Header hashes are not source authentication. */
    public static final class ExprInstantiationPolicy {
        final LevelInstantiationPolicy levels;
        final ExprConstructorPolicy constructors;
        final Header[] helpers;
        private ExprInstantiationPolicy(LevelInstantiationPolicy levels,ExprConstructorPolicy constructors,Header[] helpers) {
            this.levels=levels; this.constructors=constructors; this.helpers=helpers.clone();
        }
        public static ExprInstantiationPolicy originalHelpers(LevelInstantiationPolicy levels,Header[] helpers,Header[] constructors) {
            require(levels!=null&&helpers!=null&&helpers.length==5,"Five original Expr helper Headers required");
            ExprConstructorPolicy ctor=ExprConstructorPolicy.originalHeaders(constructors);
            require(ctor.helpers[0].source==levels.helpers[0].source,"Expr/Level constructor source bindings differ");
            String[] names={"Lean.MetavarContext.getExprAssignmentExp","Lean.MetavarContext.getDelayedMVarAssignmentExp","Lean.DelayedMetavarAssignment.fvarsExp","Lean.DelayedMetavarAssignment.mvarIdPendingExp","Lean.assignExp"},hashes={"eb558d18534d428bed55ddcbd54ff3ecdd2a357fe0ba865207a4176371b7b245","b2d125daab51fea96bc30d98915fc44af6a6879e8ab2996b2a3f6e23b415adca","b8515ae5926efd9f89b76b380588e4ba207aea6a4410bc0a3651890ad3fecd07","5f3e1d6a21afae8eedeb06a73dfc9ab5f7564494bd085ca44a38f28e9e3752fb","70435776e368ed0723d6159b1599c6c1f67eb7cfd3a12853ee417cb7d1807026"},results={"tobject","tobject","object","tobject","object"};
            String[][] parameters={new String[]{"object","tobject"},new String[]{"object","tobject"},new String[]{"object"},new String[]{"object"},new String[]{"object","tobject","object"}};
            for(int role=0;role<5;role++) {
                Header h=helpers[role];
                require(h!=null&&h.kind.equals("fdecl")&&h.originalSha256.equals(hashes[role]),"Expr helper role/source hash differs");
                require(h.source==levels.helpers[0].source,"Expr helper source bindings differ");
                Object name=Arrays.asList("anonymous");
                for(String segment:names[role].split("\\.")) name=Arrays.asList("str",name,segment);
                require(h.exactName.equals(frozenName(name)),"Expr helper typed Name differs");
                Map<String,Object> d=h.declaration;
                require(d.keySet().equals(new HashSet<>(Arrays.asList("f","info","type","xs")))
                        &&map(d.get("info")).isEmpty()&&d.get("f").equals(h.exactName)
                        &&results[role].equals(d.get("type")),"Expr helper declaration differs");
                List<Object> xs=list(d.get("xs")); require(xs.size()==parameters[role].length,"Expr helper raw arity differs");
                for(int i=0;i<xs.size();i++) {
                    Map<String,Object> p=map(xs.get(i)),x=map(p.get("x"));
                    require(p.keySet().equals(new HashSet<>(Arrays.asList("borrow","ty","x")))
                            &&x.keySet().equals(Collections.singleton("idx"))&&number(x.get("idx"))==i+1
                            &&Boolean.FALSE.equals(p.get("borrow"))&&parameters[role][i].equals(p.get("ty")),
                            "Expr helper raw parameter differs");
                }
                Map<String,Object> runtime=map(h.evidence.get("runtime"));
                require(runtime.keySet().equals(new HashSet<>(Arrays.asList("initializer","role")))
                        &&runtime.get("initializer")==null&&"ordinary".equals(runtime.get("role")),"Expr helper is not ordinary");
            }
            return new ExprInstantiationPolicy(levels,ctor,helpers);
        }
    }
    private Function exprInstantiationHelper(ExprInstantiationPolicy policy,int role) {
        Header header=policy.helpers[role]; int id=program.functionId(header); Function f=program.functions[id];
        require(f.header==header&&f.intrinsic==0&&f.hostExtern==null&&program.guestExports[id]==null,
                "Expr helper is not the current exact ordinary Function");
        requireExecutableAbi(f); require(f.resultType==OBJ,"Expr helper requires OBJ result");
        for(int lane:f.paramTypes) require(lane==OBJ,"Expr helper requires OBJ parameters");
        return preflightCallable(f,true);
    }
    private static final boolean EXPR_DIRECT_RESEARCH_READY=true;
    private static final int DS_IDLE=0,DS_RUNNING=1,DS_RESULT=2,DS_SEALED=3,DS_DRAINING=4,DS_DRAINED=5;
    private static final int MAX_DIRECT_FRAMES=100_000,MAX_DIRECT_CACHE=100_000,MAX_DIRECT_SAVED=100_000,
            MAX_DIRECT_NAMES=100_000,MAX_DIRECT_ARGUMENTS=100_000,MAX_DIRECT_LEVELS=100_000;
    private abstract static class ExprDirectTask {
        ExprDirectTask child;
        ExprCredit result,received;
        int stage,cleanup;
        boolean completed,helperDone;
    }
    private static final class DirectVisitFrame extends ExprDirectTask {
        Node original; boolean shared; int cursor;
        ExprCredit cacheTemporary;
        final ExprCredit[] children=new ExprCredit[3];
        LevelCredit level; ExprCredit levels;
        DirectVisitFrame(Node original) { this.original=original; }
    }
    private static final class DirectMVarFrame extends ExprDirectTask {
        Node original; Object name; ExprCredit assigned,delayed;
        DirectMVarFrame(Node original) { this.original=original; }
    }
    private static final class DirectAssignmentFrame extends ExprDirectTask {
        Object name; ExprCredit option,assigned,newValue;
        boolean present;
        DirectAssignmentFrame(Object name) { this.name=name; }
    }
    private static final class DirectDelayedFrame extends ExprDirectTask {
        Object name; ExprCredit option,recordTemporary,pendingName,conditionResult;
        DirectDelayedFrame(Object name) { this.name=name; }
    }
    private static final class DirectAppFrame extends ExprDirectTask {
        Node original; Object cursor,name; ExprCredit assigned,delayed;
        DirectAppFrame(Node original) { this.original=original; }
    }
    private static final class DirectNonMvarAppFrame extends ExprDirectTask {
        Node original; ExprCredit argument,function;
        DirectNonMvarAppFrame(Node original) { this.original=original; }
    }
    private static final class DirectAppBetaFrame extends ExprDirectTask {
        Object cursor; ExprCredit functionOptional,betaParameter,argumentTemporary;
        final ArrayList<ExprCredit> arguments=new ArrayList<>();
        DirectAppBetaFrame(Object input,ExprCredit function) { this.cursor=input; this.functionOptional=function; }
    }
    private static final class DirectLevelFrame extends ExprDirectTask {
        Object input; LevelCredit levelResult;
        DirectLevelFrame(Object input) { this.input=input; }
    }
    private static final class DirectLevelsFrame extends ExprDirectTask {
        Object original,cursor; final ArrayList<Node> cells=new ArrayList<>();
        LevelCredit firstChanged,currentHead,headLoan;
        ExprCredit list,replacement,tailLoan,consCredit;
        Node building; int index,builtFields;
        DirectLevelsFrame(Object original) { this.original=original; }
    }
    private static final class DirectNameEntry {
        int hash; ExprCredit name;
        DirectNameEntry(int hash,ExprCredit name) { this.hash=hash; this.name=name; }
    }
    private static final class DirectHelperPacket {
        Function function; int role; Object[] arguments; boolean[] owned;
        boolean started,entered;
        ExprDirectTask target;
    }
    private static final class ExprDirectSession {
        MVarContextCell context; InstantiationBudget budget; LevelSession levels; ExprInstantiationPolicy policy;
        final ArrayDeque<ExprDirectTask> tasks=new ArrayDeque<>();
        final IdentityHashMap<Node,ExprCredit> cache=new IdentityHashMap<>();
        final ArrayList<ExprCredit> cacheValues=new ArrayList<>(),saved=new ArrayList<>();
        final HashMap<Integer,ArrayList<DirectNameEntry>> normalized=new HashMap<>();
        final ArrayList<DirectNameEntry> nameOwners=new ArrayList<>();
        DirectHelperPacket call; ExprPacket constructorCall;
        ExprCredit result,retiring;
        boolean hasUpdateableDelayed; int phase,drainStage,drainCursor;
    }
    private static final class ExprDirectResearchState {
        MVarContextCell context; InstantiationBudget budget; ExprDirectSession session;
        ExprCredit input,e1,output,reportExprLoan;
        int stage,outputFields;
    }
    /** Research pass-one report only, NEVER the original Expr instantiation ABI. */
    private void startExprDirectResearch(Header[] helpers,Header[] constructors,Object ownedContext,Object ownedExpr) {
        explicitOnly(); require(EXPR_DIRECT_RESEARCH_READY,"Private direct Expr pass is not yet complete");
        require(taskRuntime!=null,"Private direct Expr pass requires active explicit runtime");
        if(closed||disposed||untrackedFailure||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||continuationDepth!=0
                ||runtimeAction!=null||hostCompletion!=null||hostGuestRecord!=null||quietCurrent!=null||releasePending!=0
                ||releaseTransaction!=null||releaseRoot)
            throw new IllegalStateException("Private direct Expr pass requires an open idle engine");
        ExprInstantiationPolicy policy=ExprInstantiationPolicy.originalHelpers(levelInstantiationPolicy,helpers,constructors);
        for(int role=0;role<5;role++) { levelInstantiationHelper(policy.levels,role); exprInstantiationHelper(policy,role); }
        for(int role=0;role<9;role++) exprConstructor(policy.constructors,role);
        validateHostObject(ownedContext); Node root=exprNode(ownedExpr);
        if(ownedContext==ownedExpr) require(root.rc==0||root.rc>=2,"Private direct Expr input alias credits differ");
        RuntimeAction action=newAction(ACTION_EXPR_DIRECT_RESEARCH,null,null,0,ROOT,null);
        ExprDirectResearchState state=new ExprDirectResearchState(); state.context=new MVarContextCell();
        state.context.current=new LevelCredit(ownedContext,true); state.budget=new InstantiationBudget();
        ExprDirectSession session=new ExprDirectSession(); state.session=session; session.context=state.context; session.budget=state.budget;
        session.policy=policy; session.levels=newLevelSession(state.context,state.budget,policy.levels);
        state.input=new ExprCredit(ownedExpr,true); session.tasks.addLast(new DirectVisitFrame(root)); session.phase=DS_RUNNING;
        action.exprDirect=state; objects[action.slot]=null; publishAction(action);
        callsLeft=10_000_000; instructions=0; entry=null; result=null; releaseRoot=false; phase=RUNNING;
    }
    private void directHelperEntry(Function function,Object[] arguments) {
        RuntimeAction action=runtimeAction;
        ExprDirectSession session=currentDirectSession(action);
        if(session==null||session.phase!=DS_RUNNING) return;
        DirectHelperPacket packet=session.call;
        if(packet==null||packet.entered||packet.function!=function||packet.arguments!=arguments) return;
        require(packet.started,"Direct Expr helper entered before packet publication");
        packet.entered=true; Arrays.fill(packet.owned,false);
    }
    private void directWork(ExprDirectSession session,long amount) {
        instantiationWork(session.budget,amount,"Direct Expr work outside bounded profile","Direct Expr interrupted");
    }
    private void pushDirect(ExprDirectSession session,ExprDirectTask task) {
        require(session.phase==DS_RUNNING&&session.tasks.size()<MAX_DIRECT_FRAMES,"Direct Expr task/frame limit outside profile");
        session.tasks.addLast(task);
    }
    private void directSelect(ExprDirectTask task,Object value) { task.result=exprCredit(value); acquireExpr(task.result); }
    private boolean releaseDirect(RuntimeAction action,ExprDirectSession session,ExprCredit credit) {
        if(credit==null||!credit.owned) return false;
        require(session.levels.retiring==null,"Simultaneous direct/Level retiring owners");
        session.retiring=credit; action.retiring=credit.value; action.releaseClaimed=false;
        boolean dispatch;
        try { dispatch=beginRelease(credit.value,1,ACTION_BODY); credit.owned=false; }
        finally { if(action.releaseClaimed) credit.owned=false; }
        if(!dispatch) { session.retiring=null; action.retiring=null; action.releaseClaimed=false; }
        return dispatch;
    }
    private void resumeDirectRetiring(RuntimeAction action,ExprDirectSession session) {
        require(session.retiring==null||session.levels.retiring==null,"Simultaneous direct/Level retiring owners");
        if(session.retiring!=null) {
            require(!session.retiring.owned,"Direct Expr retiring owner was not claimed");
            session.retiring=null; action.retiring=null; action.releaseClaimed=false;
        }
        resumeLevelRetiring(action,session.levels);
    }
    private ExprDirectTask takeDirectChild(ExprDirectTask parent,Class<?> expected) {
        require(parent.child!=null&&parent.child.completed&&expected.isInstance(parent.child),"Direct Expr child completion kind differs");
        return parent.child;
    }
    private ExprCredit takeDirectExprChild(ExprDirectTask parent,Class<?> expected) {
        ExprDirectTask child=takeDirectChild(parent,expected);
        require(child.result!=null&&child.result.owned,"Direct Expr child result owner missing");
        ExprCredit result=child.result; child.result=null; parent.child=null; return result;
    }
    private boolean directNameEqual(ExprDirectSession session,Object left,Object right) {
        return mvarNameEqual(session.budget,left,right);
    }
    private int directNameHash(ExprDirectSession session,Object value) {
        directWork(session,1); Node node=nameNode(value); return (int)(node==null?1723:readScalar(node,0,U64));
    }
    private boolean directNameContains(ExprDirectSession session,Object value) {
        int hash=directNameHash(session,value); ArrayList<DirectNameEntry> bucket=session.normalized.get(hash);
        if(bucket==null) return false;
        for(DirectNameEntry entry:bucket) {
            directWork(session,1); require(entry.name.owned,"Normalized Name key owner missing");
            if(directNameEqual(session,value,entry.name.value)) return true;
        }
        return false;
    }
    private void directNameInsert(ExprDirectSession session,Object value) {
        int hash=directNameHash(session,value); ArrayList<DirectNameEntry> bucket=session.normalized.get(hash);
        if(bucket!=null) for(DirectNameEntry entry:bucket) {
            directWork(session,1); if(directNameEqual(session,value,entry.name.value)) return;
        }
        require(session.nameOwners.size()<MAX_DIRECT_NAMES,"Direct Expr normalized Name limit");
        DirectNameEntry entry=new DirectNameEntry(hash,exprCredit(value)); session.nameOwners.add(entry);
        if(bucket==null) { bucket=new ArrayList<>(); session.normalized.put(hash,bucket); }
        bucket.add(entry); acquireExpr(entry.name);
    }
    private static boolean exprHasMVars(long word) { return (word&((1L<<41)|(1L<<42)))!=0; }
    private void requireDirectReceiverFree(RuntimeAction action,ExprDirectSession session) {
        require(session.call==null&&session.constructorCall==null&&session.levels.call==null&&objects[action.slot]==null,
                "Multiple outstanding direct/constructor/Level packets");
    }
    private void callDirectHelper(RuntimeAction action,ExprDirectSession session,ExprDirectTask target,int role) {
        directWork(session,1); require(role!=2,"Pass one does not call delayed fvars accessor"); requireDirectReceiverFree(action,session);
        Function helper=exprInstantiationHelper(session.policy,role);
        DirectHelperPacket packet=new DirectHelperPacket(); packet.function=helper; packet.role=role; packet.target=target;
        packet.arguments=new Object[helper.params.length]; packet.owned=new boolean[packet.arguments.length]; session.call=packet;
        if(role==3) {
            DirectDelayedFrame frame=(DirectDelayedFrame)target;
            require(frame.recordTemporary!=null&&frame.recordTemporary.owned,"Delayed accessor temporary owner missing");
            packet.arguments[0]=frame.recordTemporary.value; validateHostObject(packet.arguments[0]); inc(packet.arguments[0],1); packet.owned[0]=true;
        } else {
            LevelCredit context=session.context.current;
            require(context!=null&&context.owned,"Direct Expr current context owner missing"); packet.arguments[0]=context.value;
            if(role==4) { packet.owned[0]=true; context.owned=false; session.context.current=null; }
            else { inc(packet.arguments[0],1); packet.owned[0]=true; }
            Object name=role==1?((DirectDelayedFrame)target).name:((DirectAssignmentFrame)target).name;
            packet.arguments[1]=name; nameNode(name); inc(name,1); packet.owned[1]=true;
            if(role==4) {
                DirectAssignmentFrame frame=(DirectAssignmentFrame)target; require(frame.newValue!=null&&frame.newValue.owned,"Direct assignment result missing");
                packet.arguments[2]=frame.newValue.value; exprNode(packet.arguments[2]); inc(packet.arguments[2],1); packet.owned[2]=true;
            }
        }
        IdentityHashMap<Node,Integer> known=new IdentityHashMap<>();
        for(int i=0;i<packet.arguments.length;i++) {
            require(packet.owned[i],"Direct Expr helper argument not owned"); validateHostObject(packet.arguments[i]);
            if(packet.arguments[i] instanceof Node) known.merge((Node)packet.arguments[i],1,Integer::sum);
        }
        for(Map.Entry<Node,Integer> entry:known.entrySet()) require(entry.getKey().rc==0||entry.getKey().rc>=entry.getValue(),"Direct Expr helper alias credits differ");
        packet.started=true; enterExplicit(helper,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Direct Expr helper did not publish frame or CodeRequest");
    }
    private void validateDirectOption(Object value,boolean expression) {
        if(ERASED.equals(value)) return;
        Node option=constructorNode(value);
        require(option.tag==1&&option.fields.length==1&&option.scalars.length==0,"Direct Expr helper returned malformed Option");
        if(expression) exprNode(option.fields[0]); else validateHostObject(option.fields[0]);
    }
    private void receiveDirectHelper(RuntimeAction action,ExprDirectSession session) {
        DirectHelperPacket packet=session.call; require(packet.entered,"Direct Expr helper returned before entry");
        Object value=objects[action.slot]; ExprDirectTask target=packet.target;
        if(packet.role==4) {
            validateHostObject(value); require(session.context.current==null,"Direct Expr setter replaces a live context owner");
            session.context.current=new LevelCredit(value,true); objects[action.slot]=null; target.helperDone=true;
        } else {
            require(target.received==null,"Direct Expr helper result receiver occupied");
            if(packet.role==0||packet.role==1) validateDirectOption(value,packet.role==0);
            else if(packet.role==3) nameNode(value); else throw error("Unsupported direct Expr helper role");
            target.received=new ExprCredit(value,true); objects[action.slot]=null;
        }
        session.call=null;
    }
    private void callDirectConstructor(RuntimeAction action,ExprDirectSession session,ExprDirectTask target,int role,Object[] values) {
        directWork(session,1); requireDirectReceiverFree(action,session);
        ExprPacket packet=prepareExprConstructorPacket(session.policy.constructors,role,values); packet.directTarget=target;
        session.constructorCall=packet; acquireExprConstructorPacket(packet); packet.started=true;
        enterExplicit(packet.function,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Direct Expr constructor did not publish frame or CodeRequest");
    }
    private void receiveDirectConstructor(RuntimeAction action,ExprDirectSession session) {
        ExprPacket packet=session.constructorCall;
        require(packet.entered&&packet.directTarget!=null&&packet.directTarget.received==null,"Direct Expr constructor completion differs");
        ExprCredit result=takeExprConstructorResult(action,packet);
        packet.directTarget.received=result; session.constructorCall=null;
    }
    private void stepDirectAssignment(RuntimeAction action,ExprDirectSession session,DirectAssignmentFrame frame) {
        if(frame.stage==0) { frame.stage=1; callDirectHelper(action,session,frame,0); return; }
        if(frame.stage==1) {
            require(frame.received!=null&&frame.received.owned,"Direct getter Option missing"); frame.option=frame.received; frame.received=null;
            if(ERASED.equals(frame.option.value)) { frame.present=false; frame.stage=10; return; }
            frame.assigned=exprCredit(((Node)frame.option.value).fields[0]); acquireExpr(frame.assigned);
            if(!exprHasMVars(exprCachedData(frame.assigned.value))||directNameContains(session,frame.name)) {
                directSelect(frame,frame.assigned.value); frame.present=true; frame.stage=10; return;
            }
            directNameInsert(session,frame.name); frame.stage=2; pushDirect(session,new DirectVisitFrame(exprNode(frame.assigned.value))); return;
        }
        if(frame.stage==2) {
            frame.newValue=takeDirectExprChild(frame,DirectVisitFrame.class);
            if(frame.newValue.value!=frame.assigned.value) {
                require(session.saved.size()<MAX_DIRECT_SAVED,"Direct Expr saved assignment limit");
                ExprCredit saved=exprCredit(frame.assigned.value); session.saved.add(saved); acquireExpr(saved);
                frame.stage=3; callDirectHelper(action,session,frame,4); return;
            }
            frame.stage=4;
        }
        if(frame.stage==3) { require(frame.helperDone,"Direct setter has no completed return"); frame.helperDone=false; frame.stage=4; }
        if(frame.stage==4) { directSelect(frame,frame.newValue.value); frame.present=true; frame.stage=10; }
        require(frame.stage==10,"Invalid direct assignment continuation");
        if(frame.cleanup<3) {
            ExprCredit credit=frame.cleanup==0?frame.newValue:frame.cleanup==1?frame.assigned:frame.option;
            frame.cleanup++; releaseDirect(action,session,credit); return;
        }
        frame.option=null; frame.assigned=null; frame.newValue=null; frame.completed=true;
    }
    private void stepDirectDelayed(RuntimeAction action,ExprDirectSession session,DirectDelayedFrame frame) {
        if(frame.stage==0) { frame.stage=1; callDirectHelper(action,session,frame,1); return; }
        if(frame.stage==1) {
            require(frame.received!=null&&frame.received.owned,"Delayed getter Option missing"); frame.option=frame.received; frame.received=null;
            if(ERASED.equals(frame.option.value)) { frame.result=frame.option; frame.option=null; frame.completed=true; return; }
            // option_ref::get_val returns by value; accessor then receives its own copy.
            frame.recordTemporary=exprCredit(((Node)frame.option.value).fields[0]); acquireExpr(frame.recordTemporary);
            frame.stage=2; callDirectHelper(action,session,frame,3); return;
        }
        if(frame.stage==2) {
            require(frame.received!=null&&frame.received.owned,"Delayed pending Name missing"); frame.pendingName=frame.received; frame.received=null;
            frame.stage=3; releaseDirect(action,session,frame.recordTemporary); return;
        }
        if(frame.stage==3) { frame.stage=4; pushDirect(session,new DirectAssignmentFrame(frame.pendingName.value)); return; }
        if(frame.stage==4) {
            DirectAssignmentFrame assignment=(DirectAssignmentFrame)takeDirectChild(frame,DirectAssignmentFrame.class);
            if(assignment.present) { require(assignment.result!=null&&assignment.result.owned,"Pending optional Expr owner missing");
                frame.conditionResult=assignment.result; assignment.result=null; session.hasUpdateableDelayed=true; }
            frame.child=null; frame.stage=5; releaseDirect(action,session,frame.conditionResult); return;
        }
        if(frame.stage==5) { frame.stage=6; releaseDirect(action,session,frame.pendingName); return; }
        require(frame.stage==6&&frame.option!=null&&frame.option.owned,"Delayed probe Option lifetime differs");
        frame.result=frame.option; frame.option=null; frame.recordTemporary=null; frame.pendingName=null; frame.conditionResult=null; frame.completed=true;
    }
    private void stepDirectMVar(RuntimeAction action,ExprDirectSession session,DirectMVarFrame frame) {
        if(frame.stage==0) { frame.name=frame.original.fields[0]; frame.stage=1; pushDirect(session,new DirectAssignmentFrame(frame.name)); return; }
        if(frame.stage==1) {
            DirectAssignmentFrame assignment=(DirectAssignmentFrame)takeDirectChild(frame,DirectAssignmentFrame.class);
            if(assignment.present) {
                require(assignment.result!=null&&assignment.result.owned,"Direct optional Expr missing"); frame.assigned=assignment.result; assignment.result=null;
                frame.child=null; directSelect(frame,frame.assigned.value); frame.stage=10;
            } else { frame.child=null; frame.stage=2; pushDirect(session,new DirectDelayedFrame(frame.name)); return; }
        }
        if(frame.stage==2) {
            frame.delayed=takeDirectExprChild(frame,DirectDelayedFrame.class); directSelect(frame,frame.original); frame.stage=10;
        }
        require(frame.stage==10,"Invalid direct MVar continuation");
        if(frame.cleanup<2) { ExprCredit credit=frame.cleanup++==0?frame.assigned:frame.delayed; releaseDirect(action,session,credit); return; }
        frame.assigned=null; frame.delayed=null; frame.completed=true;
    }
    private void stepDirectApp(RuntimeAction action,ExprDirectSession session,DirectAppFrame frame) {
        if(frame.stage==0) {
            if(frame.cursor==null) frame.cursor=frame.original;
            Node head=exprNode(frame.cursor);
            if(head.tag==5) { frame.cursor=head.fields[0]; return; }
            if(head.tag!=2) { frame.stage=5; pushDirect(session,new DirectNonMvarAppFrame(frame.original)); return; }
            frame.name=head.fields[0]; frame.stage=1; pushDirect(session,new DirectAssignmentFrame(frame.name)); return;
        }
        if(frame.stage==1) {
            DirectAssignmentFrame assignment=(DirectAssignmentFrame)takeDirectChild(frame,DirectAssignmentFrame.class);
            if(assignment.present) {
                require(assignment.result!=null&&assignment.result.owned,"Assigned function optional owner missing");
                ExprCredit function=assignment.result;
                DirectAppBetaFrame beta=new DirectAppBetaFrame(frame.original,function);
                pushDirect(session,beta); assignment.result=null; frame.child=null; frame.stage=4; return;
            }
            frame.child=null; frame.stage=2; pushDirect(session,new DirectDelayedFrame(frame.name)); return;
        }
        if(frame.stage==2) {
            frame.delayed=takeDirectExprChild(frame,DirectDelayedFrame.class);
            frame.stage=5; pushDirect(session,new DirectNonMvarAppFrame(frame.original)); return;
        }
        if(frame.stage==4) { frame.result=takeDirectExprChild(frame,DirectAppBetaFrame.class); frame.completed=true; return; }
        if(frame.stage==5) { frame.result=takeDirectExprChild(frame,DirectNonMvarAppFrame.class); frame.stage=6; releaseDirect(action,session,frame.delayed); return; }
        require(frame.stage==6,"Invalid direct App continuation"); frame.delayed=null; frame.completed=true;
    }
    private void stepDirectNonMvarApp(RuntimeAction action,ExprDirectSession session,DirectNonMvarAppFrame frame) {
        if(frame.stage==0) { frame.stage=1; pushDirect(session,new DirectVisitFrame(exprNode(frame.original.fields[1]))); return; }
        if(frame.stage==1) {
            frame.argument=takeDirectExprChild(frame,DirectVisitFrame.class); Node function=exprNode(frame.original.fields[0]); frame.stage=2;
            pushDirect(session,function.tag==5?new DirectNonMvarAppFrame(function):new DirectVisitFrame(function)); return;
        }
        if(frame.stage==2) {
            frame.function=takeDirectExprChild(frame,exprNode(frame.original.fields[0]).tag==5?DirectNonMvarAppFrame.class:DirectVisitFrame.class);
            if(frame.function.value==frame.original.fields[0]&&frame.argument.value==frame.original.fields[1]) { directSelect(frame,frame.original); frame.stage=4; }
            else { frame.stage=3; callDirectConstructor(action,session,frame,3,new Object[]{frame.function.value,frame.argument.value}); return; }
        }
        if(frame.stage==3) { require(frame.received!=null&&frame.received.owned,"App constructor result missing"); frame.result=frame.received; frame.received=null; frame.stage=4; }
        if(frame.stage==4) {
            if(frame.cleanup<2) { ExprCredit credit=frame.cleanup++==0?frame.function:frame.argument; releaseDirect(action,session,credit); return; }
            frame.function=null; frame.argument=null; frame.completed=true; return;
        }
        throw error("Invalid non-MVar App continuation");
    }
    private void enterDirectBetaChild(RuntimeAction parent,ExprDirectSession session,DirectAppBetaFrame frame) {
        require(runtimeAction==parent&&frame.stage==3&&objects[parent.slot]==null&&session.call==null&&session.constructorCall==null
                &&session.levels.call==null&&session.levels.retiring==null&&session.retiring==null,"Direct beta parent is not ready");
        require(frame.betaParameter!=null&&frame.betaParameter.owned,"Direct beta parameter owner missing");
        for(int role=0;role<9;role++) exprConstructor(session.policy.constructors,role);
        RuntimeAction child=newAction(ACTION_EXPR_MACHINERY,null,ACTION_BODY,parent.slot,ASSIGN,null);
        ExprMachineryState worker=new ExprMachineryState(); worker.policy=session.policy.constructors; worker.budget=session.budget;
        BetaJob beta=new BetaJob(); beta.function=frame.betaParameter; beta.reverseArgs=new Object[frame.arguments.size()];
        for(int i=0;i<beta.reverseArgs.length;i++) { require(frame.arguments.get(i).owned,"Direct reverse argument owner missing"); beta.reverseArgs[i]=frame.arguments.get(i).value; }
        worker.jobs.addLast(beta); child.exprMachinery=worker; objects[child.slot]=null;
        publishAction(child); frame.betaParameter=null;
    }
    private void stepDirectAppBeta(RuntimeAction action,ExprDirectSession session,DirectAppBetaFrame frame) {
        if(frame.stage==0) {
            Node cursor=exprNode(frame.cursor);
            if(cursor.tag==5) { frame.stage=1; pushDirect(session,new DirectVisitFrame(exprNode(cursor.fields[1]))); return; }
            require(frame.functionOptional!=null&&frame.functionOptional.owned,"Assigned optional function owner missing");
            frame.betaParameter=exprCredit(frame.functionOptional.value); acquireExpr(frame.betaParameter);
            frame.stage=3; enterDirectBetaChild(action,session,frame); return;
        }
        if(frame.stage==1) {
            frame.argumentTemporary=takeDirectExprChild(frame,DirectVisitFrame.class);
            require(frame.arguments.size()<MAX_DIRECT_ARGUMENTS,"Direct Expr argument buffer limit");
            ExprCredit entry=exprCredit(frame.argumentTemporary.value); frame.arguments.add(entry); acquireExpr(entry);
            frame.stage=2; releaseDirect(action,session,frame.argumentTemporary); return;
        }
        if(frame.stage==2) { frame.argumentTemporary=null; frame.cursor=exprNode(frame.cursor).fields[0]; frame.stage=0; return; }
        if(frame.stage==3) {
            Object result=objects[action.slot]; exprNode(result); frame.result=new ExprCredit(result,true); objects[action.slot]=null;
            frame.stage=4; frame.cleanup=0;
        }
        if(frame.stage==4) {
            // runtime::buffer destroys forward, including its outermost-first args.
            if(frame.cleanup<frame.arguments.size()) { ExprCredit entry=frame.arguments.get(frame.cleanup++); releaseDirect(action,session,entry); return; }
            frame.stage=5; releaseDirect(action,session,frame.functionOptional); return;
        }
        require(frame.stage==5,"Invalid assigned App beta continuation"); frame.arguments.clear(); frame.functionOptional=null; frame.completed=true;
    }
    private void stepDirectLevel(RuntimeAction action,ExprDirectSession session,DirectLevelFrame frame) {
        if(frame.stage==0) { requireDirectReceiverFree(action,session); startLevelJob(session.levels,frame.input); frame.stage=1; return; }
        stepLevelJob(action,session.levels);
        if(session.levels.phase==LS_RESULT) { frame.levelResult=takeLevelJobResult(session.levels); frame.completed=true; }
    }
    private ExprCredit buildDirectCons(ExprDirectSession session,DirectLevelsFrame frame,Object head,Object tail) {
        directWork(session,1); require(frame.consCredit==null,"Direct list cons escrow occupied");
        Node cons=new Node(1,2,0); frame.building=cons; frame.consCredit=new ExprCredit(cons,true); frame.builtFields=0; allocations++;
        frame.headLoan=new LevelCredit(head,false); ownLevelCredit(frame.headLoan);
        cons.fields[0]=head; frame.headLoan.owned=false; frame.builtFields=1;
        frame.tailLoan=exprCredit(tail); acquireExpr(frame.tailLoan);
        cons.fields[1]=tail; frame.tailLoan.owned=false; frame.builtFields=2;
        ExprCredit result=frame.consCredit; frame.consCredit=null; frame.building=null; frame.headLoan=null; frame.tailLoan=null; return result;
    }
    private void stepDirectLevels(RuntimeAction action,ExprDirectSession session,DirectLevelsFrame frame) {
        if(frame.stage==0) {
            if(frame.cursor==null) frame.cursor=frame.original;
            if(ERASED.equals(frame.cursor)) { frame.index=frame.cells.size()-1; frame.stage=1; return; }
            Node cell=constructorNode(frame.cursor);
            require(cell.tag==1&&cell.fields.length==2&&cell.scalars.length==0,"Invalid Const Level list layout");
            require(frame.cells.size()<MAX_DIRECT_LEVELS,"Direct Const Level list length/cycle outside profile");
            levelNode(cell.fields[0]); frame.cells.add(cell); frame.cursor=cell.fields[1]; return;
        }
        if(frame.stage==1) {
            if(frame.index<0) {
                if(frame.list==null) directSelect(frame,frame.original);
                else { frame.result=frame.list; frame.list=null; }
                frame.stage=8; releaseLevelCredit(action,session.levels,frame.firstChanged); return;
            }
            frame.stage=2; pushDirect(session,new DirectLevelFrame(frame.cells.get(frame.index).fields[0])); return;
        }
        if(frame.stage==2) {
            DirectLevelFrame child=(DirectLevelFrame)takeDirectChild(frame,DirectLevelFrame.class);
            require(child.levelResult!=null&&child.levelResult.owned,"Const Level result missing");
            frame.currentHead=child.levelResult; child.levelResult=null; frame.child=null;
            Node cell=frame.cells.get(frame.index);
            if(frame.list==null) {
                if(sameLevel(frame.currentHead.value,cell.fields[0])) {
                    frame.stage=3; releaseLevelCredit(action,session.levels,frame.currentHead); return;
                }
                frame.firstChanged=frame.currentHead; frame.currentHead=null;
                frame.list=buildDirectCons(session,frame,frame.firstChanged.value,cell.fields[1]);
                frame.index--; frame.stage=1; return;
            }
            frame.replacement=buildDirectCons(session,frame,frame.currentHead.value,frame.list.value);
            frame.stage=4; releaseDirect(action,session,frame.list); return;
        }
        if(frame.stage==3) { frame.currentHead=null; frame.index--; frame.stage=1; return; }
        if(frame.stage==4) {
            require(frame.replacement!=null&&frame.replacement.owned,"Const prefix replacement list missing");
            frame.list=frame.replacement; frame.replacement=null; frame.stage=5;
            releaseLevelCredit(action,session.levels,frame.currentHead); return;
        }
        if(frame.stage==5) { frame.currentHead=null; frame.index--; frame.stage=1; return; }
        require(frame.stage==8&&frame.result!=null&&frame.result.owned,"Invalid Const Level list completion");
        frame.firstChanged=null; frame.currentHead=null; frame.cells.clear(); frame.cursor=null; frame.original=null; frame.completed=true;
    }
    private void stepDirectVisit(RuntimeAction action,ExprDirectSession session,DirectVisitFrame frame) {
        Node original=frame.original;
        if(frame.stage==0) {
            if(!exprHasMVars(exprCachedData(original))) { directSelect(frame,original); frame.stage=91; return; }
            frame.shared=!exclusive(original);
            ExprCredit cached=frame.shared?session.cache.get(original):null;
            if(cached!=null) { require(cached.owned,"Direct Expr cache owner missing"); directSelect(frame,cached.value); frame.shared=false; frame.stage=91; return; }
            switch(original.tag) {
                case 2: frame.shared=false; frame.stage=10; pushDirect(session,new DirectMVarFrame(original)); return;
                case 3: frame.stage=11; pushDirect(session,new DirectLevelFrame(original.fields[0])); return;
                case 4: frame.stage=12; pushDirect(session,new DirectLevelsFrame(original.fields[1])); return;
                case 5: frame.stage=10; pushDirect(session,new DirectAppFrame(original)); return;
                case 6: case 7: case 8: case 10: case 11: frame.stage=1; break;
                default: throw error("Inconsistent cached mvars on atomic Expr outside profile");
            }
        }
        if(frame.stage==1) {
            if(frame.child!=null) {
                require(frame.cursor<frame.children.length,"Direct Expr child cursor exceeds profile layout");
                frame.children[frame.cursor]=takeDirectExprChild(frame,DirectVisitFrame.class); frame.cursor++;
            }
            int count=exprChildCount(original.tag);
            if(frame.cursor<count) { pushDirect(session,new DirectVisitFrame(exprNode(original.fields[exprChildField(original.tag,frame.cursor)]))); return; }
            Object[] values=original.fields.clone(); boolean changed=false;
            for(int i=0;i<count;i++) {
                require(frame.children[i]!=null&&frame.children[i].owned,"Direct Expr child result missing");
                int at=exprChildField(original.tag,i); values[at]=frame.children[i].value; changed|=values[at]!=original.fields[at];
            }
            if(!changed) { directSelect(frame,original); frame.stage=90; }
            else {
                if(original.tag>=6&&original.tag<=8) { values=Arrays.copyOf(values,values.length+1); values[values.length-1]=Long.valueOf(original.scalars[8]&255); }
                frame.stage=3; callDirectConstructor(action,session,frame,exprCtorRole(original.tag),values); return;
            }
        }
        if(frame.stage==3) {
            require(frame.received!=null&&frame.received.owned,"Direct Expr constructor result missing"); frame.result=frame.received; frame.received=null; frame.stage=90;
        }
        if(frame.stage==10) { frame.result=takeDirectExprChild(frame,original.tag==2?DirectMVarFrame.class:DirectAppFrame.class); frame.stage=90; }
        if(frame.stage==11) {
            DirectLevelFrame child=(DirectLevelFrame)takeDirectChild(frame,DirectLevelFrame.class);
            require(child.levelResult!=null&&child.levelResult.owned,"Sort Level result missing"); frame.level=child.levelResult; child.levelResult=null; frame.child=null;
            if(sameLevel(frame.level.value,original.fields[0])) { directSelect(frame,original); frame.stage=90; }
            else { frame.stage=3; callDirectConstructor(action,session,frame,1,new Object[]{frame.level.value}); return; }
        }
        if(frame.stage==12) {
            frame.levels=takeDirectExprChild(frame,DirectLevelsFrame.class);
            if(sameExprField(frame.levels.value,original.fields[1])) { directSelect(frame,original); frame.stage=90; }
            else { frame.stage=3; callDirectConstructor(action,session,frame,2,new Object[]{original.fields[0],frame.levels.value}); return; }
        }
        if(frame.stage==90) {
            require(frame.result!=null&&frame.result.owned,"Direct Expr computed result missing"); frame.stage=91;
            if(frame.shared) {
                // Reentrant assignment normalization may already have inserted
                // this key: native insert keeps the first value, returns our r.
                ExprCredit copy=exprCredit(frame.result.value);
                if(session.cache.containsKey(original)) {
                    frame.cacheTemporary=copy; acquireExpr(copy); releaseDirect(action,session,copy); return;
                }
                require(session.cacheValues.size()<MAX_DIRECT_CACHE,"Direct Expr cache limit");
                session.cacheValues.add(copy); session.cache.put(original,copy); acquireExpr(copy);
            }
        }
        require(frame.stage==91,"Invalid direct Expr visit continuation");
        if(frame.cleanup<5) {
            int at=frame.cleanup++;
            if(at<3) releaseDirect(action,session,frame.children[2-at]);
            else if(at==3) releaseLevelCredit(action,session.levels,frame.level);
            else releaseDirect(action,session,frame.levels);
            return;
        }
        Arrays.fill(frame.children,null); frame.level=null; frame.levels=null; frame.cacheTemporary=null; frame.completed=true;
    }
    private void stepExprDirectJob(RuntimeAction action,ExprDirectSession session) {
        require(session.phase==DS_RUNNING,"Direct Expr session has no running job"); directWork(session,1); resumeDirectRetiring(action,session);
        int packets=(session.call==null?0:1)+(session.constructorCall==null?0:1)+(session.levels.call==null?0:1);
        require(packets<=1,"Multiple outstanding direct/constructor/Level packets");
        if(session.call!=null) { receiveDirectHelper(action,session); return; }
        if(session.constructorCall!=null) { receiveDirectConstructor(action,session); return; }
        ExprDirectTask task=session.tasks.peekLast(); require(task!=null,"Missing direct Expr task");
        if(!task.completed) {
            if(task instanceof DirectVisitFrame) stepDirectVisit(action,session,(DirectVisitFrame)task);
            else if(task instanceof DirectAssignmentFrame) stepDirectAssignment(action,session,(DirectAssignmentFrame)task);
            else if(task instanceof DirectDelayedFrame) stepDirectDelayed(action,session,(DirectDelayedFrame)task);
            else if(task instanceof DirectMVarFrame) stepDirectMVar(action,session,(DirectMVarFrame)task);
            else if(task instanceof DirectAppFrame) stepDirectApp(action,session,(DirectAppFrame)task);
            else if(task instanceof DirectNonMvarAppFrame) stepDirectNonMvarApp(action,session,(DirectNonMvarAppFrame)task);
            else if(task instanceof DirectAppBetaFrame) stepDirectAppBeta(action,session,(DirectAppBetaFrame)task);
            else if(task instanceof DirectLevelFrame) stepDirectLevel(action,session,(DirectLevelFrame)task);
            else stepDirectLevels(action,session,(DirectLevelsFrame)task);
            return;
        }
        Iterator<ExprDirectTask> ancestors=session.tasks.descendingIterator(); ancestors.next();
        ExprDirectTask parent=ancestors.hasNext()?ancestors.next():null;
        if(parent==null) {
            require(task instanceof DirectVisitFrame&&task.result!=null&&task.result.owned&&session.result==null
                    &&session.context.current!=null&&session.context.current.owned&&session.levels.phase==LS_IDLE,
                    "Direct root completion ownership differs");
            session.result=task.result; task.result=null; session.phase=DS_RESULT;
        } else { require(parent.child==null,"Direct Expr child receiver occupied"); parent.child=task; }
        session.tasks.removeLast();
    }
    private ExprCredit takeExprDirectResult(ExprDirectSession session) {
        require(session.phase==DS_RESULT&&session.tasks.isEmpty()&&session.result!=null&&session.result.owned
                &&session.call==null&&session.constructorCall==null&&session.retiring==null&&session.levels.retiring==null,
                "Direct Expr result is not ready");
        ExprCredit result=session.result; session.result=null; session.phase=DS_IDLE; return result;
    }
    private void sealExprDirectSession(ExprDirectSession session) {
        require(session.phase==DS_IDLE&&session.result==null&&session.tasks.isEmpty()&&session.call==null
                &&session.constructorCall==null&&session.retiring==null&&session.levels.retiring==null,
                "Direct Expr session is not idle with result taken");
        sealLevelSession(session.levels); session.cache.clear(); session.phase=DS_SEALED;
    }
    private void stepExprDirectDrain(RuntimeAction action,ExprDirectSession session) {
        require(session.phase==DS_SEALED||session.phase==DS_DRAINING,"Direct Expr session is not sealed for drain");
        directWork(session,1); resumeDirectRetiring(action,session); session.phase=DS_DRAINING;
        if(session.drainStage<3) {
            int size=session.drainStage==0?session.saved.size():session.drainStage==1?session.cacheValues.size():session.nameOwners.size();
            if(session.drainStage==2) session.normalized.clear();
            if(session.drainCursor<size) {
                int at=size-1-session.drainCursor++;
                ExprCredit credit=session.drainStage==0?session.saved.get(at):session.drainStage==1?session.cacheValues.get(at):session.nameOwners.get(at).name;
                releaseDirect(action,session,credit); return;
            }
            session.drainStage++; session.drainCursor=0; return;
        }
        stepLevelSessionDrain(action,session.levels);
        if(session.levels.phase!=LS_DRAINED) return;
        session.saved.clear(); session.cacheValues.clear(); session.nameOwners.clear(); session.normalized.clear(); session.phase=DS_DRAINED;
    }
    private void stepExprDirectResearch(RuntimeAction action) {
        ExprDirectResearchState state=action.exprDirect; require(state!=null,"Missing private direct Expr state");
        ExprDirectSession session=state.session;
        if(state.stage==0) {
            stepExprDirectJob(action,session);
            if(session.phase==DS_RESULT) { state.e1=takeExprDirectResult(session); sealExprDirectSession(session); state.stage=1; }
            return;
        }
        if(state.stage==4) { stepExprDirectDrain(action,session); if(session.phase!=DS_DRAINED) return; state.stage=5; }
        else { directWork(session,1); resumeDirectRetiring(action,session); }
        if(state.stage==1) { state.stage=2; releaseDirect(action,session,state.input); return; }
        if(state.stage==2) {
            require(state.e1!=null&&state.e1.owned&&state.context.current!=null&&state.context.current.owned&&session.phase==DS_SEALED,
                    "Private direct report inputs missing");
            Node report=new Node(0,3,0); state.output=new ExprCredit(report,true); allocations++;
            report.fields[0]=state.context.current.value; state.context.current.owned=false; state.context.current=null; state.outputFields=1;
            state.reportExprLoan=exprCredit(state.e1.value); acquireExpr(state.reportExprLoan);
            report.fields[1]=state.reportExprLoan.value; state.reportExprLoan.owned=false; state.outputFields=2;
            report.fields[2]=session.hasUpdateableDelayed?Long.valueOf(1):ERASED; state.outputFields=3;
            state.stage=3; return;
        }
        if(state.stage==3) { state.stage=4; releaseDirect(action,session,state.e1); return; }
        require(state.stage==5&&session.phase==DS_DRAINED&&state.output!=null&&state.output.owned&&state.outputFields==3
                &&state.context.current==null,"Private direct report is incomplete");
        Object output=state.output.value; state.output.owned=false; action.output=output;
        state.input=null; state.e1=null; state.output=null; state.reportExprLoan=null; state.context=null; state.budget=null; state.session=null;
        action.exprDirect=null; finishAction(action,output);
    }


    /* Stage four: private protocol/analysis foundation only. No Expr native
     * registration, full delayed transformation, or new source authority. */
    private static final boolean DELAYED_FOUNDATION_RESEARCH_READY=true;
    private static final int DELAYED_CACHE_PROTOCOL=0,DELAYED_RESOLVER_PROTOCOL=1,DELAYED_SUBSTITUTION_PROTOCOL=2;
    private static final int DC_PUSH=0,DC_POP=1,DC_LOOKUP=2,DC_INSERT=3,DC_ANALYZE=4,DC_INSTALL=5,DC_RESTORE=6,DC_SUBST_LOOKUP=7;
    private static final int MAX_DELAYED_KEYS=100_000,MAX_DELAYED_ENTRIES=100_000,MAX_DELAYED_GENERATIONS=100_000;
    private static final int MAX_DELAYED_FRAMES=100_000,MAX_DELAYED_NAMES=100_000,MAX_DELAYED_COMMANDS=100_000;
    private static final int PENDING_IN_PROGRESS=0,PENDING_YES=1,PENDING_NO=2;
    private static final int DELAYED_IDLE=0,DELAYED_RUNNING=1,DELAYED_RESULT=2,DELAYED_SEALED=3,DELAYED_DRAINED=4;
    /** Immutable and guest-reference-free. Fork may share these chains. */
    private static final class ScopeGeneration {
        final int serial; final ScopeGeneration parent;
        ScopeGeneration(int serial,ScopeGeneration parent) { this.serial=serial; this.parent=parent; }
    }
    /** A data-only command: no guest Function, body, capability, or resource. */
    private static final class DelayedCommand {
        final int operation,key,depth,value,resultScope;
        DelayedCommand(int operation,int key,int depth,int value,int resultScope) {
            this.operation=operation; this.key=key; this.depth=depth; this.value=value; this.resultScope=resultScope;
        }
    }
    private static final class ScopedEntry {
        ExprCredit result; ScopeGeneration generation;
        int validLevel,resultScope; boolean reserved;
    }
    private static final class ScopedBucket {
        Node key; int depth; final ArrayList<ScopedEntry> entries=new ArrayList<>();
    }
    private static final class ScopedExprCache {
        final IdentityHashMap<Node,HashMap<Integer,ScopedBucket>> index=new IdentityHashMap<>();
        final ArrayList<ScopedBucket> buckets=new ArrayList<>();
        ScopeGeneration current=new ScopeGeneration(0,null);
        int scope,generationCounter,generationCount=1,liveEntries;
        boolean sealed; int drainBucket,drainEntry; ScopedEntry retiringEntry;
    }
    /** computed aliases its caller's one owner flag; it is NOT another credit.
     * optional/shared/returned and retiringEntry each represent literal copies
     * or moved occurrences with distinct, resumable disposition. */
    private static final class ScopedCacheOperation {
        ScopedBucket bucket; ScopedEntry top,retiringEntry,newEntry;
        ScopeGeneration currentCursor,entryCursor;
        ExprCredit computed,shared,optional,returned,replacement;
        Node key; int kind,depth,resultScope,stage,walkLevel,rewindStage; boolean hit,completed,rewound;
    }
    private static final class PendingNameEntry {
        ExprCredit name; int hash,state;
    }
    private static final class SubstitutionEntry {
        ExprCredit name,value; int hash,depth,scope; boolean live;
    }
    private static final class SavedSubstitution {
        ExprCredit name,oldValue; int oldDepth,oldScope; boolean hadOld;
    }
    /** Shared production maintenance frame. saved records own independent old
     * copies and survive restoration; oldValue drains before its Name key. */
    private static final class SubstitutionFrame {
        Object fvars,sourceArguments; final ArrayList<ExprCredit> arguments=new ArrayList<>();
        final ArrayList<SavedSubstitution> saved=new ArrayList<>();
        SubstitutionEntry existing,replacement; ExprCredit newName,newValue,retiringName,retiringValue;
        int depth,index,stage,cleanup; boolean scopePushed,restored,completed,ownsArguments,erasing;
    }
    /** Lookup/lift borrows the map entry value; a nested existing ReplaceJob
     * has no root input credit and must not INC merely to start the lift. */
    private static final class SubstitutionLookup {
        Object name; SubstitutionEntry entry; ExprCredit optional,returned;
        int depth,stage; boolean present,completed;
    }
    private abstract static class ResolverTask {
        ResolverTask child; ExprCredit received; int stage,cursor,cleanup;
        boolean result,completed;
    }
    private static final class ResolvableExprFrame extends ResolverTask {
        Node original; boolean entryShared;
        ResolvableExprFrame(Node original) { this.original=original; }
    }
    private static final class ResolvablePendingFrame extends ResolverTask {
        Object name; PendingNameEntry entry; ExprCredit option,temporary;
        ResolvablePendingFrame(Object name) { this.name=name; }
    }
    private static final class ResolvableAppFrame extends ResolverTask {
        Node original; Object head,cursor; int argumentCount;
        ExprCredit option,recordTemporary,fvars,pendingName;
        ResolvableAppFrame(Node original) { this.original=original; }
    }
    private static final class DelayedHelperPacket {
        Function function; Object[] arguments; boolean[] owned;
        ResolverTask target; DelayedTransformTask transformTarget; int role; boolean started,entered;
    }
    private static final class DelayedSession {
        MVarContextCell context; InstantiationBudget budget; ExprInstantiationPolicy policy;
        ScopedExprCache cache=new ScopedExprCache();
        final IdentityHashMap<Node,Boolean> resolvableExpressions=new IdentityHashMap<>();
        final HashMap<Integer,ArrayList<PendingNameEntry>> pending=new HashMap<>();
        final ArrayList<PendingNameEntry> pendingOwners=new ArrayList<>();
        final ArrayList<ExprCredit> saved=new ArrayList<>();
        final HashMap<Integer,ArrayList<DirectNameEntry>> normalized=new HashMap<>();
        final ArrayList<DirectNameEntry> nameOwners=new ArrayList<>();
        final HashMap<Integer,ArrayList<SubstitutionEntry>> substitutions=new HashMap<>();
        final ArrayList<SubstitutionEntry> substitutionOwners=new ArrayList<>();
        final ArrayDeque<ResolverTask> resolver=new ArrayDeque<>();
        DelayedHelperPacket call; ExprPacket constructorCall;
        ScopedCacheOperation cacheOperation; SubstitutionFrame substitution; SubstitutionLookup lookup;
        final ArrayDeque<SubstitutionFrame> substitutionFrames=new ArrayDeque<>();
        ExprCredit retiring,result; int depth,resultScope,phase,drainStage,drainCursor;
        boolean booleanResult;
    }
    /** Anchors are OWNED only by this labeled protocol caller. Production
     * sessions/jobs borrow their source-backed roots; no giant retained visitor
     * history is introduced. Observation logs must contain primitives only. */
    private static final class DelayedResearchState {
        MVarContextCell context; InstantiationBudget budget; DelayedSession session;
        final ArrayList<ExprCredit> anchors=new ArrayList<>();
        DelayedCommand[] commands; ExprCredit lastResult,output,pendingInput; long lastObservation;
        int mode,commandCursor,stage,cleanup,outputFields;
        final ArrayList<Long> observations=new ArrayList<>();
    }
    /* Stage five: private complete transform scaffold. Native530 is RESERVED,
     * not registered. No operation can claim input while READY remains false. */
    private static final boolean EXPR_FULL_RESEARCH_READY=true;
    private static final boolean EXPR_INSTANTIATION_NATIVE_READY=true;
    private static final int DT_IDLE=0,DT_RUNNING=1,DT_RESULT=2,DT_SEALED=3,DT_DRAINED=4;
    private abstract static class DelayedTransformTask {
        DelayedTransformTask child;
        ExprCredit result,received;
        int stage,cleanup;
        boolean completed,helperDone;
    }
    /** NORMAL snapshots sharing and the caller watermark before child work.
     * Child occurrences stay owned until their literal case-block boundaries. */
    private static final class DelayedVisitFrame extends DelayedTransformTask {
        Node original;
        int entryDepth,savedWatermark,cursor;
        boolean shared,cacheHit,skipInsert;
        final ExprCredit[] children=new ExprCredit[3];
        DelayedVisitFrame(Node original) { this.original=original; }
    }
    private static final class DelayedFVarFrame extends DelayedTransformTask {
        Node original; Object name;
        DelayedFVarFrame(Node original) { this.original=original; }
    }
    /** A private optional result: present/result, never a fabricated guest Some. */
    private static final class DelayedAssignmentFrame extends DelayedTransformTask {
        Object name;
        ExprCredit option,assigned,newValue;
        boolean present,outer;
        DelayedAssignmentFrame(Object name) { this.name=name; }
    }
    private static final class DelayedAppFrame extends DelayedTransformTask {
        Node original; Object head,cursor;
        int argumentCount;
        ExprCredit option,recordTemporary,fvars,pendingName,discardedAssignment;
        DelayedAppFrame(Node original) { this.original=original; }
    }
    /** Prefix function Apps bypass NORMAL cache in both lookup and insertion. */
    private static final class DelayedPrefixFrame extends DelayedTransformTask {
        Node original;
        ExprCredit argument,function;
        DelayedPrefixFrame(Node original) { this.original=original; }
    }
    private static final class DelayedResolveFrame extends DelayedTransformTask {
        Node original;
        Object cursor,fvars,pendingName;
        final ArrayList<ExprCredit> arguments=new ArrayList<>();
        ExprCredit argumentTemporary,option,expressionTemporary,newValue,betaParameter;
        SubstitutionFrame substitutions;
        int argumentCount,extraCount;
        DelayedResolveFrame(Node original,Object fvars,Object pendingName) {
            this.original=original; this.fvars=fvars; this.pendingName=pendingName;
        }
    }
    /** This phase is independent of foundation.phase: the foundation may be
     * running its resolver/cache/substitution operation inside a live transform. */
    private static final class DelayedTransform {
        DelayedSession foundation;
        final ArrayDeque<DelayedTransformTask> tasks=new ArrayDeque<>();
        Object input;
        ExprCredit result;
        int phase;
    }
    /** One cell and budget span both passes. Direct members survive through
     * delayed work and pair construction; e1 and e2 are separate occurrences. */
    private static final class ExprFullResearchState {
        MVarContextCell context;
        InstantiationBudget budget;
        ExprDirectSession direct;
        DelayedTransform delayed;
        ExprCredit input,e1,e2,pair;
        int stage,pairFields;
    }
    /** Fixed private research entry; native530 remains unregistered. */
    private void startExprFullResearch(Header[] helpers,Header[] constructors,Object ownedContext,Object ownedExpr) {
        explicitOnly(); require(EXPR_FULL_RESEARCH_READY,"Private complete Expr transform is not yet enabled");
        require(taskRuntime!=null,"Complete Expr research requires active explicit runtime");
        if(closed||disposed||untrackedFailure||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||continuationDepth!=0
                ||runtimeAction!=null||hostCompletion!=null||hostGuestRecord!=null||quietCurrent!=null||releasePending!=0
                ||releaseTransaction!=null||releaseRoot) throw new IllegalStateException("Complete Expr research requires open idle engine");
        ExprInstantiationPolicy policy=ExprInstantiationPolicy.originalHelpers(levelInstantiationPolicy,helpers,constructors);
        for(int role=0;role<5;role++) { levelInstantiationHelper(policy.levels,role); exprInstantiationHelper(policy,role); }
        for(int role=0;role<9;role++) exprConstructor(policy.constructors,role);
        validateHostObject(ownedContext); Node root=exprNode(ownedExpr);
        if(ownedContext==ownedExpr) require(root.rc==0||root.rc>=2,"Complete Expr input owner aliases differ");
        RuntimeAction action=newAction(ACTION_EXPR_FULL_RESEARCH,null,null,0,ROOT,null);
        prepareExprFullAction(action,policy,ownedContext,root);
        objects[action.slot]=null; publishAction(action);
        callsLeft=10_000_000; instructions=0; entry=null; result=null; releaseRoot=false; phase=RUNNING;
    }
    private void prepareExprFullAction(RuntimeAction action,ExprInstantiationPolicy policy,Object ownedContext,Node root) {
        ExprFullResearchState state=new ExprFullResearchState(); action.exprFull=state;
        state.context=new MVarContextCell(); state.context.current=new LevelCredit(ownedContext,true); state.budget=new InstantiationBudget();
        state.input=new ExprCredit(root,true); ExprDirectSession direct=new ExprDirectSession(); state.direct=direct;
        direct.context=state.context; direct.budget=state.budget; direct.policy=policy;
        direct.levels=newLevelSession(state.context,state.budget,policy.levels);
        direct.tasks.addLast(new DirectVisitFrame(root)); direct.phase=DS_RUNNING;
        objects[action.slot]=null;
    }
    private ExprInstantiationPolicy exprInstantiationPolicy;
    /** One actual configured Level policy plus nineteen exact ordinary Headers.
     * Source acceptance remains the caller's trusted-loader obligation. */
    public void configureExprInstantiation(ExprInstantiationPolicy policy) {
        explicitOnly(); require(taskRuntime!=null&&policy!=null,"Expr instantiation requires active runtime and actual policy");
        if(closed||disposed||untrackedFailure||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||continuationDepth!=0
                ||runtimeAction!=null||hostCompletion!=null||hostGuestRecord!=null||quietCurrent!=null||releasePending!=0
                ||releaseTransaction!=null||releaseRoot) throw new IllegalStateException("Expr instantiation configuration requires open idle engine");
        require(exprInstantiationPolicy==null,"Expr instantiation policy already configured");
        require(policy.levels==levelInstantiationPolicy,"Expr policy must use actual configured Level policy");
        for(int role=0;role<5;role++) { levelInstantiationHelper(policy.levels,role); exprInstantiationHelper(policy,role); }
        for(int role=0;role<9;role++) exprConstructor(policy.constructors,role);
        exprInstantiationPolicy=policy;
    }
    private ExprInstantiationPolicy exprInstantiationProfile(Function function) {
        require(EXPR_INSTANTIATION_NATIVE_READY,"Full Expr native is not yet enabled");
        require(explicit&&taskRuntime!=null&&exprInstantiationPolicy!=null,"Expr instantiation requires active explicit runtime and configured original helpers");
        ExprInstantiationPolicy policy=exprInstantiationPolicy;
        require(policy.levels==levelInstantiationPolicy,"Expr/Level configured policy identity differs");
        Header origin=function.header;
        require(origin!=null&&origin.source==policy.helpers[0].source&&origin.kind.equals("extern")
                &&origin.originalSha256.equals("7e53092b477181a60a5e66f6cf2e2f33827b9f05411b294359b860431fc8a9ef"),
                "Expr instantiation native source Header differs");
        Object name=Arrays.asList("str",Arrays.asList("str",Arrays.asList("anonymous"),"Lean"),"instantiateExprMVarsImp");
        require(origin.exactName.equals(frozenName(name)),"Expr instantiation native typed Name differs");
        for(int role=0;role<5;role++) { levelInstantiationHelper(policy.levels,role); exprInstantiationHelper(policy,role); }
        for(int role=0;role<9;role++) exprConstructor(policy.constructors,role);
        return policy;
    }
    private void validateExprInstantiationArguments(Function function,Object[] args) {
        exprInstantiationProfile(function);
        require(args!=null&&args.length==2,"Expr instantiation native arity differs");
        validateHostObject(args[0]); Node root=exprNode(args[1]);
        if(args[0]==args[1]) require(root.rc==0||root.rc>=2,"Expr instantiation input alias credits differ");
    }
    private ExprDirectSession currentDirectSession(RuntimeAction action) {
        return action==null?null:action.exprDirect!=null?action.exprDirect.session:
                action.exprFull!=null&&(action.exprFull.stage==0||action.exprFull.stage>=5)?action.exprFull.direct:null;
    }
    private DelayedSession currentDelayedSession(RuntimeAction action) {
        return action==null?null:action.delayedResearch!=null?action.delayedResearch.session:
                action.exprFull!=null&&action.exprFull.delayed!=null&&action.exprFull.stage>=3&&action.exprFull.stage<=4
                        ?action.exprFull.delayed.foundation:null;
    }
    private boolean delayedOuterMode(DelayedSession session) { return session.substitutions.isEmpty(); }
    private boolean delayedNormalizedContains(DelayedSession session,Object name) {
        int hash=delayedNameHash(session,name); ArrayList<DirectNameEntry> bucket=session.normalized.get(hash);
        if(bucket!=null) for(DirectNameEntry entry:bucket) {
            delayedWork(session,1); require(entry.name.owned,"Delayed normalized Name owner missing");
            if(mvarNameEqual(session.budget,name,entry.name.value)) return true;
        }
        return false;
    }
    private void delayedNormalizedInsert(DelayedSession session,Object name) {
        int hash=delayedNameHash(session,name); ArrayList<DirectNameEntry> bucket=session.normalized.get(hash);
        if(bucket!=null) for(DirectNameEntry entry:bucket) {
            delayedWork(session,1); if(mvarNameEqual(session.budget,name,entry.name.value)) return;
        }
        require(session.nameOwners.size()<MAX_DELAYED_NAMES,"Delayed normalized Name bound");
        DirectNameEntry entry=new DirectNameEntry(hash,exprCredit(name)); session.nameOwners.add(entry);
        if(bucket==null) { bucket=new ArrayList<>(); session.normalized.put(hash,bucket); }
        bucket.add(entry); acquireExpr(entry.name);
    }
    private void pushTransform(DelayedTransform transform,DelayedTransformTask task) {
        require(transform.phase==DT_RUNNING&&transform.tasks.size()<MAX_DELAYED_FRAMES,"Delayed transform task bound");
        transform.tasks.addLast(task);
    }
    private ExprCredit takeTransformChild(DelayedTransformTask parent,Class<?> expected) {
        DelayedTransformTask child=parent.child;
        require(child!=null&&child.completed&&expected.isInstance(child)&&child.result!=null&&child.result.owned,
                "Delayed transform child receiver differs");
        ExprCredit result=child.result; child.result=null; parent.child=null; return result;
    }
    private DelayedAssignmentFrame takeTransformAssignment(DelayedTransformTask parent) {
        require(parent.child instanceof DelayedAssignmentFrame&&parent.child.completed,"Delayed optional assignment not ready");
        DelayedAssignmentFrame child=(DelayedAssignmentFrame)parent.child; parent.child=null;
        require(!child.present||child.result!=null&&child.result.owned,"Delayed private optional result owner missing"); return child;
    }
    private void transformSelect(DelayedTransformTask frame,Object value) { frame.result=exprCredit(value); acquireExpr(frame.result); }
    private void callTransformHelper(RuntimeAction action,DelayedSession session,DelayedTransformTask target,int role,Object name,Object record,ExprCredit newValue) {
        delayedWork(session,1); require(role>=0&&role<=4,"Delayed transform helper role differs"); requireDelayedReceiverFree(action,session);
        Function helper=exprInstantiationHelper(session.policy,role);
        DelayedHelperPacket packet=new DelayedHelperPacket(); packet.function=helper; packet.role=role; packet.transformTarget=target;
        packet.arguments=new Object[helper.params.length]; packet.owned=new boolean[packet.arguments.length];
        if(role==2||role==3) packet.arguments[0]=record;
        else {
            require(session.context.current!=null&&session.context.current.owned,"Delayed transform context absent");
            packet.arguments[0]=session.context.current.value; packet.arguments[1]=name; nameNode(name);
            if(role==4) { require(newValue!=null&&newValue.owned,"Delayed setter value absent"); packet.arguments[2]=newValue.value; exprNode(newValue.value); }
        }
        for(Object argument:packet.arguments) validateHostObject(argument);
        session.call=packet;
        for(int i=0;i<packet.arguments.length;i++) {
            if(role==4&&i==0) { packet.owned[i]=true; session.context.current.owned=false; session.context.current=null; }
            else { inc(packet.arguments[i],1); packet.owned[i]=true; }
        }
        IdentityHashMap<Node,Integer> known=new IdentityHashMap<>();
        for(Object argument:packet.arguments) if(argument instanceof Node) known.merge((Node)argument,1,Integer::sum);
        for(Map.Entry<Node,Integer> entry:known.entrySet()) require(entry.getKey().rc==0||entry.getKey().rc>=entry.getValue(),"Delayed helper owner aliases differ");
        packet.started=true; enterExplicit(helper,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Delayed transform helper did not publish frame/CodeRequest");
    }
    private void receiveTransformHelper(RuntimeAction action,DelayedSession session) {
        DelayedHelperPacket packet=session.call;
        require(packet!=null&&packet.entered&&packet.target==null&&packet.transformTarget!=null,"Delayed transform helper target differs");
        Object value=objects[action.slot]; DelayedTransformTask target=packet.transformTarget;
        if(packet.role==4) {
            validateHostObject(value); require(session.context.current==null,"Delayed setter replaces owned context");
            session.context.current=new LevelCredit(value,true); objects[action.slot]=null; target.helperDone=true;
        } else {
            require(target.received==null,"Delayed transform helper receiver occupied");
            if(packet.role<=1) validateDirectOption(value,packet.role==0);
            else if(packet.role==2) { Node array=pureExprArray(value); require(array.arraySize()<=MAX_DELAYED_NAMES,"Delayed fvars Array bound"); }
            else nameNode(value);
            target.received=new ExprCredit(value,true); objects[action.slot]=null;
        }
        session.call=null;
    }
    private void callTransformConstructor(RuntimeAction action,DelayedSession session,DelayedTransformTask target,int role,Object[] values) {
        delayedWork(session,1); requireDelayedReceiverFree(action,session);
        ExprPacket packet=prepareExprConstructorPacket(session.policy.constructors,role,values); packet.delayedTarget=target;
        session.constructorCall=packet; acquireExprConstructorPacket(packet); packet.started=true;
        enterExplicit(packet.function,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Delayed constructor did not publish frame/CodeRequest");
    }
    private void receiveTransformConstructor(RuntimeAction action,DelayedSession session) {
        ExprPacket packet=session.constructorCall;
        require(packet!=null&&packet.entered&&packet.delayedTarget!=null&&packet.delayedTarget.received==null,"Delayed constructor receiver differs");
        ExprCredit result=takeExprConstructorResult(action,packet); packet.delayedTarget.received=result; session.constructorCall=null;
    }
    private void stepTransformFVar(RuntimeAction action,DelayedTransform transform,DelayedFVarFrame frame) {
        DelayedSession session=transform.foundation;
        if(frame.stage==0) {
            require(session.lookup==null,"Delayed FVar lookup occupied"); SubstitutionLookup lookup=new SubstitutionLookup();
            lookup.name=frame.original.fields[0]; lookup.depth=session.depth; session.lookup=lookup; frame.stage=1; return;
        }
        SubstitutionLookup lookup=session.lookup; require(lookup!=null,"Delayed FVar lookup missing");
        stepSubstitutionLookup(action,session,lookup); if(!lookup.completed) return;
        if(lookup.present) { require(lookup.returned!=null&&lookup.returned.owned,"Delayed FVar returned owner absent"); frame.result=lookup.returned; lookup.returned=null; }
        else transformSelect(frame,frame.original);
        session.lookup=null; frame.completed=true;
    }
    private void stepTransformAssignment(RuntimeAction action,DelayedTransform transform,DelayedAssignmentFrame frame) {
        DelayedSession session=transform.foundation;
        if(frame.stage==0) { frame.stage=1; callTransformHelper(action,session,frame,0,frame.name,null,null); return; }
        if(frame.stage==1) {
            require(frame.received!=null&&frame.received.owned,"Delayed assignment Option absent"); frame.option=frame.received; frame.received=null;
            if(ERASED.equals(frame.option.value)) { frame.present=false; frame.stage=20; return; }
            frame.assigned=exprCredit(((Node)frame.option.value).fields[0]); acquireExpr(frame.assigned); frame.outer=delayedOuterMode(session);
            if(frame.outer&&delayedNormalizedContains(session,frame.name)) {
                transformSelect(frame,frame.assigned.value); frame.present=true; frame.stage=20; return;
            }
            if(frame.outer) delayedNormalizedInsert(session,frame.name);
            frame.stage=2; pushTransform(transform,new DelayedVisitFrame(exprNode(frame.assigned.value))); return;
        }
        if(frame.stage==2) {
            frame.newValue=takeTransformChild(frame,DelayedVisitFrame.class);
            if(frame.outer&&frame.newValue.value!=frame.assigned.value) {
                require(session.saved.size()<MAX_DIRECT_SAVED,"Delayed saved assignment bound");
                ExprCredit saved=exprCredit(frame.assigned.value); session.saved.add(saved); acquireExpr(saved);
                frame.stage=3; callTransformHelper(action,session,frame,4,frame.name,null,frame.newValue); return;
            }
            frame.stage=4;
        }
        if(frame.stage==3) { require(frame.helperDone,"Delayed setter completion absent"); frame.stage=4; }
        if(frame.stage==4) {
            if(frame.outer) transformSelect(frame,frame.newValue.value);
            else { frame.result=frame.newValue; frame.newValue=null; }
            frame.present=true; frame.stage=20;
        }
        if(frame.stage==20) { frame.stage=21; releaseDelayed(action,session,frame.newValue); return; }
        if(frame.stage==21) { frame.stage=22; releaseDelayed(action,session,frame.assigned); return; }
        if(frame.stage==22) { frame.stage=23; releaseDelayed(action,session,frame.option); return; }
        require(frame.stage==23,"Delayed assignment continuation differs");
        frame.newValue=null; frame.assigned=null; frame.option=null; frame.completed=true;
    }
    private void stepTransformPrefix(RuntimeAction action,DelayedTransform transform,DelayedPrefixFrame frame) {
        DelayedSession session=transform.foundation;
        if(frame.stage==0) { frame.stage=1; pushTransform(transform,new DelayedVisitFrame(exprNode(frame.original.fields[1]))); return; }
        if(frame.stage==1) {
            frame.argument=takeTransformChild(frame,DelayedVisitFrame.class); Node f=exprNode(frame.original.fields[0]); frame.stage=2;
            pushTransform(transform,f.tag==5?new DelayedPrefixFrame(f):new DelayedVisitFrame(f)); return;
        }
        if(frame.stage==2) {
            frame.function=takeTransformChild(frame,exprNode(frame.original.fields[0]).tag==5?DelayedPrefixFrame.class:DelayedVisitFrame.class);
            if(frame.function.value==frame.original.fields[0]&&frame.argument.value==frame.original.fields[1]) { transformSelect(frame,frame.original); frame.stage=4; }
            else { frame.stage=3; callTransformConstructor(action,session,frame,3,new Object[]{frame.function.value,frame.argument.value}); return; }
        }
        if(frame.stage==3) { require(frame.received!=null&&frame.received.owned,"Delayed App constructor result absent"); frame.result=frame.received; frame.received=null; frame.stage=4; }
        if(frame.stage==4) { frame.stage=5; releaseDelayed(action,session,frame.function); return; }
        if(frame.stage==5) { frame.stage=6; releaseDelayed(action,session,frame.argument); return; }
        require(frame.stage==6,"Delayed prefix continuation differs"); frame.function=null; frame.argument=null; frame.completed=true;
    }
    private void stepTransformApp(RuntimeAction action,DelayedTransform transform,DelayedAppFrame frame) {
        DelayedSession session=transform.foundation;
        if(frame.stage==0) {
            frame.head=frame.original; frame.argumentCount=0; frame.stage=1;
        }
        if(frame.stage==1) {
            Node head=exprNode(frame.head);
            if(head.tag==5) { require(frame.argumentCount<MAX_DIRECT_ARGUMENTS,"Delayed App spine bound"); frame.argumentCount++; frame.head=head.fields[0]; return; }
            if(head.tag!=2) { frame.stage=20; pushTransform(transform,new DelayedPrefixFrame(frame.original)); return; }
            frame.stage=2; callTransformHelper(action,session,frame,1,head.fields[0],null,null); return;
        }
        if(frame.stage==2) {
            require(frame.received!=null&&frame.received.owned,"Delayed App Option absent"); frame.option=frame.received; frame.received=null;
            if(ERASED.equals(frame.option.value)) { frame.stage=20; pushTransform(transform,new DelayedPrefixFrame(frame.original)); return; }
            frame.recordTemporary=exprCredit(((Node)frame.option.value).fields[0]); acquireExpr(frame.recordTemporary);
            frame.stage=3; callTransformHelper(action,session,frame,2,null,frame.recordTemporary.value,null); return;
        }
        if(frame.stage==3) {
            require(frame.received!=null&&frame.received.owned,"Delayed App fvars absent"); frame.fvars=frame.received; frame.received=null;
            frame.stage=4; releaseDelayed(action,session,frame.recordTemporary); return;
        }
        if(frame.stage==4) {
            frame.recordTemporary=exprCredit(((Node)frame.option.value).fields[0]); acquireExpr(frame.recordTemporary);
            frame.stage=5; callTransformHelper(action,session,frame,3,null,frame.recordTemporary.value,null); return;
        }
        if(frame.stage==5) {
            require(frame.received!=null&&frame.received.owned,"Delayed App pending Name absent"); frame.pendingName=frame.received; frame.received=null;
            frame.stage=6; releaseDelayed(action,session,frame.recordTemporary); return;
        }
        if(frame.stage==6) {
            frame.recordTemporary=null;
            if(((Node)frame.fvars.value).arraySize()>frame.argumentCount) { frame.stage=20; pushTransform(transform,new DelayedPrefixFrame(frame.original)); return; }
            require(session.phase==DELAYED_IDLE&&session.resolver.isEmpty(),"Delayed pending resolver occupied");
            session.phase=DELAYED_RUNNING; pushResolver(session,new ResolvablePendingFrame(frame.pendingName.value)); frame.stage=7; return;
        }
        if(frame.stage==7) {
            stepResolver(action,session); if(session.phase!=DELAYED_RESULT) return;
            if(takeResolverResult(session)) {
                frame.stage=21; pushTransform(transform,new DelayedResolveFrame(frame.original,frame.fvars.value,frame.pendingName.value)); return;
            }
            require(delayedOuterMode(session),"Unresolvable delayed App in inner mode outside source profile");
            frame.stage=8; pushTransform(transform,new DelayedAssignmentFrame(frame.pendingName.value)); return;
        }
        if(frame.stage==8) {
            DelayedAssignmentFrame assignment=takeTransformAssignment(frame); frame.discardedAssignment=assignment.result; assignment.result=null;
            frame.stage=9; releaseDelayed(action,session,frame.discardedAssignment); return;
        }
        if(frame.stage==9) { frame.discardedAssignment=null; frame.stage=20; pushTransform(transform,new DelayedPrefixFrame(frame.original)); return; }
        if(frame.stage==20||frame.stage==21) { frame.result=takeTransformChild(frame,frame.stage==20?DelayedPrefixFrame.class:DelayedResolveFrame.class); frame.stage=30; }
        if(frame.stage==30) { frame.stage=31; releaseDelayed(action,session,frame.pendingName); return; }
        if(frame.stage==31) { frame.stage=32; releaseDelayed(action,session,frame.fvars); return; }
        if(frame.stage==32) { frame.stage=33; releaseDelayed(action,session,frame.option); return; }
        require(frame.stage==33,"Delayed App continuation differs"); frame.pendingName=null; frame.fvars=null; frame.option=null; frame.completed=true;
    }
    private void enterTransformBeta(RuntimeAction parent,DelayedTransform transform,DelayedResolveFrame frame) {
        DelayedSession session=transform.foundation;
        require(runtimeAction==parent&&objects[parent.slot]==null&&session.call==null&&session.constructorCall==null&&session.retiring==null,
                "Delayed beta receiver occupied");
        require(frame.betaParameter!=null&&frame.betaParameter.owned,"Delayed beta parameter absent");
        for(int role=0;role<9;role++) exprConstructor(session.policy.constructors,role);
        RuntimeAction child=newAction(ACTION_EXPR_MACHINERY,null,ACTION_BODY,parent.slot,ASSIGN,null);
        ExprMachineryState worker=new ExprMachineryState(); worker.policy=session.policy.constructors; worker.budget=session.budget;
        BetaJob beta=new BetaJob(); beta.function=frame.betaParameter; beta.reverseArgs=new Object[frame.extraCount];
        for(int i=0;i<beta.reverseArgs.length;i++) {
            ExprCredit arg=frame.arguments.get(i); require(arg.owned,"Delayed beta reverse argument backing absent"); beta.reverseArgs[i]=arg.value;
        }
        worker.jobs.addLast(beta); child.exprMachinery=worker; objects[child.slot]=null;
        publishAction(child); frame.betaParameter=null;
    }
    private void stepTransformResolve(RuntimeAction action,DelayedTransform transform,DelayedResolveFrame frame) {
        DelayedSession session=transform.foundation;
        if(frame.stage==0) {
            if(frame.cursor==null) frame.cursor=frame.original;
            Node cursor=exprNode(frame.cursor);
            if(cursor.tag==5) { frame.stage=1; pushTransform(transform,new DelayedVisitFrame(exprNode(cursor.fields[1]))); return; }
            Node fvars=pureExprArray(frame.fvars); int n=fvars.arraySize();
            require(n<=frame.arguments.size(),"Delayed resolve argument arity differs"); frame.extraCount=frame.arguments.size()-n;
            require(session.substitution==null&&session.substitutionFrames.size()<MAX_DELAYED_FRAMES,"Delayed resolve substitution receiver occupied");
            SubstitutionFrame install=new SubstitutionFrame(); frame.substitutions=install;
            install.fvars=fvars; install.depth=session.depth; install.ownsArguments=false; install.arguments.addAll(frame.arguments);
            install.stage=SF_ENTER; session.substitution=install; frame.stage=3; return;
        }
        if(frame.stage==1) {
            frame.argumentTemporary=takeTransformChild(frame,DelayedVisitFrame.class);
            require(frame.arguments.size()<MAX_DIRECT_ARGUMENTS,"Delayed reverse argument buffer bound");
            ExprCredit copy=exprCredit(frame.argumentTemporary.value); frame.arguments.add(copy); acquireExpr(copy);
            frame.stage=2; releaseDelayed(action,session,frame.argumentTemporary); return;
        }
        if(frame.stage==2) { frame.argumentTemporary=null; frame.cursor=exprNode(frame.cursor).fields[0]; frame.stage=0; return; }
        if(frame.stage==3) {
            SubstitutionFrame install=frame.substitutions; require(session.substitution==install,"Delayed install current frame differs");
            stepSubstitutionInstall(action,session,install); if(!install.completed) return;
            session.substitution=null; session.substitutionFrames.addLast(install);
            frame.stage=4; callTransformHelper(action,session,frame,0,frame.pendingName,null,null); return;
        }
        if(frame.stage==4) {
            require(frame.received!=null&&frame.received.owned,"Delayed pending Option absent"); frame.option=frame.received; frame.received=null;
            require(!ERASED.equals(frame.option.value),"Resolvable pending assignment missing outside source profile");
            frame.expressionTemporary=exprCredit(((Node)frame.option.value).fields[0]); acquireExpr(frame.expressionTemporary);
            frame.stage=5; pushTransform(transform,new DelayedVisitFrame(exprNode(frame.expressionTemporary.value))); return;
        }
        if(frame.stage==5) {
            frame.newValue=takeTransformChild(frame,DelayedVisitFrame.class); frame.stage=6;
            releaseDelayed(action,session,frame.expressionTemporary); return;
        }
        if(frame.stage==6) {
            frame.expressionTemporary=null;
            require(session.substitution==null&&session.substitutionFrames.peekLast()==frame.substitutions,"Delayed scope restore order differs");
            session.substitution=frame.substitutions; beginSubstitutionRestore(session,frame.substitutions); frame.stage=7; return;
        }
        if(frame.stage==7) {
            stepSubstitutionRestore(action,session,frame.substitutions); if(!frame.substitutions.completed) return;
            session.substitution=null; require(session.substitutionFrames.removeLast()==frame.substitutions,"Delayed restored scope differs");
            frame.betaParameter=exprCredit(frame.newValue.value); acquireExpr(frame.betaParameter); frame.stage=8;
            enterTransformBeta(action,transform,frame); return;
        }
        if(frame.stage==8) {
            Object value=objects[action.slot]; exprNode(value); frame.result=new ExprCredit(value,true); objects[action.slot]=null;
            frame.stage=9; releaseDelayed(action,session,frame.newValue); return;
        }
        if(frame.stage==9) { frame.newValue=null; frame.stage=10; releaseDelayed(action,session,frame.option); return; }
        if(frame.stage==10) {
            frame.option=null; stepSubstitutionFrameDrain(action,session,frame.substitutions);
            if(!frame.substitutions.completed||frame.substitutions.stage!=SF_DRAINED) return;
            frame.substitutions=null; frame.cleanup=0; frame.stage=11; return;
        }
        if(frame.stage==11) {
            if(frame.cleanup<frame.arguments.size()) { ExprCredit arg=frame.arguments.get(frame.cleanup++); releaseDelayed(action,session,arg); return; }
            frame.arguments.clear(); frame.fvars=null; frame.pendingName=null; frame.cursor=null; frame.completed=true; return;
        }
        throw error("Delayed resolution continuation differs");
    }
    private void transformCompositeResult(RuntimeAction action,DelayedTransform transform,DelayedVisitFrame frame) {
        Node original=frame.original; Object[] values=original.fields.clone(); boolean changed=false;
        int count=exprChildCount(original.tag);
        for(int i=0;i<count;i++) {
            require(frame.children[i]!=null&&frame.children[i].owned,"Delayed composite child owner absent");
            int at=exprChildField(original.tag,i); values[at]=frame.children[i].value; changed|=values[at]!=original.fields[at];
        }
        if(!changed) { transformSelect(frame,original); frame.stage=30; return; }
        if(original.tag>=6&&original.tag<=8) { values=Arrays.copyOf(values,values.length+1); values[values.length-1]=Long.valueOf(original.scalars[8]&255); }
        frame.stage=21; callTransformConstructor(action,transform.foundation,frame,exprCtorRole(original.tag),values);
    }
    private void stepTransformVisit(RuntimeAction action,DelayedTransform transform,DelayedVisitFrame frame) {
        DelayedSession session=transform.foundation; Node original=frame.original;
        if(frame.stage==0) {
            frame.entryDepth=session.depth; long word=exprCachedData(original);
            if(((word&(1L<<40))==0||delayedOuterMode(session))&&(word&(1L<<41))==0) {
                transformSelect(frame,original); frame.stage=51; return;
            }
            frame.shared=!exclusive(original);
            if(frame.shared) { startScopedOperation(session,DC_LOOKUP,original,frame.entryDepth,null,0); frame.stage=1; return; }
            frame.stage=2;
        }
        if(frame.stage==1) {
            ScopedCacheOperation op=session.cacheOperation; require(op!=null,"Delayed lookup operation absent");
            stepScopedCache(action,session); if(!op.completed) return;
            session.cacheOperation=null;
            if(op.hit) { require(op.returned!=null&&op.returned.owned,"Delayed cache hit return absent"); frame.result=op.returned; op.returned=null; frame.cacheHit=true; frame.stage=51; return; }
            frame.stage=2;
        }
        if(frame.stage==2) {
            frame.savedWatermark=session.resultScope; session.resultScope=0;
            switch(original.tag) {
                case 1: frame.skipInsert=true; frame.stage=10; pushTransform(transform,new DelayedFVarFrame(original)); return;
                case 2:
                    require(delayedOuterMode(session),"Bare Expr MVar in inner mode outside source profile");
                    frame.skipInsert=true; transformSelect(frame,original); frame.stage=40; return;
                case 5: frame.stage=10; pushTransform(transform,new DelayedAppFrame(original)); return;
                case 6: case 7: case 8: case 10: case 11: frame.stage=20; break;
                default: throw error("Contradictory delayed Expr flags on atomic storage");
            }
        }
        if(frame.stage==10) {
            frame.result=takeTransformChild(frame,original.tag==1?DelayedFVarFrame.class:DelayedAppFrame.class); frame.stage=40;
        }
        if(frame.stage==20) {
            int count=exprChildCount(original.tag);
            if(frame.child!=null) {
                require(frame.cursor<count,"Delayed child cursor outside layout"); frame.children[frame.cursor]=takeTransformChild(frame,DelayedVisitFrame.class); frame.cursor++;
            }
            if(frame.cursor<count) {
                boolean body=original.tag>=6&&original.tag<=8&&frame.cursor==count-1;
                require(frame.entryDepth<MAX_EXPR_JOB_OFFSET||!body,"Delayed binder depth bound");
                session.depth=frame.entryDepth+(body?1:0);
                pushTransform(transform,new DelayedVisitFrame(exprNode(original.fields[exprChildField(original.tag,frame.cursor)]))); return;
            }
            session.depth=frame.entryDepth; transformCompositeResult(action,transform,frame); return;
        }
        if(frame.stage==21) {
            require(frame.received!=null&&frame.received.owned,"Delayed composite constructor return absent");
            frame.result=frame.received; frame.received=null; frame.stage=30;
        }
        if(frame.stage==30) {
            int count=exprChildCount(original.tag);
            if(frame.cleanup<count) { ExprCredit child=frame.children[count-1-frame.cleanup++]; releaseDelayed(action,session,child); return; }
            Arrays.fill(frame.children,null); frame.stage=40;
        }
        if(frame.stage==40) {
            require(session.depth==frame.entryDepth&&frame.result!=null&&frame.result.owned,"Delayed insertion depth/result differs");
            if(frame.shared&&!frame.skipInsert) {
                ExprCredit computed=frame.result;
                // The operation aliases this exact moved occurrence, not a new credit.
                startScopedOperation(session,DC_INSERT,original,frame.entryDepth,computed,session.resultScope); frame.result=null; frame.stage=41; return;
            }
            frame.stage=50;
        }
        if(frame.stage==41) {
            ScopedCacheOperation op=session.cacheOperation; require(op!=null,"Delayed insertion operation absent");
            stepScopedCache(action,session); if(!op.completed) return;
            require(op.returned!=null&&op.returned.owned,"Delayed insertion returned owner absent");
            frame.result=op.returned; op.returned=null; session.cacheOperation=null; frame.stage=50;
        }
        if(frame.stage==50) { session.resultScope=Math.max(frame.savedWatermark,session.resultScope); frame.stage=51; }
        require(frame.stage==51&&frame.result!=null&&frame.result.owned,"Delayed NORMAL result absent"); frame.completed=true;
    }
    private void stepDelayedTransform(RuntimeAction action,DelayedTransform transform) {
        DelayedSession session=transform.foundation; delayedWork(session,1); resumeDelayedRetiring(action,session);
        require(transform.phase==DT_RUNNING,"Delayed transform not running");
        if(session.call!=null&&session.call.transformTarget!=null) { receiveTransformHelper(action,session); return; }
        if(session.constructorCall!=null) { receiveTransformConstructor(action,session); return; }
        DelayedTransformTask task=transform.tasks.peekLast(); require(task!=null,"Delayed transform frame absent");
        if(!task.completed) {
            if(task instanceof DelayedVisitFrame) stepTransformVisit(action,transform,(DelayedVisitFrame)task);
            else if(task instanceof DelayedFVarFrame) stepTransformFVar(action,transform,(DelayedFVarFrame)task);
            else if(task instanceof DelayedAssignmentFrame) stepTransformAssignment(action,transform,(DelayedAssignmentFrame)task);
            else if(task instanceof DelayedAppFrame) stepTransformApp(action,transform,(DelayedAppFrame)task);
            else if(task instanceof DelayedPrefixFrame) stepTransformPrefix(action,transform,(DelayedPrefixFrame)task);
            else stepTransformResolve(action,transform,(DelayedResolveFrame)task);
            return;
        }
        Iterator<DelayedTransformTask> iterator=transform.tasks.descendingIterator(); iterator.next();
        DelayedTransformTask parent=iterator.hasNext()?iterator.next():null;
        if(parent==null) {
            require(task instanceof DelayedVisitFrame&&task.result!=null&&task.result.owned&&transform.result==null
                    &&session.context.current!=null&&session.context.current.owned&&session.phase==DELAYED_IDLE,
                    "Delayed transform root ownership differs");
            transform.result=task.result; task.result=null; transform.phase=DT_RESULT;
        } else { require(parent.child==null,"Delayed transform parent receiver occupied"); parent.child=task; }
        transform.tasks.removeLast();
    }
    private ExprCredit takeDelayedTransformResult(DelayedTransform transform) {
        require(transform.phase==DT_RESULT&&transform.tasks.isEmpty()&&transform.result!=null&&transform.result.owned,
                "Delayed transform result unavailable");
        ExprCredit result=transform.result; transform.result=null; transform.input=null; transform.phase=DT_IDLE; return result;
    }
    private void stepExprFullResearch(RuntimeAction action) {
        ExprFullResearchState state=action.exprFull; require(state!=null,"Complete Expr root state absent");
        ExprDirectSession direct=state.direct;
        if(state.stage==0) {
            stepExprDirectJob(action,direct);
            if(direct.phase==DS_RESULT) { state.e1=takeExprDirectResult(direct); sealExprDirectSession(direct); state.stage=1; }
            return;
        }
        if(state.stage==3) {
            stepDelayedTransform(action,state.delayed);
            if(state.delayed.phase!=DT_RESULT) return;
            state.e2=takeDelayedTransformResult(state.delayed); sealDelayedSession(state.delayed.foundation);
            state.delayed.phase=DT_SEALED; state.stage=4; return;
        }
        if(state.stage==4) {
            stepDelayedDrain(action,state.delayed.foundation);
            if(state.delayed.foundation.phase!=DELAYED_DRAINED) return;
            state.delayed.phase=DT_DRAINED; state.stage=5; return;
        }
        if(state.stage==7) { stepExprDirectDrain(action,direct); if(direct.phase!=DS_DRAINED) return; state.stage=8; }
        else { directWork(direct,1); resumeDirectRetiring(action,direct); }
        if(state.stage==1) { state.stage=2; releaseDirect(action,direct,state.input); return; }
        if(state.stage==2) {
            require(state.e1!=null&&state.e1.owned,"Complete Expr pass-one result absent");
            if(!direct.hasUpdateableDelayed) { state.e2=exprCredit(state.e1.value); acquireExpr(state.e2); state.stage=5; return; }
            DelayedTransform delayed=new DelayedTransform(); state.delayed=delayed;
            DelayedSession session=new DelayedSession(); delayed.foundation=session;
            session.context=state.context; session.budget=state.budget; session.policy=direct.policy; session.phase=DELAYED_IDLE;
            delayed.input=state.e1.value; delayed.phase=DT_RUNNING;
            pushTransform(delayed,new DelayedVisitFrame(exprNode(delayed.input))); state.stage=3; return;
        }
        if(state.stage==5) {
            require(state.context.current!=null&&state.context.current.owned&&state.e2!=null&&state.e2.owned
                    &&state.pair==null,"Complete Expr pair inputs absent");
            Node pair=new Node(0,2,0); state.pair=new ExprCredit(pair,true); allocations++;
            pair.fields[0]=state.context.current.value; state.context.current.owned=false; state.context.current=null; state.pairFields=1;
            pair.fields[1]=state.e2.value; state.e2.owned=false; state.pairFields=2; state.stage=6; return;
        }
        if(state.stage==6) { state.stage=7; releaseDirect(action,direct,state.e1); return; }
        require(state.stage==8&&direct.phase==DS_DRAINED&&state.pair!=null&&state.pair.owned&&state.pairFields==2
                &&state.context.current==null&&!state.input.owned&&!state.e1.owned&&!state.e2.owned,
                "Complete Expr root final ownership differs");
        Object output=state.pair.value; state.pair.owned=false; action.output=output;
        state.input=null; state.e1=null; state.e2=null; state.pair=null; state.context=null; state.budget=null; state.direct=null; state.delayed=null;
        action.exprFull=null; action.arguments=null; finishAction(action,output);
    }

    private void delayedWork(DelayedSession session,long amount) {
        instantiationWork(session.budget,amount,"Delayed Expr work outside bounded runtime profile","Delayed Expr interrupted");
    }
    private static void delayedAnchorIndex(Object[] anchors,int index) {
        require(index>=0&&index<anchors.length,"Delayed research anchor index outside profile");
    }
    private DelayedCommand[] delayedCommands(int mode,int[][] descriptions,Object[] anchors) {
        require(mode>=DELAYED_CACHE_PROTOCOL&&mode<=DELAYED_SUBSTITUTION_PROTOCOL,"Unknown delayed research protocol");
        require(descriptions!=null&&descriptions.length>0&&descriptions.length<=MAX_DELAYED_COMMANDS,"Delayed research command bound");
        DelayedCommand[] result=new DelayedCommand[descriptions.length]; int scope=0; long validationWork=0;
        for(int i=0;i<result.length;i++) {
            require(++validationWork<=MAX_INSTANTIATION_WORK,"Delayed research preflight work bound");
            int[] row=descriptions[i]; require(row!=null&&row.length>0,"Missing delayed research command");
            int op=row[0],key=-1,depth=0,value=-1,resultScope=0;
            if(mode==DELAYED_CACHE_PROTOCOL) {
                if(op==DC_PUSH) { require(row.length==1&&scope<MAX_DELAYED_GENERATIONS,"Invalid scope push command"); scope++; }
                else if(op==DC_POP) { require(row.length==1&&scope>0,"Invalid scope pop command"); scope--; }
                else {
                    require((op==DC_LOOKUP&&row.length==3)||(op==DC_INSERT&&row.length==5),"Invalid scoped cache command");
                    key=row[1]; depth=row[2]; delayedAnchorIndex(anchors,key); exprNode(anchors[key]);
                    if(op==DC_INSERT) {
                        value=row[3]; resultScope=row[4]; delayedAnchorIndex(anchors,value); exprNode(anchors[value]);
                        require(resultScope>=0&&resultScope<=MAX_DELAYED_GENERATIONS,"Invalid cache result-scope watermark");
                        // Literal duplicate restoration can yield resultScope > scope.
                    }
                }
            } else if(mode==DELAYED_RESOLVER_PROTOCOL) {
                require(op==DC_ANALYZE&&row.length==2,"Invalid resolvability command");
                key=row[1]; delayedAnchorIndex(anchors,key); exprNode(anchors[key]);
            } else {
                if(op==DC_INSTALL) {
                    require(row.length==4&&scope<MAX_DELAYED_GENERATIONS,"Invalid substitution install command");
                    key=row[1]; value=row[2]; depth=row[3]; delayedAnchorIndex(anchors,key); delayedAnchorIndex(anchors,value);
                    Node fvars=node(anchors[key]),arguments=node(anchors[value]);
                    require(fvars.array&&arguments.array,"Substitution research requires object Arrays");
                    int n=fvars.arraySize(),m=arguments.arraySize(); require(n<=MAX_DELAYED_NAMES&&m>=n&&m<=MAX_DELAYED_NAMES,"Substitution Array extent outside profile");
                    require(n+m<=MAX_INSTANTIATION_WORK-validationWork,"Delayed research preflight work bound"); validationWork+=n+m;
                    for(int j=0;j<n;j++) { Node fvar=exprNode(fvars.fields[j]); require(fvar.tag==1,"Delayed substitution element is not an FVar"); nameNode(fvar.fields[0]); }
                    for(int j=0;j<m;j++) exprNode(arguments.fields[j]); scope++;
                } else if(op==DC_RESTORE) { require(row.length==1&&scope>0,"Invalid substitution restoration command"); scope--; }
                else {
                    require(op==DC_SUBST_LOOKUP&&row.length==3,"Invalid substitution lookup command");
                    key=row[1]; depth=row[2]; delayedAnchorIndex(anchors,key); nameNode(anchors[key]);
                }
            }
            require(depth>=0&&depth<=MAX_EXPR_JOB_OFFSET,"Delayed research binder depth outside profile");
            result[i]=new DelayedCommand(op,key,depth,value,resultScope);
        }
        require(scope==0,"Delayed research protocol leaves an unbalanced scope"); return result;
    }
    /** Private fixed research protocols only; no native/public invocation API.
     * READY stays false until all typed operations and drains are reviewed. */
    private void startDelayedFoundationResearch(Header[] helpers,Header[] constructors,int mode,Object ownedContext,Object[] ownedAnchors,int[][] descriptions) {
        explicitOnly(); require(DELAYED_FOUNDATION_RESEARCH_READY,"Private delayed foundation is not yet complete");
        require(taskRuntime!=null,"Private delayed foundation requires active explicit runtime");
        if(closed||disposed||untrackedFailure||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||continuationDepth!=0
                ||runtimeAction!=null||hostCompletion!=null||hostGuestRecord!=null||quietCurrent!=null||releasePending!=0
                ||releaseTransaction!=null||releaseRoot) throw new IllegalStateException("Private delayed foundation requires an open idle engine");
        require(ownedAnchors!=null&&ownedAnchors.length<=MAX_DELAYED_KEYS,"Delayed research anchor bound");
        ExprInstantiationPolicy policy=ExprInstantiationPolicy.originalHelpers(levelInstantiationPolicy,helpers,constructors);
        for(int role=0;role<5;role++) { levelInstantiationHelper(policy.levels,role); exprInstantiationHelper(policy,role); }
        for(int role=0;role<9;role++) exprConstructor(policy.constructors,role);
        IdentityHashMap<Node,Integer> known=new IdentityHashMap<>(); validateHostObject(ownedContext);
        if(ownedContext instanceof Node) known.merge((Node)ownedContext,1,Integer::sum);
        for(Object anchor:ownedAnchors) { validateHostObject(anchor); if(anchor instanceof Node) known.merge((Node)anchor,1,Integer::sum); }
        DelayedCommand[] commands=delayedCommands(mode,descriptions,ownedAnchors);
        for(Map.Entry<Node,Integer> entry:known.entrySet()) require(entry.getKey().rc==0||entry.getKey().rc>=entry.getValue(),"Delayed research input alias credits differ");
        RuntimeAction action=newAction(ACTION_DELAYED_FOUNDATION_RESEARCH,null,null,0,ROOT,null);
        DelayedResearchState state=new DelayedResearchState(); state.context=new MVarContextCell(); state.context.current=new LevelCredit(ownedContext,true);
        state.budget=new InstantiationBudget(); state.session=new DelayedSession(); state.session.context=state.context;
        state.session.budget=state.budget; state.session.policy=policy; state.session.phase=DELAYED_IDLE;
        state.mode=mode; state.commands=commands; for(Object anchor:ownedAnchors) state.anchors.add(new ExprCredit(anchor,true));
        action.delayedResearch=state; objects[action.slot]=null; publishAction(action);
        callsLeft=10_000_000; instructions=0; entry=null; result=null; releaseRoot=false; phase=RUNNING;
    }
    private void requireDelayedReceiverFree(RuntimeAction action,DelayedSession session) {
        require(runtimeAction==action&&currentDelayedSession(action)==session
                &&session.call==null&&session.constructorCall==null&&objects[action.slot]==null,
                "Multiple outstanding delayed helper/constructor packets");
    }
    private void delayedHelperEntry(Function function,Object[] arguments) {
        RuntimeAction action=runtimeAction;
        DelayedSession session=currentDelayedSession(action);
        if(session==null) return;
        DelayedHelperPacket packet=session.call;
        if(packet==null||packet.entered||packet.function!=function||packet.arguments!=arguments) return;
        require(packet.started,"Delayed helper entered before packet publication");
        packet.entered=true; Arrays.fill(packet.owned,false);
    }
    private boolean releaseDelayed(RuntimeAction action,DelayedSession session,ExprCredit credit) {
        if(credit==null||!credit.owned) return false;
        require(session.retiring==null,"Two delayed retiring occurrences");
        session.retiring=credit; action.retiring=credit.value; action.releaseClaimed=false;
        boolean dispatch;
        try { dispatch=beginRelease(credit.value,1,ACTION_BODY); credit.owned=false; }
        finally { if(action.releaseClaimed) credit.owned=false; }
        if(!dispatch) { session.retiring=null; action.retiring=null; action.releaseClaimed=false; }
        return dispatch;
    }
    private void resumeDelayedRetiring(RuntimeAction action,DelayedSession session) {
        if(session.retiring!=null) {
            require(!session.retiring.owned,"Delayed retiring occurrence was not claimed");
            session.retiring=null; action.retiring=null; action.releaseClaimed=false;
        }
    }
    private boolean mvarNameEqual(InstantiationBudget budget,Object left,Object right) {
        ExprEquality comparison=new ExprEquality(false); comparison.work=budget.work;
        try { return nameEquals(left,right,comparison); }
        finally { budget.work=comparison.work; }
    }
    private int delayedNameHash(DelayedSession session,Object value) {
        delayedWork(session,1); Node name=nameNode(value); return (int)(name==null?1723:readScalar(name,0,U64));
    }
    private void scopedPush(DelayedSession session) {
        delayedWork(session,1); ScopedExprCache cache=session.cache;
        require(!cache.sealed&&cache.generationCount<MAX_DELAYED_GENERATIONS&&cache.scope<MAX_DELAYED_GENERATIONS
                &&cache.generationCounter<Integer.MAX_VALUE,"Scoped Expr generation bound");
        ScopeGeneration next=new ScopeGeneration(cache.generationCounter+1,cache.current);
        cache.current=next; cache.generationCounter++; cache.generationCount++; cache.scope++;
    }
    private void scopedPop(DelayedSession session) {
        delayedWork(session,1); ScopedExprCache cache=session.cache;
        require(!cache.sealed&&cache.scope>0&&cache.current!=null&&cache.current.parent!=null,"Scoped Expr pop outside active scope");
        cache.current=cache.current.parent; cache.scope--;
    }
    private ScopedBucket scopedBucket(DelayedSession session,Node key,int depth,boolean create) {
        delayedWork(session,1); ScopedExprCache cache=session.cache;
        require(!cache.sealed&&depth>=0&&depth<=MAX_EXPR_JOB_OFFSET,"Scoped Expr key outside profile");
        HashMap<Integer,ScopedBucket> depths=cache.index.get(key); ScopedBucket bucket=depths==null?null:depths.get(depth);
        if(bucket!=null||!create) return bucket;
        require(cache.buckets.size()<MAX_DELAYED_KEYS,"Scoped Expr (identity,depth) key bound");
        bucket=new ScopedBucket(); bucket.key=key; bucket.depth=depth; cache.buckets.add(bucket);
        if(depths==null) { depths=new HashMap<>(); cache.index.put(key,depths); }
        depths.put(depth,bucket); return bucket;
    }
    private void startScopedOperation(DelayedSession session,int kind,Object key,int depth,ExprCredit computed,int resultScope) {
        require(session.cacheOperation==null&&session.call==null&&session.constructorCall==null,"Scoped Expr operation already active");
        require(kind==DC_LOOKUP||kind==DC_INSERT,"Unknown scoped Expr operation");
        Node original=exprNode(key);
        if(kind==DC_INSERT) require(computed!=null&&computed.owned&&resultScope>=0&&resultScope<=MAX_DELAYED_GENERATIONS,
                "Scoped Expr computed/result-scope owner missing");
        ScopedCacheOperation op=new ScopedCacheOperation(); op.kind=kind; op.key=original; op.depth=depth;
        op.computed=computed; op.resultScope=resultScope; session.cacheOperation=op;
        op.bucket=scopedBucket(session,original,depth,kind==DC_INSERT);
    }
    private void finishScopedRetiring(DelayedSession session,ScopedCacheOperation op) {
        if(op.retiringEntry==null) return;
        ScopedEntry entry=op.retiringEntry;
        require(entry.result!=null&&!entry.result.owned,"Scoped Expr eviction owner not drained");
        if(entry.reserved) { require(session.cache.liveEntries>0,"Scoped Expr reservation underflow"); session.cache.liveEntries--; entry.reserved=false; }
        entry.result=null; op.retiringEntry=null;
    }
    private void dropScopedTop(RuntimeAction action,DelayedSession session,ScopedCacheOperation op) {
        require(op.retiringEntry==null&&op.bucket!=null&&!op.bucket.entries.isEmpty(),"Missing scoped eviction entry");
        op.retiringEntry=op.bucket.entries.remove(op.bucket.entries.size()-1); op.top=null; op.rewindStage=0;
        releaseDelayed(action,session,op.retiringEntry.result);
    }
    private void stepScopedRewind(RuntimeAction action,DelayedSession session,ScopedCacheOperation op) {
        ScopedExprCache cache=session.cache;
        if(op.bucket==null||op.bucket.entries.isEmpty()) { op.rewound=true; return; }
        if(op.rewindStage==0) {
            op.top=op.bucket.entries.get(op.bucket.entries.size()-1);
            if(op.top.resultScope>cache.scope) { dropScopedTop(action,session,op); return; }
            op.rewindStage=1; return;
        }
        ScopedEntry top=op.top; require(top!=null&&top.result!=null&&top.result.owned,"Scoped rewind top owner missing");
        if(op.rewindStage==1) {
            if(top.validLevel>cache.scope) {
                require(top.generation!=null&&top.generation.parent!=null,"Scoped degrade chain exhausted");
                top.generation=top.generation.parent; top.validLevel--; return;
            }
            op.currentCursor=cache.current; op.walkLevel=cache.scope; op.rewindStage=2; return;
        }
        if(op.rewindStage==2) {
            if(op.walkLevel>top.validLevel) { require(op.currentCursor!=null&&op.currentCursor.parent!=null,"Scoped current chain exhausted"); op.currentCursor=op.currentCursor.parent; op.walkLevel--; return; }
            require(top.generation!=null&&op.currentCursor!=null,"Scoped generation cursor missing");
            if(top.generation.serial==op.currentCursor.serial) { op.rewound=true; return; }
            op.entryCursor=top.generation; op.walkLevel=top.validLevel; op.rewindStage=3; return;
        }
        require(op.rewindStage==3,"Invalid scoped rewind stage");
        if(op.walkLevel>top.resultScope) {
            require(op.entryCursor.parent!=null&&op.currentCursor.parent!=null,"Scoped mismatch chain exhausted");
            op.entryCursor=op.entryCursor.parent; op.currentCursor=op.currentCursor.parent; op.walkLevel--;
            if(op.entryCursor.serial==op.currentCursor.serial) { top.validLevel=op.walkLevel; top.generation=op.entryCursor; op.rewound=true; }
            return;
        }
        dropScopedTop(action,session,op);
    }
    private void stepScopedCache(RuntimeAction action,DelayedSession session) {
        delayedWork(session,1); resumeDelayedRetiring(action,session);
        ScopedCacheOperation op=session.cacheOperation; require(op!=null&&!op.completed,"No running scoped Expr operation");
        finishScopedRetiring(session,op);
        if(op.stage==0) { stepScopedRewind(action,session,op); if(op.rewound) op.stage=1; return; }
        if(op.kind==DC_LOOKUP) {
            if(op.stage==1) {
                if(op.bucket==null||op.bucket.entries.isEmpty()) { op.completed=true; return; }
                ScopedEntry top=op.bucket.entries.get(op.bucket.entries.size()-1);
                if(top.validLevel!=session.cache.scope) { op.completed=true; return; }
                session.resultScope=Math.max(session.resultScope,top.resultScope);
                op.optional=exprCredit(top.result.value); acquireExpr(op.optional); op.hit=true; op.stage=2; return;
            }
            if(op.stage==2) { op.returned=exprCredit(op.optional.value); acquireExpr(op.returned); op.stage=3; return; }
            if(op.stage==3) { op.stage=4; releaseDelayed(action,session,op.optional); return; }
            require(op.stage==4,"Invalid scoped lookup completion"); op.optional=null; op.completed=true; return;
        }
        if(op.stage==1) {
            require(op.computed!=null&&op.computed.owned,"Scoped insertion computed owner missing");
            op.shared=exprCredit(op.computed.value); acquireExpr(op.shared); op.stage=10; return;
        }
        if(op.stage==10) {
            if(!op.bucket.entries.isEmpty()&&op.bucket.entries.get(op.bucket.entries.size()-1).resultScope==op.resultScope) {
                op.replacement=exprCredit(op.bucket.entries.get(op.bucket.entries.size()-1).result.value); acquireExpr(op.replacement); op.stage=11; return;
            }
            op.stage=13;
        }
        if(op.stage==11) { op.stage=12; releaseDelayed(action,session,op.shared); return; }
        if(op.stage==12) { op.shared=op.replacement; op.replacement=null; op.stage=13; }
        if(op.stage==13) {
            if(!op.bucket.entries.isEmpty()&&op.bucket.entries.get(op.bucket.entries.size()-1).validLevel>=op.resultScope) {
                dropScopedTop(action,session,op); return;
            }
            op.stage=14; return;
        }
        if(op.stage==14) {
            require(session.cache.liveEntries<MAX_DELAYED_ENTRIES,"Scoped Expr live-entry bound");
            ScopedEntry entry=new ScopedEntry(); op.newEntry=entry; entry.result=op.shared; op.shared=null;
            entry.validLevel=session.cache.scope; entry.resultScope=op.resultScope; entry.generation=session.cache.current;
            entry.reserved=true; session.cache.liveEntries++; op.bucket.entries.add(entry); op.stage=15; return;
        }
        if(op.stage==15) { op.returned=exprCredit(op.newEntry.result.value); acquireExpr(op.returned); op.stage=16; return; }
        if(op.stage==16) { op.stage=17; releaseDelayed(action,session,op.computed); return; }
        require(op.stage==17&&op.returned!=null&&op.returned.owned,"Invalid scoped insert completion");
        op.computed=null; op.newEntry=null; op.completed=true;
    }

    private PendingNameEntry pendingEntry(DelayedSession session,Object name,boolean create) {
        int hash=delayedNameHash(session,name); ArrayList<PendingNameEntry> bucket=session.pending.get(hash);
        if(bucket!=null) for(PendingNameEntry entry:bucket) {
            delayedWork(session,1); require(entry.name!=null&&entry.name.owned,"Pending Name key owner missing");
            if(mvarNameEqual(session.budget,name,entry.name.value)) return entry;
        }
        if(!create) return null;
        require(session.pendingOwners.size()<MAX_DELAYED_NAMES,"Resolvable pending Name bound");
        PendingNameEntry entry=new PendingNameEntry(); entry.hash=hash; entry.state=PENDING_IN_PROGRESS; entry.name=exprCredit(name);
        session.pendingOwners.add(entry);
        if(bucket==null) { bucket=new ArrayList<>(); session.pending.put(hash,bucket); }
        bucket.add(entry); acquireExpr(entry.name); return entry;
    }
    private void pushResolver(DelayedSession session,ResolverTask frame) {
        require(session.phase==DELAYED_RUNNING&&session.resolver.size()<MAX_DELAYED_FRAMES,"Resolvable Expr frame bound"); session.resolver.addLast(frame);
    }
    private boolean takeResolverChild(ResolverTask parent,Class<?> expected) {
        ResolverTask child=parent.child;
        require(child!=null&&child.completed&&expected.isInstance(child),"Resolvable child kind/completion differs");
        boolean result=child.result; parent.child=null; return result;
    }
    private void callResolverHelper(RuntimeAction action,DelayedSession session,ResolverTask target,int role) {
        delayedWork(session,1); require(role>=0&&role<=3,"Resolver does not call assignment setter"); requireDelayedReceiverFree(action,session);
        Function helper=exprInstantiationHelper(session.policy,role); DelayedHelperPacket packet=new DelayedHelperPacket();
        packet.function=helper; packet.role=role; packet.target=target; packet.arguments=new Object[helper.params.length]; packet.owned=new boolean[packet.arguments.length];
        if(role<=1) {
            require(session.context.current!=null&&session.context.current.owned,"Resolvable context owner missing");
            packet.arguments[0]=session.context.current.value;
            packet.arguments[1]=role==0?((ResolvablePendingFrame)target).name:((Node)((ResolvableAppFrame)target).head).fields[0];
            nameNode(packet.arguments[1]);
        } else {
            ExprCredit record=((ResolvableAppFrame)target).recordTemporary;
            require(record!=null&&record.owned,"Resolvable accessor record temporary missing"); packet.arguments[0]=record.value;
        }
        for(Object argument:packet.arguments) validateHostObject(argument);
        session.call=packet;
        for(int i=0;i<packet.arguments.length;i++) { inc(packet.arguments[i],1); packet.owned[i]=true; }
        IdentityHashMap<Node,Integer> known=new IdentityHashMap<>();
        for(Object argument:packet.arguments) if(argument instanceof Node) known.merge((Node)argument,1,Integer::sum);
        for(Map.Entry<Node,Integer> entry:known.entrySet()) require(entry.getKey().rc==0||entry.getKey().rc>=entry.getValue(),"Resolvable helper alias credits differ");
        packet.started=true; enterExplicit(helper,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Resolvable helper did not publish frame/CodeRequest");
    }
    private void receiveResolverHelper(RuntimeAction action,DelayedSession session) {
        DelayedHelperPacket packet=session.call; require(packet!=null&&packet.entered,"Resolver helper returned before entry");
        require(packet.target.received==null,"Resolver helper receiver occupied"); Object value=objects[action.slot];
        if(packet.role<=1) validateDirectOption(value,packet.role==0);
        else if(packet.role==2) { Node array=node(value); require(array.array&&array.arraySize()<=MAX_DELAYED_NAMES,"Delayed fvars accessor requires bounded object Array"); }
        else nameNode(value);
        packet.target.received=new ExprCredit(value,true); objects[action.slot]=null; session.call=null;
    }
    private void stepResolvablePending(RuntimeAction action,DelayedSession session,ResolvablePendingFrame frame) {
        if(frame.stage==0) {
            frame.entry=pendingEntry(session,frame.name,false);
            if(frame.entry!=null) { frame.result=frame.entry.state==PENDING_YES; frame.completed=true; return; }
            frame.entry=pendingEntry(session,frame.name,true); frame.stage=1; callResolverHelper(action,session,frame,0); return;
        }
        if(frame.stage==1) {
            require(frame.received!=null&&frame.received.owned,"Resolvable pending Option missing"); frame.option=frame.received; frame.received=null;
            if(ERASED.equals(frame.option.value)) { frame.result=false; frame.stage=4; }
            else {
                frame.temporary=exprCredit(((Node)frame.option.value).fields[0]); acquireExpr(frame.temporary);
                frame.stage=2; pushResolver(session,new ResolvableExprFrame(exprNode(frame.temporary.value))); return;
            }
        }
        if(frame.stage==2) { frame.result=takeResolverChild(frame,ResolvableExprFrame.class); frame.stage=3; releaseDelayed(action,session,frame.temporary); return; }
        if(frame.stage==3) { frame.temporary=null; frame.stage=4; }
        if(frame.stage==4) { frame.entry.state=frame.result?PENDING_YES:PENDING_NO; frame.stage=5; releaseDelayed(action,session,frame.option); return; }
        require(frame.stage==5,"Invalid resolvable pending continuation"); frame.option=null; frame.completed=true;
    }
    private void stepResolvableApp(RuntimeAction action,DelayedSession session,ResolvableAppFrame frame) {
        if(frame.stage==0) {
            if(frame.head==null) frame.head=frame.original;
            Node head=exprNode(frame.head);
            if(head.tag==5) { frame.head=head.fields[0]; return; }
            if(head.tag!=2) { frame.stage=100; pushResolver(session,new ResolvableExprFrame(exprNode(frame.original.fields[0]))); return; }
            frame.stage=1; callResolverHelper(action,session,frame,1); return;
        }
        if(frame.stage==1) {
            require(frame.received!=null&&frame.received.owned,"Resolvable delayed Option missing"); frame.option=frame.received; frame.received=null;
            if(ERASED.equals(frame.option.value)) { frame.result=false; frame.stage=200; }
            else { frame.recordTemporary=exprCredit(((Node)frame.option.value).fields[0]); acquireExpr(frame.recordTemporary);
                frame.stage=2; callResolverHelper(action,session,frame,2); return; }
        }
        if(frame.stage==2) { require(frame.received!=null&&frame.received.owned,"Resolvable fvars Array missing"); frame.fvars=frame.received; frame.received=null;
            frame.stage=3; releaseDelayed(action,session,frame.recordTemporary); return; }
        if(frame.stage==3) { frame.recordTemporary=null; frame.cursor=frame.original; frame.argumentCount=0; frame.stage=4; }
        if(frame.stage==4) {
            Node current=exprNode(frame.cursor);
            if(current.tag==5) { require(frame.argumentCount<MAX_DIRECT_ARGUMENTS,"Resolvable application arity bound"); frame.argumentCount++; frame.cursor=current.fields[0]; return; }
            if(((Node)frame.fvars.value).arraySize()>frame.argumentCount) { frame.result=false; frame.stage=200; }
            else { frame.recordTemporary=exprCredit(((Node)frame.option.value).fields[0]); acquireExpr(frame.recordTemporary);
                frame.stage=5; callResolverHelper(action,session,frame,3); return; }
        }
        if(frame.stage==5) { require(frame.received!=null&&frame.received.owned,"Resolvable pending Name missing"); frame.pendingName=frame.received; frame.received=null;
            frame.stage=6; releaseDelayed(action,session,frame.recordTemporary); return; }
        if(frame.stage==6) { frame.recordTemporary=null; frame.stage=7; pushResolver(session,new ResolvablePendingFrame(frame.pendingName.value)); return; }
        if(frame.stage==7) {
            if(!takeResolverChild(frame,ResolvablePendingFrame.class)) { frame.result=false; frame.stage=200; }
            else { frame.cursor=frame.original; frame.stage=8; }
        }
        if(frame.stage==8) {
            Node current=exprNode(frame.cursor);
            if(current.tag!=5) { frame.result=true; frame.stage=200; }
            else { frame.stage=9; pushResolver(session,new ResolvableExprFrame(exprNode(current.fields[1]))); return; }
        }
        if(frame.stage==9) {
            if(!takeResolverChild(frame,ResolvableExprFrame.class)) { frame.result=false; frame.stage=200; }
            else { frame.cursor=exprNode(frame.cursor).fields[0]; frame.stage=8; return; }
        }
        if(frame.stage==100) {
            if(!takeResolverChild(frame,ResolvableExprFrame.class)) { frame.result=false; frame.completed=true; return; }
            frame.stage=101; pushResolver(session,new ResolvableExprFrame(exprNode(frame.original.fields[1]))); return;
        }
        if(frame.stage==101) { frame.result=takeResolverChild(frame,ResolvableExprFrame.class); frame.completed=true; return; }
        require(frame.stage==200,"Invalid resolvable App continuation");
        if(frame.cleanup<3) {
            ExprCredit credit=frame.cleanup==0?frame.pendingName:frame.cleanup==1?frame.fvars:frame.option;
            frame.cleanup++; releaseDelayed(action,session,credit); return;
        }
        frame.pendingName=null; frame.fvars=null; frame.option=null; require(frame.recordTemporary==null,"Resolvable D temporary not retired"); frame.completed=true;
    }
    private void stepResolvableExpr(RuntimeAction action,DelayedSession session,ResolvableExprFrame frame) {
        Node original=frame.original;
        if(frame.stage==0) {
            if((exprCachedData(original)&(1L<<41))==0) { frame.result=true; frame.completed=true; return; }
            frame.entryShared=!exclusive(original);
            Boolean cached=frame.entryShared?session.resolvableExpressions.get(original):null;
            if(cached!=null) { frame.result=cached; frame.completed=true; return; }
            if(original.tag==2) { frame.result=false; frame.stage=90; }
            else if(original.tag==5) { frame.stage=10; pushResolver(session,new ResolvableAppFrame(original)); return; }
            else if(original.tag==6||original.tag==7||original.tag==8||original.tag==10||original.tag==11) frame.stage=1;
            else { frame.result=true; frame.stage=90; }
        }
        if(frame.stage==1) {
            if(frame.child!=null) { if(!takeResolverChild(frame,ResolvableExprFrame.class)) { frame.result=false; frame.stage=90; } else frame.cursor++; }
            if(frame.stage==1) {
                if(frame.cursor<exprChildCount(original.tag)) { pushResolver(session,new ResolvableExprFrame(exprNode(original.fields[exprChildField(original.tag,frame.cursor)]))); return; }
                frame.result=true; frame.stage=90;
            }
        }
        if(frame.stage==10) { frame.result=takeResolverChild(frame,ResolvableAppFrame.class); frame.stage=90; }
        require(frame.stage==90,"Invalid resolvable Expr continuation");
        // Native samples sharing again after analysis, not only at entry.
        if(!exclusive(original)) {
            require(session.resolvableExpressions.containsKey(original)||session.resolvableExpressions.size()<MAX_DELAYED_KEYS,"Resolvable Expr key bound");
            session.resolvableExpressions.put(original,frame.result);
        }
        frame.completed=true;
    }
    private void startResolver(DelayedSession session,Object input) {
        require(session.phase==DELAYED_IDLE&&session.resolver.isEmpty()&&session.call==null&&session.constructorCall==null,"Resolvable session is not idle");
        Node root=exprNode(input); session.phase=DELAYED_RUNNING; pushResolver(session,new ResolvableExprFrame(root));
    }
    private void stepResolver(RuntimeAction action,DelayedSession session) {
        delayedWork(session,1); resumeDelayedRetiring(action,session);
        require(session.phase==DELAYED_RUNNING&&session.constructorCall==null,"No running resolver or unsupported delayed constructor packet");
        if(session.call!=null) { receiveResolverHelper(action,session); return; }
        ResolverTask frame=session.resolver.peekLast(); require(frame!=null,"Missing resolvability frame");
        if(!frame.completed) {
            if(frame instanceof ResolvableExprFrame) stepResolvableExpr(action,session,(ResolvableExprFrame)frame);
            else if(frame instanceof ResolvablePendingFrame) stepResolvablePending(action,session,(ResolvablePendingFrame)frame);
            else stepResolvableApp(action,session,(ResolvableAppFrame)frame);
            return;
        }
        Iterator<ResolverTask> ancestors=session.resolver.descendingIterator(); ancestors.next(); ResolverTask parent=ancestors.hasNext()?ancestors.next():null;
        if(parent==null) { session.booleanResult=frame.result; session.phase=DELAYED_RESULT; }
        else { require(parent.child==null,"Resolver parent receiver occupied"); parent.child=frame; }
        session.resolver.removeLast();
    }
    private boolean takeResolverResult(DelayedSession session) {
        require(session.phase==DELAYED_RESULT&&session.resolver.isEmpty()&&session.call==null&&session.retiring==null,"Resolver result not ready");
        boolean result=session.booleanResult; session.phase=DELAYED_IDLE; return result;
    }

    private SubstitutionEntry substitutionEntry(DelayedSession session,Object name) {
        int hash=delayedNameHash(session,name); ArrayList<SubstitutionEntry> bucket=session.substitutions.get(hash);
        if(bucket!=null) for(SubstitutionEntry entry:bucket) {
            delayedWork(session,1); require(entry.live&&entry.name!=null&&entry.name.owned,"Substitution key owner missing");
            if(mvarNameEqual(session.budget,name,entry.name.value)) return entry;
        }
        return null;
    }
    private void publishSubstitution(DelayedSession session,SubstitutionEntry entry) {
        require(!entry.live&&entry.name!=null&&entry.name.owned&&entry.value!=null&&entry.value.owned,"Incomplete new substitution entry");
        require(session.substitutionOwners.size()<MAX_DELAYED_NAMES,"Substitution entry allocation bound");
        session.substitutionOwners.add(entry); ArrayList<SubstitutionEntry> bucket=session.substitutions.get(entry.hash);
        if(bucket==null) { bucket=new ArrayList<>(); session.substitutions.put(entry.hash,bucket); }
        bucket.add(entry); entry.live=true;
    }
    private void detachSubstitution(DelayedSession session,SubstitutionEntry entry) {
        ArrayList<SubstitutionEntry> bucket=session.substitutions.get(entry.hash);
        require(entry.live&&bucket!=null,"Missing substitution erase entry"); delayedWork(session,bucket.size());
        require(bucket.remove(entry),"Substitution erase index differs"); if(bucket.isEmpty()) session.substitutions.remove(entry.hash); entry.live=false;
    }
    private static final int SF_PREPARE=0,SF_ENTER=1,SF_SAVE=2,SF_RELEASE_OLD=3,SF_COMMIT=4,SF_INSTALLED=5;
    private static final int SF_RESTORE_NEXT=21,SF_RESTORE_VALUE=22,SF_RESTORE_KEY=23,SF_RESTORE_COMMIT=24,SF_RESTORED=25,SF_DRAIN_SAVED=30,SF_DRAIN_ARGS=31,SF_DRAINED=32;
    private void prepareSubstitutionValue(DelayedSession session,SubstitutionFrame frame,Object name,Object value) {
        require(frame.newName==null&&frame.newValue==null&&frame.replacement==null,"Substitution replacement escrow occupied");
        frame.newValue=exprCredit(value); acquireExpr(frame.newValue);
        if(frame.existing==null) {
            require(session.substitutionOwners.size()<MAX_DELAYED_NAMES,"Substitution entry allocation bound");
            frame.replacement=new SubstitutionEntry(); frame.replacement.hash=delayedNameHash(session,name);
            frame.newName=exprCredit(name); acquireExpr(frame.newName);
        }
    }
    private void commitSubstitutionValue(DelayedSession session,SubstitutionFrame frame,int depth,int scope) {
        require(frame.newValue!=null&&frame.newValue.owned,"Substitution replacement value missing");
        SubstitutionEntry entry=frame.existing==null?frame.replacement:frame.existing;
        require(entry!=null&&entry.value==null,"Substitution old value not retired");
        if(frame.existing==null) { entry.name=frame.newName; frame.newName=null; }
        entry.value=frame.newValue; frame.newValue=null; entry.depth=depth; entry.scope=scope;
        if(frame.existing==null) publishSubstitution(session,entry);
        frame.existing=null; frame.replacement=null; frame.retiringValue=null; frame.retiringName=null;
    }
    private void stepSubstitutionInstall(RuntimeAction action,DelayedSession session,SubstitutionFrame frame) {
        delayedWork(session,1); resumeDelayedRetiring(action,session);
        require(!frame.restored&&!frame.completed,"No running substitution install");
        if(frame.stage==SF_PREPARE) {
            require(frame.ownsArguments&&frame.sourceArguments instanceof Node,"Missing research argument source");
            Node arguments=(Node)frame.sourceArguments;
            if(frame.index<arguments.arraySize()) {
                ExprCredit argument=exprCredit(arguments.fields[frame.index]); frame.arguments.add(argument); frame.index++; acquireExpr(argument); return;
            }
            frame.index=0; frame.stage=SF_ENTER;
        }
        if(frame.stage==SF_ENTER) { scopedPush(session); frame.scopePushed=true; frame.stage=SF_SAVE; return; }
        Node fvars=node(frame.fvars); int count=fvars.arraySize();
        if(frame.stage==SF_SAVE) {
            if(frame.index==count) { frame.stage=SF_INSTALLED; frame.completed=true; return; }
            require(frame.saved.size()<MAX_DELAYED_NAMES&&frame.arguments.size()>=count,"Delayed saved-substitution bound/arity");
            Node fvar=exprNode(fvars.fields[frame.index]); require(fvar.tag==1,"Delayed substitution requires FVar elements"); Object name=fvar.fields[0]; nameNode(name);
            frame.existing=substitutionEntry(session,name);
            SavedSubstitution saved=new SavedSubstitution(); saved.name=exprCredit(name); frame.saved.add(saved); acquireExpr(saved.name);
            saved.hadOld=frame.existing!=null;
            if(saved.hadOld) {
                require(frame.existing.value!=null&&frame.existing.value.owned,"Old substitution value missing");
                saved.oldDepth=frame.existing.depth; saved.oldScope=frame.existing.scope;
                saved.oldValue=exprCredit(frame.existing.value.value); acquireExpr(saved.oldValue);
            }
            ExprCredit argument=frame.arguments.get(frame.arguments.size()-1-frame.index); require(argument.owned,"Substitution argument backing owner missing");
            prepareSubstitutionValue(session,frame,name,argument.value); frame.stage=SF_RELEASE_OLD; return;
        }
        if(frame.stage==SF_RELEASE_OLD) {
            frame.stage=SF_COMMIT;
            if(frame.existing!=null) { frame.retiringValue=frame.existing.value; frame.existing.value=null; releaseDelayed(action,session,frame.retiringValue); }
            return;
        }
        require(frame.stage==SF_COMMIT,"Invalid substitution install continuation");
        commitSubstitutionValue(session,frame,frame.depth,session.cache.scope); frame.index++; frame.stage=SF_SAVE;
    }
    private void beginSubstitutionRestore(DelayedSession session,SubstitutionFrame frame) {
        require(frame.completed&&frame.stage==SF_INSTALLED&&frame.scopePushed&&!frame.restored,"Substitution scope is not installed");
        scopedPop(session); session.resultScope=Math.min(session.resultScope,session.cache.scope);
        frame.scopePushed=false; frame.completed=false; frame.index=0; frame.stage=SF_RESTORE_NEXT;
    }
    private void stepSubstitutionRestore(RuntimeAction action,DelayedSession session,SubstitutionFrame frame) {
        delayedWork(session,1); resumeDelayedRetiring(action,session);
        require(!frame.completed&&!frame.restored,"No running substitution restoration");
        if(frame.stage==SF_RESTORE_NEXT) {
            if(frame.index==frame.saved.size()) { frame.restored=true; frame.completed=true; frame.stage=SF_RESTORED; return; }
            SavedSubstitution saved=frame.saved.get(frame.index); require(saved.name!=null&&saved.name.owned,"Saved substitution Name owner missing");
            frame.existing=substitutionEntry(session,saved.name.value); frame.erasing=!saved.hadOld;
            if(frame.erasing) {
                if(frame.existing==null) { frame.index++; return; }
                detachSubstitution(session,frame.existing);
                frame.retiringValue=frame.existing.value; frame.existing.value=null;
                frame.retiringName=frame.existing.name; frame.existing.name=null;
            } else {
                require(saved.oldValue!=null&&saved.oldValue.owned,"Saved old substitution value missing");
                prepareSubstitutionValue(session,frame,saved.name.value,saved.oldValue.value);
                if(frame.existing!=null) { frame.retiringValue=frame.existing.value; frame.existing.value=null; }
            }
            frame.stage=SF_RESTORE_VALUE; return;
        }
        if(frame.stage==SF_RESTORE_VALUE) { frame.stage=SF_RESTORE_KEY; releaseDelayed(action,session,frame.retiringValue); return; }
        if(frame.stage==SF_RESTORE_KEY) { frame.stage=SF_RESTORE_COMMIT; releaseDelayed(action,session,frame.retiringName); return; }
        require(frame.stage==SF_RESTORE_COMMIT,"Invalid substitution restoration continuation");
        if(!frame.erasing) {
            SavedSubstitution saved=frame.saved.get(frame.index); commitSubstitutionValue(session,frame,saved.oldDepth,saved.oldScope);
        } else { frame.existing=null; frame.retiringValue=null; frame.retiringName=null; }
        frame.index++; frame.stage=SF_RESTORE_NEXT;
    }
    private void stepSubstitutionFrameDrain(RuntimeAction action,DelayedSession session,SubstitutionFrame frame) {
        delayedWork(session,1); resumeDelayedRetiring(action,session);
        require(frame.restored&&!frame.scopePushed,"Cannot drain an active substitution scope");
        if(frame.stage==SF_RESTORED) { frame.completed=false; frame.cleanup=0; frame.stage=SF_DRAIN_SAVED; }
        if(frame.stage==SF_DRAIN_SAVED) {
            if(frame.cleanup<frame.saved.size()*2) {
                SavedSubstitution saved=frame.saved.get(frame.cleanup/2); ExprCredit credit=(frame.cleanup++&1)==0?saved.oldValue:saved.name;
                releaseDelayed(action,session,credit); return;
            }
            frame.saved.clear(); frame.cleanup=0; frame.stage=SF_DRAIN_ARGS;
        }
        if(frame.stage==SF_DRAIN_ARGS) {
            if(frame.ownsArguments&&frame.cleanup<frame.arguments.size()) { ExprCredit credit=frame.arguments.get(frame.cleanup++); releaseDelayed(action,session,credit); return; }
            frame.arguments.clear(); frame.fvars=null; frame.sourceArguments=null; frame.stage=SF_DRAINED; frame.completed=true;
        }
        require(frame.stage==SF_DRAINED,"Invalid substitution frame drain");
    }
    private void stepSubstitutionLookup(RuntimeAction action,DelayedSession session,SubstitutionLookup frame) {
        delayedWork(session,1); resumeDelayedRetiring(action,session);
        if(frame.stage==0) {
            frame.entry=substitutionEntry(session,frame.name);
            if(frame.entry==null) { frame.completed=true; return; }
            require(frame.entry.value!=null&&frame.entry.value.owned&&frame.depth>=frame.entry.depth,"Delayed substitution lookup depth/owner invalid");
            int delta=frame.depth-frame.entry.depth; require(delta<=MAX_EXPR_JOB_OFFSET,"Delayed substitution lift bound");
            session.resultScope=Math.max(session.resultScope,frame.entry.scope); frame.present=true;
            if(delta==0) { frame.optional=exprCredit(frame.entry.value.value); acquireExpr(frame.optional); frame.stage=2; return; }
            require(runtimeAction==action&&objects[action.slot]==null&&session.call==null&&session.constructorCall==null,"Substitution lift receiver occupied");
            for(int role=0;role<9;role++) exprConstructor(session.policy.constructors,role);
            RuntimeAction child=newAction(ACTION_EXPR_MACHINERY,null,ACTION_BODY,action.slot,ASSIGN,null);
            ExprMachineryState worker=new ExprMachineryState(); worker.policy=session.policy.constructors; worker.budget=session.budget;
            pushReplaceJob(worker,EXPR_LIFT_JOB,frame.entry.value.value,0,delta,new Object[0]);
            child.exprMachinery=worker; objects[child.slot]=null; frame.stage=1; publishAction(child); return;
        }
        if(frame.stage==1) { Object value=objects[action.slot]; exprNode(value); frame.optional=new ExprCredit(value,true); objects[action.slot]=null; frame.stage=2; }
        if(frame.stage==2) { frame.returned=exprCredit(frame.optional.value); acquireExpr(frame.returned); frame.stage=3; return; }
        if(frame.stage==3) { frame.stage=4; releaseDelayed(action,session,frame.optional); return; }
        require(frame.stage==4,"Invalid substitution lookup completion"); frame.optional=null; frame.completed=true;
    }

    private void sealDelayedSession(DelayedSession session) {
        require(session.phase==DELAYED_IDLE&&session.resolver.isEmpty()&&session.call==null&&session.constructorCall==null
                &&session.cacheOperation==null&&session.substitution==null&&session.lookup==null&&session.substitutionFrames.isEmpty()
                &&session.retiring==null&&session.result==null&&session.cache.scope==0,"Delayed session is not idle for seal");
        session.resolvableExpressions.clear(); session.pending.clear(); session.normalized.clear(); session.substitutions.clear(); session.cache.index.clear();
        for(ScopedBucket bucket:session.cache.buckets) bucket.key=null;
        session.cache.sealed=true; session.phase=DELAYED_SEALED;
    }
    private void stepDelayedDrain(RuntimeAction action,DelayedSession session) {
        delayedWork(session,1); resumeDelayedRetiring(action,session); require(session.phase==DELAYED_SEALED,"Delayed member drain requires sealed session");
        if(session.drainStage==0) {
            if(session.drainCursor<session.pendingOwners.size()) { ExprCredit name=session.pendingOwners.get(session.drainCursor++).name; releaseDelayed(action,session,name); return; }
            session.pendingOwners.clear(); session.drainCursor=0; session.drainStage=1; return;
        }
        if(session.drainStage==1) {
            if(session.drainCursor<session.saved.size()) { ExprCredit credit=session.saved.get(session.saved.size()-1-session.drainCursor++); releaseDelayed(action,session,credit); return; }
            session.saved.clear(); session.drainCursor=0; session.drainStage=2; return;
        }
        if(session.drainStage==2) {
            if(session.drainCursor<session.nameOwners.size()) { ExprCredit credit=session.nameOwners.get(session.nameOwners.size()-1-session.drainCursor++).name; releaseDelayed(action,session,credit); return; }
            session.nameOwners.clear(); session.normalized.clear(); session.drainCursor=0; session.drainStage=3; return;
        }
        if(session.drainStage==3) {
            ScopedExprCache cache=session.cache;
            if(cache.retiringEntry!=null) {
                ScopedEntry entry=cache.retiringEntry; require(entry.result!=null&&!entry.result.owned,"Scoped member owner not drained");
                if(entry.reserved) { require(cache.liveEntries>0,"Scoped drain reservation underflow"); cache.liveEntries--; entry.reserved=false; }
                entry.result=null; cache.retiringEntry=null;
            }
            if(cache.drainBucket<cache.buckets.size()) {
                ScopedBucket bucket=cache.buckets.get(cache.drainBucket);
                if(bucket.entries.isEmpty()) { cache.drainBucket++; return; }
                cache.retiringEntry=bucket.entries.remove(bucket.entries.size()-1); releaseDelayed(action,session,cache.retiringEntry.result); return;
            }
            require(cache.liveEntries==0,"Scoped member drain leaked reservations"); cache.buckets.clear(); cache.current=null;
            session.drainStage=4; session.drainCursor=0; return;
        }
        if(session.drainStage==4) {
            if(session.drainCursor<session.substitutionOwners.size()*2) {
                SubstitutionEntry entry=session.substitutionOwners.get(session.drainCursor/2);
                ExprCredit credit=(session.drainCursor++&1)==0?entry.value:entry.name; releaseDelayed(action,session,credit); return;
            }
            session.substitutionOwners.clear(); session.phase=DELAYED_DRAINED; return;
        }
        throw error("Invalid delayed member drain stage");
    }
    private int liveSubstitutions(DelayedSession session) {
        int count=0; for(ArrayList<SubstitutionEntry> bucket:session.substitutions.values()) { delayedWork(session,bucket.size()); count+=bucket.size(); } return count;
    }
    private void finishDelayedCommand(DelayedResearchState state,long observation) {
        DelayedSession session=state.session; delayedWork(session,1); DelayedCommand command=state.commands[state.commandCursor];
        state.observations.add((long)command.operation); state.observations.add((long)session.cache.scope);
        state.observations.add((long)session.resultScope); state.observations.add(observation);
        state.lastObservation=observation; state.commandCursor++; state.stage=0;
    }
    private void launchDelayedCommand(DelayedResearchState state) {
        DelayedSession session=state.session; DelayedCommand command=state.commands[state.commandCursor];
        require(session.phase==DELAYED_IDLE&&session.call==null&&session.constructorCall==null&&session.cacheOperation==null
                &&session.substitution==null&&session.lookup==null,"Delayed protocol has an outstanding operation");
        if(state.mode==DELAYED_CACHE_PROTOCOL) {
            if(command.operation==DC_PUSH) { scopedPush(session); finishDelayedCommand(state,session.cache.generationCounter); return; }
            if(command.operation==DC_POP) { scopedPop(session); finishDelayedCommand(state,session.cache.generationCounter); return; }
            if(command.operation==DC_INSERT) {
                state.pendingInput=exprCredit(state.anchors.get(command.value).value); acquireExpr(state.pendingInput);
            }
            startScopedOperation(session,command.operation,state.anchors.get(command.key).value,command.depth,state.pendingInput,command.resultScope);
            state.pendingInput=null; state.stage=2; return;
        }
        if(state.mode==DELAYED_RESOLVER_PROTOCOL) { startResolver(session,state.anchors.get(command.key).value); state.stage=2; return; }
        if(command.operation==DC_INSTALL) {
            require(session.substitutionFrames.size()<MAX_DELAYED_FRAMES,"Substitution scope/frame bound");
            SubstitutionFrame frame=new SubstitutionFrame(); frame.fvars=state.anchors.get(command.key).value;
            frame.sourceArguments=state.anchors.get(command.value).value; frame.depth=command.depth; frame.ownsArguments=true;
            session.substitution=frame; state.stage=2; return;
        }
        if(command.operation==DC_RESTORE) {
            SubstitutionFrame frame=session.substitutionFrames.peekLast(); require(frame!=null,"No substitution frame to restore");
            session.substitution=frame; beginSubstitutionRestore(session,frame); state.stage=2; return;
        }
        SubstitutionLookup lookup=new SubstitutionLookup(); lookup.name=state.anchors.get(command.key).value; lookup.depth=command.depth;
        session.lookup=lookup; state.stage=2;
    }
    private void stepDelayedFoundationResearch(RuntimeAction action) {
        DelayedResearchState state=action.delayedResearch; require(state!=null,"Missing private delayed foundation state");
        DelayedSession session=state.session; delayedWork(session,1); resumeDelayedRetiring(action,session);
        require(session.constructorCall==null,"Stage four has no typed delayed constructor target");
        if(state.stage==0) {
            if(state.commandCursor==state.commands.length) { sealDelayedSession(session); state.stage=10; state.cleanup=0; return; }
            state.stage=1; releaseDelayed(action,session,state.lastResult); return;
        }
        if(state.stage==1) { state.lastResult=null; launchDelayedCommand(state); return; }
        if(state.stage==2) {
            DelayedCommand command=state.commands[state.commandCursor];
            if(state.mode==DELAYED_CACHE_PROTOCOL) {
                ScopedCacheOperation op=session.cacheOperation; stepScopedCache(action,session);
                if(op.completed) {
                    state.lastResult=op.returned; op.returned=null; session.cacheOperation=null;
                    finishDelayedCommand(state,command.operation==DC_LOOKUP?(op.hit?1:0):session.cache.liveEntries);
                }
                return;
            }
            if(state.mode==DELAYED_RESOLVER_PROTOCOL) {
                stepResolver(action,session); if(session.phase==DELAYED_RESULT) finishDelayedCommand(state,takeResolverResult(session)?1:0); return;
            }
            if(command.operation==DC_INSTALL) {
                SubstitutionFrame frame=session.substitution; stepSubstitutionInstall(action,session,frame);
                if(frame.completed) { session.substitutionFrames.addLast(frame); session.substitution=null; finishDelayedCommand(state,liveSubstitutions(session)); }
                return;
            }
            if(command.operation==DC_RESTORE) {
                SubstitutionFrame frame=session.substitution; stepSubstitutionRestore(action,session,frame);
                if(frame.completed) { require(session.substitutionFrames.peekLast()==frame,"Substitution restoration stack differs"); session.substitutionFrames.removeLast(); state.stage=3; }
                return;
            }
            SubstitutionLookup lookup=session.lookup; stepSubstitutionLookup(action,session,lookup);
            if(lookup.completed) { state.lastResult=lookup.returned; lookup.returned=null; session.lookup=null; finishDelayedCommand(state,lookup.present?1:0); }
            return;
        }
        if(state.stage==3) {
            SubstitutionFrame frame=session.substitution; stepSubstitutionFrameDrain(action,session,frame);
            if(frame.completed) { session.substitution=null; finishDelayedCommand(state,liveSubstitutions(session)); } return;
        }
        if(state.stage==10) {
            if(state.cleanup<state.anchors.size()) { ExprCredit anchor=state.anchors.get(state.cleanup++); releaseDelayed(action,session,anchor); return; }
            state.anchors.clear(); state.stage=11;
        }
        if(state.stage==11) { stepDelayedDrain(action,session); if(session.phase==DELAYED_DRAINED) state.stage=12; return; }
        if(state.stage==12) {
            require(session.phase==DELAYED_DRAINED&&state.context.current!=null&&state.context.current.owned,"Delayed research report owners missing");
            Node report=new Node(0,3,0); state.output=new ExprCredit(report,true); allocations++;
            report.fields[0]=state.context.current.value; state.context.current.owned=false; state.context.current=null; state.outputFields=1;
            if(state.lastResult!=null) { require(state.lastResult.owned,"Delayed research last result owner missing"); report.fields[1]=state.lastResult.value; state.lastResult.owned=false; }
            else report.fields[1]=ERASED;
            state.outputFields=2; report.fields[2]=Long.valueOf(state.lastObservation); state.outputFields=3; state.stage=13; return;
        }
        require(state.stage==13&&state.output!=null&&state.output.owned&&state.outputFields==3&&state.context.current==null,"Incomplete delayed protocol report");
        Object output=state.output.value; state.output.owned=false; action.output=output;
        state.lastResult=null; state.pendingInput=null; state.output=null; state.session=null; state.context=null; state.budget=null; state.commands=null;
        action.delayedResearch=null; finishAction(action,output);
    }


    /** Five exact source-authenticated ordinary helper roles, without guest values,
     * Program bodies or catalogue resources. SHA identities remain descriptive;
     * the trusted source adapter authenticates the original bytes. */
    public static final class LevelInstantiationPolicy {
        private final Header[] helpers;
        private LevelInstantiationPolicy(Header[] helpers) { this.helpers=helpers.clone(); }
        public static LevelInstantiationPolicy originalHelpers(Header getter,Header setter,Header succ,Header max,Header imax) {
            Header[] helpers={getter,setter,succ,max,imax};
            String[] names={"Lean.getLevelMVarAssignmentExp","Lean.assignLevelMVarExp","Lean.Level.succ._override",
                    "Lean.Level.max._override","Lean.Level.imax._override"};
            String[] hashes={"2be7a950bc5a94407c262d74d69b8381e3cb0f399ac04256e158fb53500f37ec",
                    "38e9fa5f0baa194fa8ac0f9d3d9563e17bce02330e87caa8b976a5eb217ae2da",
                    "66444fd502f36a4fae92d150070f35aa8366e535cb31816f94df52e4e37d88bc",
                    "1e7d159b9bc54bafea5853b8b53d9929b862d95405ea641629f2dd4aedfc4043",
                    "d0ec934a52dc032906aeab3e431ff1dfffd3c0bab7501de1d1aa89a32a572f57"};
            String[][] parameters={{"object","tobject"},{"object","tobject","tobject"},
                    {"tobject"},{"tobject","tobject"},{"tobject","tobject"}};
            for(int role=0;role<helpers.length;role++) {
                Header h=helpers[role];
                require(h!=null&&h.kind.equals("fdecl")&&h.originalSha256.equals(hashes[role]),"Level instantiation helper role/source hash differs");
                if(role!=0) require(h.source==getter.source,"Level instantiation helpers have different source bindings");
                Object name=Arrays.asList("anonymous");
                for(String segment:names[role].split("\\.")) name=Arrays.asList("str",name,segment);
                require(h.exactName.equals(frozenName(name)),"Level instantiation helper typed Name differs");
                Map<String,Object> d=h.declaration;
                require(d.keySet().equals(new HashSet<>(Arrays.asList("f","info","type","xs")))
                        &&map(d.get("info")).isEmpty()&&d.get("f").equals(h.exactName),"Level instantiation helper declaration differs");
                List<Object> xs=list(d.get("xs"));
                String result=role==1?"object":"tobject";
                require(xs.size()==parameters[role].length&&h.resultType.equals(result)&&result.equals(d.get("type")),"Level instantiation helper raw ABI differs");
                for(int i=0;i<xs.size();i++) {
                    Map<String,Object> p=map(xs.get(i)),x=map(p.get("x"));
                    require(p.keySet().equals(new HashSet<>(Arrays.asList("borrow","ty","x")))
                            &&x.keySet().equals(Collections.singleton("idx"))&&number(x.get("idx"))==i+1
                            &&Boolean.FALSE.equals(p.get("borrow"))&&parameters[role][i].equals(p.get("ty")),
                            "Level instantiation helper parameter declaration differs");
                }
                Map<String,Object> runtime=map(h.evidence.get("runtime"));
                require(runtime.keySet().equals(new HashSet<>(Arrays.asList("initializer","role")))
                        &&runtime.get("initializer")==null&&"ordinary".equals(runtime.get("role")),"Level instantiation helper is not an ordinary original function");
            }
            return new LevelInstantiationPolicy(helpers);
        }
    }
    private LevelInstantiationPolicy levelInstantiationPolicy;
    private static final boolean LEVEL_INSTANTIATION_READY=true;
    private Function levelInstantiationHelper(LevelInstantiationPolicy policy,int role) {
        Header header=policy.helpers[role]; int id=program.functionId(header); Function function=program.functions[id];
        require(function.header==header&&function.intrinsic==0&&function.hostExtern==null&&program.guestExports[id]==null,
                "Level instantiation helper is not the exact ordinary function");
        requireExecutableAbi(function);
        require(function.resultType==OBJ,"Level instantiation helper requires OBJ result");
        for(int lane:function.paramTypes) require(lane==OBJ,"Level instantiation helper requires OBJ parameters");
        return preflightCallable(function,true);
    }
    /** Configure once at an open idle boundary. No helper body is forced. */
    public void configureLevelInstantiation(LevelInstantiationPolicy policy) {
        explicitOnly();
        require(taskRuntime!=null&&policy!=null,"Level instantiation requires active runtime and actual helper policy");
        if(closed||disposed||untrackedFailure||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||continuationDepth!=0
                ||runtimeAction!=null||hostCompletion!=null||hostGuestRecord!=null||quietCurrent!=null||releasePending!=0
                ||releaseTransaction!=null||releaseRoot)
            throw new IllegalStateException("Level instantiation configuration requires an open idle engine");
        require(levelInstantiationPolicy==null,"Level instantiation policy is already configured");
        for(int role=0;role<5;role++) levelInstantiationHelper(policy,role);
        levelInstantiationPolicy=policy;
    }
    private void levelInstantiationProfile(Function function) {
        require(LEVEL_INSTANTIATION_READY,"Level instantiation traversal is not yet enabled");
        require(explicit&&taskRuntime!=null&&levelInstantiationPolicy!=null,"Level instantiation requires active explicit runtime and configured original helpers");
        Header origin=function.header;
        require(origin!=null&&origin.source==levelInstantiationPolicy.helpers[0].source
                &&origin.kind.equals("extern")&&origin.originalSha256.equals("43de9c312f7e7a4bdeb9cd3b070ca4bd245fcca722f532b05f9e3083c1847605"),
                "Level instantiation native source Header differs");
        Object name=Arrays.asList("str",Arrays.asList("str",Arrays.asList("anonymous"),"Lean"),"instantiateLevelMVarsImp");
        require(origin.exactName.equals(frozenName(name)),"Level instantiation native typed Name differs");
        for(int role=0;role<5;role++) levelInstantiationHelper(levelInstantiationPolicy,role);
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
    private boolean graphInstalled,moduleGraphInstalled;
    private PreparedGlobalSource preparedModuleSource;
    private boolean initializing;
    // Narrow interpreted [init] protocol; this is not a module-completeness ledger.
    private BitSet initializerAttempts=new BitSet();
    private Header pendingInitializerGlobal,pendingInitializerAction;
    private boolean initializerFailed;
    private Map<Integer,PreparedGlobalSource> preparedGlobalSources=Collections.emptyMap();
    private boolean closed;
    private boolean untrackedFailure;
    private final Object runtimeIdentity=new Object();
    private Node stdoutRoot; // legacy root; opt-in stdio default stdout occurrence
    private Node stdinDefaultRoot,stderrRoot;
    private final StringBuilder stderrOutput=new StringBuilder();
    /** All supported synchronous tasks execute on this ONE branch-local thread.
     * currentTask never selects, inherits, resets or retires these slots. */
    private static final class StdioContext { final Node[] current=new Node[3]; }
    private StdioContext stdioContext;
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
    private static final int ACTION_RELEASE=1,ACTION_DISPOSE=2,ACTION_NATIVE=3,ACTION_HOST=4,ACTION_TASK=5,ACTION_RESOLVE=6,ACTION_RUN_TASK=7,ACTION_PROFILE=8,ACTION_FIND=9,ACTION_LEVEL_MVARS=10,ACTION_EXPR_MACHINERY=11,ACTION_MVAR_SESSION_RESEARCH=12,ACTION_SHARECOMMON=13,ACTION_EXPR_DIRECT_RESEARCH=14,ACTION_EXPR_REPLACE=15,ACTION_EXPR_ABSTRACT=16,ACTION_DELAYED_FOUNDATION_RESEARCH=17,ACTION_EXPR_PURE=18,ACTION_EXPR_FULL_RESEARCH=19,ACTION_HOST_GUEST=20;
    private static final Body ACTION_BODY=new Body();
    /** Typed ownership/control state, separate from NodeMetadata. The output
     * scratch slot is reserved before callbacks may enter generic AP. */
    private static final class RuntimeAction {
        RuntimeAction parent;
        HostGuestRecord guest;
        FindState find;
        ShareState share;
        LevelInstantiationState levelMvars;
        ExprMachineryState exprMachinery;
        MVarSessionResearchState mvarSessionResearch;
        ExprDirectResearchState exprDirect;
        DelayedResearchState delayedResearch;
        ExprFullResearchState exprFull;
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
        if(action.parent!=null&&action.parent.share!=null&&action.parent.share.discarding) {
            Node current=action.current;
            require(!current.ref&&!current.readyTask&&current.closure==null&&!isPromise(current)&&!isByteArray(current)
                    &&(current.array||current.tag>=0&&current.tag<=243),"ShareCommon duplicate quiet proof reached opaque zero");
        }
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
        if(stdioContext!=null) { stepStdioDispose(action); return; }
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
        return taskRuntime!=null&&(pureExprTransform(op)||abstractPrimitive(op)||op==EXPR_REPLACE||op==SHARECOMMON_QUICK||op==LEVEL_INSTANTIATE||op==EXPR_INSTANTIATE_MVARS||op==VOID_MK||op==PROFILE_IT||findPrimitive(op)||taskPrimitive(op)||op==TASK_MAP||op==REF_SET||op==ARRAY_POP||op==ARRAY_FSET||op==ARRAY_USET||op==ARRAY_CHECKED_SET||op==ARRAY_REPLICATE);
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
    /** Inactive Void.mk promises only a bounded quiet domain. Preflight the
     * positive owning graph before claiming a last root credit; shared children
     * cannot be skipped because duplicate incoming edges may jointly retire them. */
    private void validateQuietVoid(Object value) {
        if(taskRuntime!=null||!(value instanceof Node)) return;
        Node root=(Node)value;
        if(root.rc==0||root.rc>1) return;
        IdentityHashMap<Node,Boolean> seen=new IdentityHashMap<>();
        ArrayDeque<Node> pending=new ArrayDeque<>(); pending.push(root); long edges=0;
        while(!pending.isEmpty()) {
            Node current=pending.pop();
            validateHostObject(current);
            if(current.rc==0||seen.containsKey(current)) continue;
            require(seen.size()<100_000,"Void.mk quiet graph exceeds bounded node profile");
            seen.put(current,Boolean.TRUE);
            require(!(kindMetadata(current) instanceof TaskMetadata),"Void.mk quiet profile rejects runtime Task/Promise metadata");
            NodeMetadata kind=kindMetadata(current);
            if(current.array) {
                require(kind instanceof ArrayState&&!current.readyTask&&current.tag==246&&current.scalars.length==0,
                        "Void.mk quiet profile rejects unknown array shape"); array(current);
            } else if(isByteArray(current)) byteArray(current);
            else if(current.ref) { require(!current.readyTask,"Void.mk quiet profile rejects unknown Ref shape"); reference(current); }
            else if(current.readyTask) readyTaskNode(current);
            else if(current.closure!=null) {
                require(current.tag==245&&current.scalars.length==0,"Void.mk quiet profile rejects unknown closure shape"); acceptsClosure(current);
            } else require(kind==null&&current.tag>=0&&current.tag<=243,"Void.mk quiet profile rejects unknown object kind");
            int live=owningFieldCount(current);
            require(live>=0&&live<=current.fields.length,"Void.mk quiet owning extent outside payload");
            require(edges<=1_000_000-live,"Void.mk quiet graph exceeds bounded edge profile"); edges+=live;
            if(Thread.currentThread().isInterrupted()) throw error("Void.mk quiet preflight interrupted");
            for(int i=0;i<live;i++) {
                Object child=current.fields[i];
                if(child==null) { require(current.ref,"Void.mk quiet profile rejects absent owning field"); continue; }
                if(child instanceof Node) pending.push((Node)child); else validateHostObject(child);
            }
        }
    }
    private void validateVoidArguments(Object erased,Object value) {
        require(ERASED.equals(erased),"Void.mk requires an erased parameter placeholder");
        validateHostObject(value); validateQuietVoid(value);
    }
    private void voidIntrinsic(Object erased,Object value) {
        validateVoidArguments(erased,value);
        releaseQuiet(value,1); result=ERASED;
    }
    private void validateNative(Function function,Object[] args) {
        if(pureExprTransform(function.intrinsic)) { validatePureExprTransform(function,args); return; }
        if(function.intrinsic==EXPR_REPLACE) { validateExprReplace(function,args); return; }
        if(abstractPrimitive(function.intrinsic)) { validateAbstractArguments(function,args); return; }
        if(function.intrinsic==SHARECOMMON_QUICK) {
            shareCommonProfile(); require(args!=null&&args.length==2&&ERASED.equals(args[0]),"ShareCommon requires erased placeholder and borrowed input");
            shareKind(args[1]); return;
        }
        if(function.intrinsic==LEVEL_INSTANTIATE) { validateLevelArguments(function,args); return; }
        if(function.intrinsic==EXPR_INSTANTIATE_MVARS) { validateExprInstantiationArguments(function,args); return; }
        if(function.intrinsic==ARRAY_CHECKED_SET) { validateCheckedArraySet(args); return; }
        if(function.intrinsic==VOID_MK) {
            require(args!=null&&args.length==2,"Void.mk native arity mismatch");
            validateVoidArguments(args[0],args[1]); return;
        }
        if(function.intrinsic==PROFILE_IT) { validateProfile(function,args); return; }
        if(findPrimitive(function.intrinsic)) { validateFind(args); return; }
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
        RuntimeAction action=newAction(function.intrinsic==EXPR_INSTANTIATE_MVARS?ACTION_EXPR_FULL_RESEARCH:pureExprTransform(function.intrinsic)?ACTION_EXPR_PURE:abstractPrimitive(function.intrinsic)?ACTION_EXPR_ABSTRACT:function.intrinsic==EXPR_REPLACE?ACTION_EXPR_REPLACE:function.intrinsic==SHARECOMMON_QUICK?ACTION_SHARECOMMON:function.intrinsic==LEVEL_INSTANTIATE?ACTION_LEVEL_MVARS:findPrimitive(function.intrinsic)?ACTION_FIND:function.intrinsic==PROFILE_IT?ACTION_PROFILE:
                taskPrimitive(function.intrinsic)||function.intrinsic==TASK_MAP?ACTION_TASK:ACTION_NATIVE,function,next,dest,kind,surplus);
        action.arguments=args;
        if(function.intrinsic==EXPR_INSTANTIATE_MVARS) prepareExprFullAction(action,exprInstantiationPolicy,args[0],exprNode(args[1]));
        if(pureExprTransform(function.intrinsic)) preparePureExprTransform(action,function,args);
        if(abstractPrimitive(function.intrinsic)) prepareAbstractAction(action,function,args);
        if(function.intrinsic==EXPR_REPLACE) {
            ExprMachineryState state=new ExprMachineryState(); state.policy=exprTransformsProfile(function);
            state.budget=new InstantiationBudget(); state.borrowedPredicate=(Node)args[0];
            pushReplaceJob(state,EXPR_CALLBACK_JOB,args[1],0,0,new Object[0]); action.exprMachinery=state; objects[action.slot]=null;
        }
        if(function.intrinsic==SHARECOMMON_QUICK) {
            ShareState state=new ShareState(); state.input=args[1]; sharePush(state,state.input); action.share=state; objects[action.slot]=null;
        }
        if(function.intrinsic==LEVEL_INSTANTIATE) {
            LevelInstantiationState state=new LevelInstantiationState();
            MVarContextCell cell=new MVarContextCell(); cell.current=new LevelCredit(args[0],true);
            state.session=newLevelSession(cell,new InstantiationBudget(),levelInstantiationPolicy);
            state.input=new LevelCredit(args[1],true); action.levelMvars=state;
            startLevelJob(state.session,args[1]); objects[action.slot]=null;
        }
        if(findPrimitive(function.intrinsic)) {
            FindState state=new FindState(); state.predicate=(Node)args[0]; state.root=(Node)args[1];
            state.extended=function.intrinsic==EXPR_FIND_EXT;
            pushFind(state,state.root); action.find=state; objects[action.slot]=null;
        }
        publishAction(action); applicationEntry(kind);
    }
    private static boolean findPrimitive(int op) { return op==EXPR_FIND||op==EXPR_FIND_EXT; }
    /** Immutable, explicitly selected target layout; not native memory recovery. */
    public static final class JvmCarrierLayoutV1 {
        private JvmCarrierLayoutV1() {}
        public static JvmCarrierLayoutV1 normalizedValues() { return new JvmCarrierLayoutV1(); }
    }
    private JvmCarrierLayoutV1 shareCommonLayout;
    public void configureShareCommon(JvmCarrierLayoutV1 layout) {
        explicitOnly();
        require(taskRuntime!=null&&layout!=null,"ShareCommon requires active runtime and explicit JVM layout");
        if(closed||disposed||untrackedFailure||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||continuationDepth!=0
                ||runtimeAction!=null||hostCompletion!=null||hostGuestRecord!=null||quietCurrent!=null||releasePending!=0
                ||releaseTransaction!=null||releaseRoot)
            throw new IllegalStateException("ShareCommon configuration requires an open idle engine");
        require(shareCommonLayout==null,"ShareCommon layout is already configured");
        shareCommonLayout=layout;
    }
    private void shareCommonProfile() {
        require(explicit&&taskRuntime!=null&&shareCommonLayout!=null,
                "ShareCommon requires active explicit runtime and configured JvmCarrierLayoutV1");
    }
    private static final int SHARE_LONG=1,SHARE_INTEGER=2,SHARE_STRING=3,SHARE_CTOR=4,SHARE_ARRAY=5,SHARE_BYTES=6,SHARE_OPAQUE=7;
    private static final int MAX_SHARE_WORK=8_000_000,MAX_SHARE_FRAMES=100_000,MAX_SHARE_ENTRIES=100_000,
            MAX_SHARE_STRING=65_536,MAX_SHARE_INTEGER_BITS=65_536,MAX_SHARE_BYTES=1_048_576;
    private static final long MAX_SHARE_OUTPUT_BYTES=32L*1024*1024;
    /** Table/identity aliases own no guest credits. Fresh candidates and result
     * flags designate occurrences; zero-shell disposal transfers to ACTION_RELEASE. */
    private static final class ShareState {
        final ArrayDeque<ShareFrame> frames=new ArrayDeque<>();
        final IdentityHashMap<Node,Node> memo=new IdentityHashMap<>();
        final IdentityHashMap<Node,Boolean> active=new IdentityHashMap<>();
        final IdentityHashMap<Object,Integer> identities=new IdentityHashMap<>();
        final HashMap<Integer,ArrayList<Object>> canonical=new HashMap<>();
        Object input,result;
        boolean resultOwned,discarding;
        int nextIdentity=1,entries;
        long work,outputBytes;
    }
    private static final class ShareFrame {
        Object input,representative;
        Node candidate;
        int kind,stage,cursor,scalarCursor,hash,bucketCursor,compareCursor;
        boolean memoEligible,candidateOwned;
        ShareFrame(Object input) { this.input=input; }
    }
    private static void shareCharge(ShareState state,int amount) {
        require(amount>=0&&amount<=MAX_SHARE_WORK-state.work,"ShareCommon work outside bounded JVM layout profile");
        long before=state.work; state.work+=amount;
        if((before>>>10)!=(state.work>>>10)&&Thread.currentThread().isInterrupted())
            throw error("ShareCommon interrupted outside bounded JVM layout profile");
    }
    private int shareKind(Object value) {
        validateHostObject(value);
        if(value instanceof Long) return SHARE_LONG;
        if(value instanceof BigInteger) {
            require(value.getClass()==BigInteger.class,"ShareCommon requires exact immutable BigInteger");
            require(((BigInteger)value).bitLength()<=MAX_SHARE_INTEGER_BITS,"ShareCommon integer outside bounded JVM layout profile");
            return SHARE_INTEGER;
        }
        if(value instanceof String) {
            require(((String)value).length()<=MAX_SHARE_STRING,"ShareCommon String outside bounded JVM layout profile");
            return SHARE_STRING;
        }
        Node node=(Node)value;
        if(node.array) {
            require(!node.ref&&!node.readyTask&&node.closure==null&&node.tag==246&&node.scalars.length==0
                    &&kindMetadata(node) instanceof ArrayState,"Invalid ShareCommon Array storage");
            require(arrayState(node).size>=0&&arrayState(node).size<=node.fields.length&&node.fields.length<=MAX_ARRAY_CAPACITY,
                    "Invalid ShareCommon Array extent"); return SHARE_ARRAY;
        }
        if(isByteArray(node)) {
            require(!node.ref&&!node.readyTask&&node.closure==null&&node.tag==248&&node.fields.length==0,
                    "Invalid ShareCommon ByteArray storage");
            int size=((ByteArrayState)kindMetadata(node)).size;
            require(size>=0&&size<=node.scalars.length&&node.scalars.length<=MAX_SHARE_BYTES,
                    "ShareCommon ByteArray outside bounded JVM layout profile"); return SHARE_BYTES;
        }
        if(node.ref) {
            reference(node); require(!node.readyTask&&kindMetadata(node)==null,"Invalid ShareCommon Ref storage"); return SHARE_OPAQUE;
        }
        if(node.closure!=null) {
            require(!node.readyTask&&node.tag==245&&node.scalars.length==0,"Invalid ShareCommon closure storage");
            acceptsClosure(node); return SHARE_OPAQUE;
        }
        if(node.readyTask) { taskNode(node); return SHARE_OPAQUE; }
        if(isPromise(node)) { promiseNode(node); return SHARE_OPAQUE; }
        require(node.tag>=0&&node.tag<=243&&kindMetadata(node)==null&&node.fields.length<256&&node.scalars.length<1024
                &&(node.fields.length!=0||node.scalars.length!=0),"Unsupported ShareCommon Node kind/storage");
        return SHARE_CTOR;
    }
    private static void sharePush(ShareState state,Object input) {
        require(state.frames.size()<MAX_SHARE_FRAMES,"ShareCommon frames outside bounded JVM layout profile");
        state.frames.push(new ShareFrame(input));
    }
    private static int shareIdentity(ShareState state,Object value) {
        if(value instanceof Long) return 31+Long.hashCode((Long)value);
        Integer old=state.identities.get(value); if(old!=null) return old;
        require(state.identities.size()<MAX_SHARE_ENTRIES,"ShareCommon identities outside bounded JVM layout profile");
        int id=state.nextIdentity++; state.identities.put(value,id); return id;
    }
    private static boolean shareSameChild(Object left,Object right) {
        return left instanceof Long&&right instanceof Long?left.equals(right):left==right;
    }
    private void shareReturn(ShareState state,ShareFrame frame,Object result) {
        require(state.frames.peek()==frame&&!state.resultOwned,"Invalid ShareCommon result transfer");
        state.result=result; state.resultOwned=true; frame.candidateOwned=false;
        state.frames.pop();
    }
    private void shareHashStep(ShareState state,ShareFrame frame) {
        Object value=frame.candidate==null?frame.input:frame.candidate;
        if(frame.kind==SHARE_STRING) {
            String text=(String)value; int end=Math.min(text.length(),frame.cursor+256);
            for(;frame.cursor<end;frame.cursor++) {
                char c=text.charAt(frame.cursor);
                require(!Character.isHighSurrogate(c)||(frame.cursor+1<text.length()&&Character.isLowSurrogate(text.charAt(frame.cursor+1))),"Invalid Unicode in ShareCommon String");
                require(!Character.isLowSurrogate(c)||(frame.cursor>0&&Character.isHighSurrogate(text.charAt(frame.cursor-1))),"Invalid Unicode in ShareCommon String");
                frame.hash=31*frame.hash+c; shareCharge(state,1);
            }
            if(frame.cursor==text.length()) frame.stage=3;
        } else if(frame.kind==SHARE_INTEGER) {
            BigInteger integer=(BigInteger)value; shareCharge(state,1+(integer.bitLength()+31)/32);
            frame.hash=31*frame.hash+integer.hashCode(); frame.stage=3;
        } else if(frame.kind==SHARE_BYTES) {
            Node bytes=(Node)value; int size=((ByteArrayState)kindMetadata(bytes)).size;
            int end=Math.min(size,frame.cursor+1024);
            for(;frame.cursor<end;frame.cursor++) { frame.hash=31*frame.hash+Byte.toUnsignedInt(bytes.scalars[frame.cursor]); shareCharge(state,1); }
            if(frame.cursor==size) frame.stage=3;
        } else {
            Node node=(Node)value; int end=Math.min(node.fields.length,frame.cursor+64);
            for(;frame.cursor<end;frame.cursor++) { frame.hash=31*frame.hash+shareIdentity(state,node.fields[frame.cursor]); shareCharge(state,1); }
            if(frame.cursor==node.fields.length) {
                for(;frame.scalarCursor<node.scalars.length;frame.scalarCursor++) {
                    frame.hash=31*frame.hash+Byte.toUnsignedInt(node.scalars[frame.scalarCursor]); shareCharge(state,1);
                }
                frame.stage=3;
            }
        }
    }
    /** -1: unequal, 0: compare another bounded chunk, 1: equal. */
    private int shareCompare(ShareState state,ShareFrame frame,Object other) {
        Object value=frame.candidate==null?frame.input:frame.candidate;
        if(frame.kind==SHARE_STRING) {
            if(!(other instanceof String)||((String)value).length()!=((String)other).length()) return -1;
            String a=(String)value,b=(String)other; int end=Math.min(a.length(),frame.compareCursor+256);
            for(;frame.compareCursor<end;frame.compareCursor++) { shareCharge(state,1); if(a.charAt(frame.compareCursor)!=b.charAt(frame.compareCursor)) return -1; }
            return frame.compareCursor==a.length()?1:0;
        }
        if(frame.kind==SHARE_INTEGER) {
            if(other==null||other.getClass()!=BigInteger.class) return -1;
            shareCharge(state,1+(((BigInteger)value).bitLength()+31)/32); return value.equals(other)?1:-1;
        }
        if(!(other instanceof Node)) return -1;
        Node a=(Node)value,b=(Node)other;
        if(frame.kind==SHARE_BYTES) {
            if(!isByteArray(b)||a.scalars.length!=b.scalars.length) return -1;
            int size=((ByteArrayState)kindMetadata(a)).size;
            if(size!=((ByteArrayState)kindMetadata(b)).size) return -1;
            int end=Math.min(size,frame.compareCursor+1024);
            for(;frame.compareCursor<end;frame.compareCursor++) { shareCharge(state,1); if(a.scalars[frame.compareCursor]!=b.scalars[frame.compareCursor]) return -1; }
            return frame.compareCursor==size?1:0;
        }
        if(a.array!=b.array||a.tag!=b.tag||a.fields.length!=b.fields.length||a.scalars.length!=b.scalars.length
                ||b.ref||b.readyTask||b.closure!=null||isByteArray(b)||isPromise(b)) return -1;
        int total=a.fields.length+a.scalars.length,end=Math.min(total,frame.compareCursor+64);
        for(;frame.compareCursor<end;frame.compareCursor++) {
            int i=frame.compareCursor; shareCharge(state,1);
            if(i<a.fields.length?!shareSameChild(a.fields[i],b.fields[i]):a.scalars[i-a.fields.length]!=b.scalars[i-a.fields.length]) return -1;
        }
        return frame.compareCursor==total?1:0;
    }
    private void stepShareCommon(RuntimeAction action) {
        ShareState state=action.share; require(state!=null,"Missing ShareCommon traversal state"); shareCharge(state,1);
        if(state.frames.isEmpty()) {
            require(state.resultOwned,"Missing owned ShareCommon root result"); Object answer=state.result;
            action.output=answer; state.result=null; state.resultOwned=false; state.input=null;
            state.memo.clear(); state.active.clear(); state.identities.clear(); state.canonical.clear();
            action.share=null; action.arguments=null; finishAction(action,answer); return;
        }
        ShareFrame frame=state.frames.peek();
        if(frame.stage==0) {
            frame.kind=shareKind(frame.input); frame.hash=31+frame.kind;
            if(frame.kind==SHARE_LONG) { shareReturn(state,frame,frame.input); return; }
            if(frame.kind==SHARE_OPAQUE) {
                shareIdentity(state,frame.input); inc(frame.input,1); shareReturn(state,frame,frame.input); return;
            }
            if(frame.kind==SHARE_STRING||frame.kind==SHARE_INTEGER||frame.kind==SHARE_BYTES) {
                if(frame.kind==SHARE_BYTES) { Node bytes=(Node)frame.input;
                    frame.hash=31*(31*frame.hash+((ByteArrayState)kindMetadata(bytes)).size)+bytes.scalars.length; }
                frame.stage=2; return;
            }
            Node input=(Node)frame.input; frame.memoEligible=!exclusive(input);
            if(frame.memoEligible) {
                Node prior=state.memo.get(input);
                if(prior!=null) { inc(prior,1); shareReturn(state,frame,prior); return; }
            }
            require(!state.active.containsKey(input),"ShareCommon constructor/Array cycle outside bounded JVM layout profile");
            int fields=frame.kind==SHARE_ARRAY?arrayState(input).size:input.fields.length;
            long bytes=8L+8L*fields+input.scalars.length;
            require(bytes<=MAX_SHARE_OUTPUT_BYTES-state.outputBytes,"ShareCommon output outside bounded JVM layout profile");
            // Publish candidate owner before any child traversal/acquisition.
            frame.candidate=frame.kind==SHARE_ARRAY?newArray(fields,fields):new Node(input.tag,fields,input.scalars.length);
            if(frame.kind==SHARE_CTOR) allocations++;
            frame.candidateOwned=true; state.outputBytes+=bytes; state.active.put(input,Boolean.TRUE);
            frame.hash=31*(31*(31*frame.hash+input.tag)+fields)+input.scalars.length;
            frame.stage=1; return;
        }
        if(frame.stage==1) {
            if(state.resultOwned) {
                require(frame.cursor<frame.candidate.fields.length,"Unexpected ShareCommon child result");
                frame.candidate.fields[frame.cursor]=state.result; state.result=null; state.resultOwned=false; frame.cursor++; return;
            }
            if(frame.cursor<frame.candidate.fields.length) { sharePush(state,((Node)frame.input).fields[frame.cursor]); return; }
            if(frame.kind==SHARE_CTOR) System.arraycopy(((Node)frame.input).scalars,0,frame.candidate.scalars,0,frame.candidate.scalars.length);
            frame.cursor=0; frame.stage=2; return;
        }
        if(frame.stage==2) { shareHashStep(state,frame); return; }
        if(frame.stage==3) {
            ArrayList<Object> bucket=state.canonical.get(frame.hash);
            if(bucket==null||frame.bucketCursor==bucket.size()) {
                require(state.entries<MAX_SHARE_ENTRIES,"ShareCommon canonical set outside bounded JVM layout profile");
                Object value=frame.candidate==null?frame.input:frame.candidate;
                if(bucket==null) { bucket=new ArrayList<>(); state.canonical.put(frame.hash,bucket); }
                bucket.add(value); state.entries++; frame.representative=value; frame.stage=5; return;
            }
            Object other=bucket.get(frame.bucketCursor); int equal=shareCompare(state,frame,other);
            if(equal==0) return;
            if(equal<0) { frame.bucketCursor++; frame.compareCursor=0; return; }
            frame.representative=other;
            if(frame.candidate!=null) {
                require(frame.candidateOwned&&frame.candidate.rc==1,"Invalid ShareCommon duplicate owner");
                frame.stage=4; state.discarding=true;
                // Native-order disposal is budgeted. The parent marks this as
                // a quiet proof; stepRelease rejects reaching any opaque zero.
                beginRelease(frame.candidate,1,ACTION_BODY,true); frame.candidateOwned=false; return;
            }
            frame.stage=5; return;
        }
        if(frame.stage==4) { state.discarding=false; frame.stage=5; }
        require(frame.stage==5,"Invalid ShareCommon traversal stage");
        Object result=frame.representative;
        if(result!=frame.candidate) inc(result,1);
        // Record the result owner before memo/identity-table allocation can fail.
        state.result=result; state.resultOwned=true; frame.candidateOwned=false;
        shareIdentity(state,result);
        if(frame.candidate!=null) {
            if(frame.memoEligible) {
                require(state.memo.size()<MAX_SHARE_ENTRIES,"ShareCommon memo outside bounded JVM layout profile");
                state.memo.put((Node)frame.input,(Node)result);
            }
            state.active.remove((Node)frame.input);
        }
        state.frames.pop();
    }

    private static final int MAX_FIND_ENCOUNTERS=1_000_000,MAX_FIND_PENDING=100_000,MAX_FIND_VISITED=100_000;
    /** All graph cursors/keys are BORROWED, backed by the suspended caller.
     * Only the flagged acquisition packet, receiver slot, and found/option
     * escrows can own credits. Once AP starts its existing packet is authoritative. */
    private static final class FindState {
        Node predicate,root,current,found,option;
        final ArrayDeque<Object> pending=new ArrayDeque<>();
        final ArrayDeque<Boolean> functionSpines=new ArrayDeque<>();
        boolean extended;
        final IdentityHashMap<Node,Boolean> visited=new IdentityHashMap<>();
        Object[] packet;
        long encounters;
        int stage;
        boolean predicateCredit,currentCredit,callbackStarted,receiverOwned,foundOwned;
    }
    private static final int MAX_LEVEL_INSTANTIATION_FRAMES=100_000,
            MAX_LEVEL_INSTANTIATION_CACHE=100_000,MAX_LEVEL_INSTANTIATION_SAVED=100_000;
    /** Exactly one control-owned occurrence when owned=true; other references
     * to this credit object are aliases. Never stored in guest Node metadata. */
    private static final class LevelCredit {
        Object value; boolean owned;
        LevelCredit(Object value,boolean owned) { this.value=value; this.owned=owned; }
    }
    private static final class LevelFrame {
        Object original,name;
        int tag,stage,cleanup;
        boolean shared,active,cached;
        LevelCredit left,right,option,assignment,result;
        LevelFrame(Object original) { this.original=original; }
    }
    private static final class LevelPacket {
        Function function; int role;
        Object[] arguments; boolean[] owned;
        boolean entryStarted,entered;
        LevelFrame frame;
    }
    private static final int LS_IDLE=0,LS_RUNNING=1,LS_RESULT=2,LS_SEALED=3,LS_DRAINING=4,LS_DRAINED=5;
    /** Borrowed input/key lifetimes extend through seal; only values/saved
     * assignments own. The context cell is shared, never a second owner. */
    private static final class LevelSession {
        MVarContextCell context;
        InstantiationBudget budget;
        LevelInstantiationPolicy policy;
        final ArrayDeque<LevelFrame> frames=new ArrayDeque<>();
        final IdentityHashMap<Node,LevelCredit> cache=new IdentityHashMap<>();
        // cacheValues indexes the SAME owned credit objects as cache.
        final ArrayList<LevelCredit> cacheValues=new ArrayList<>(),saved=new ArrayList<>();
        final IdentityHashMap<Node,Boolean> active=new IdentityHashMap<>();
        LevelPacket call;
        LevelCredit result,retiring;
        int phase,drainStage,drainCursor;
    }
    private static final class LevelInstantiationState {
        LevelSession session;
        LevelCredit input,result,pair;
        int stage,pairFields;
    }
    /** Both helper entry commit points call this AFTER publication and BEFORE
     * tick/guest work. Until then the native packet remains the owner escrow. */
    private void actionHelperEntry(Function function,Object[] arguments) {
        levelHelperEntry(function,arguments);
        directHelperEntry(function,arguments);
        delayedHelperEntry(function,arguments);
        RuntimeAction action=runtimeAction;
        if(action==null) return;
        ExprPacket packet=action.exprMachinery==null?null:action.exprMachinery.call;
        ExprDirectSession direct=currentDirectSession(action);
        if(direct!=null) { require(packet==null,"Multiple current Expr constructor packets"); packet=direct.constructorCall; }
        DelayedSession delayed=currentDelayedSession(action);
        if(delayed!=null) { require(packet==null,"Multiple current delayed constructor packets"); packet=delayed.constructorCall; }
        if(packet==null||packet.entered||packet.function!=function||packet.arguments!=arguments) return;
        require(packet.started,"Expr constructor entered before packet publication");
        packet.entered=true; Arrays.fill(packet.owned,false);
    }
    private void levelHelperEntry(Function function,Object[] arguments) {
        RuntimeAction action=runtimeAction;
        LevelSession session=currentLevelSession(action);
        if(session==null) return;
        LevelPacket packet=session.call;
        if(packet==null||packet.entered||packet.function!=function||packet.arguments!=arguments) return;
        require(packet.entryStarted,"Level helper entered before packet publication");
        packet.entered=true; Arrays.fill(packet.owned,false);
    }
    private static final int LF_ENTER=0,LF_LEFT=1,LF_RIGHT=2,LF_GET=3,LF_ASSIGN=4,LF_ASSIGNED=5,LF_SET=6,LF_BUILD=7,LF_FINISH=8,LF_CLEAN=9;
    private void levelWork(LevelSession state,long amount) {
        instantiationWork(state.budget,amount,"Level instantiation work outside bounded runtime profile","Level instantiation interrupted");
    }
    private static boolean sameLevel(Object a,Object b) {
        return a==b||a instanceof Long&&b instanceof Long&&((Long)a)==0&&((Long)b)==0;
    }
    private long levelWord(Object value) { Node node=levelNode(value); return node==null?2221:readScalar(node,0,U64); }
    private boolean levelHasMVar(Object value) { return (levelWord(value)&(1L<<32))!=0; }
    private boolean instantiatedLevelEqual(LevelSession state,Object left,Object right) {
        ExprEquality comparison=new ExprEquality(false); comparison.work=state.budget.work;
        try { return comparison.applyLevel(left,right); }
        finally { state.budget.work=comparison.work; }
    }
    private static final class LevelOffset {
        final Object base; final int offset;
        LevelOffset(Object base,int offset) { this.base=base; this.offset=offset; }
    }
    private LevelOffset levelOffset(LevelSession state,Object value) {
        IdentityHashMap<Node,Boolean> seen=new IdentityHashMap<>(); int offset=0;
        while(true) {
            levelWork(state,1); Node node=levelNode(value);
            if(node==null||node.tag!=1) return new LevelOffset(value,offset);
            require(seen.size()<MAX_LEVEL_INSTANTIATION_FRAMES&&!seen.containsKey(node),"Level instantiation offset cycle/depth outside profile");
            seen.put(node,Boolean.TRUE); value=node.fields[0]; offset++;
        }
    }
    private boolean levelNotZero(LevelSession state,Object value) {
        ArrayDeque<Object[]> todo=new ArrayDeque<>(); IdentityHashMap<Node,Boolean> seen=new IdentityHashMap<>();
        todo.push(new Object[]{value,Boolean.FALSE});
        while(!todo.isEmpty()) {
            levelWork(state,1); Object[] item=todo.pop(); Node node=levelNode(item[0]);
            if(node==null) continue;
            if(item[1]==Boolean.TRUE) { seen.put(node,Boolean.TRUE); continue; }
            if(node.tag==1) return true;
            if(node.tag==4||node.tag==5) continue;
            Boolean prior=seen.get(node);
            require(prior!=Boolean.FALSE,"Level instantiation nonzero cycle outside profile");
            if(prior==Boolean.TRUE) continue;
            require(seen.size()<MAX_LEVEL_INSTANTIATION_FRAMES&&todo.size()<MAX_LEVEL_INSTANTIATION_FRAMES-3,
                    "Level instantiation nonzero stack outside profile");
            seen.put(node,Boolean.FALSE); todo.push(new Object[]{node,Boolean.TRUE});
            if(node.tag==2) todo.push(new Object[]{node.fields[1],Boolean.FALSE});
            todo.push(new Object[]{node.fields[node.tag==3?1:0],Boolean.FALSE});
        }
        return false;
    }
    private boolean levelOne(LevelSession state,Object value) {
        levelWork(state,1); Node node=levelNode(value);
        return node!=null&&node.tag==1&&sameLevel(node.fields[0],ERASED)
                &&(int)readScalar(node,0,U64)==(int)mixHash(2243,2221)&&(readScalar(node,0,U64)>>>40)==1;
    }
    /** Null means call the raw constructor. Every nonnull selection is borrowed. */
    private Object smartLevelMax(LevelSession state,Object left,Object right) {
        LevelOffset x=levelOffset(state,left),y=null;
        if(sameLevel(x.base,ERASED)) {
            y=levelOffset(state,right);
            if(sameLevel(y.base,ERASED)) return (levelWord(left)>>>40)>=(levelWord(right)>>>40)?left:right;
        }
        if(instantiatedLevelEqual(state,left,right)) return left;
        if(sameLevel(left,ERASED)) return right;
        if(sameLevel(right,ERASED)) return left;
        Node a=levelNode(left),b=levelNode(right);
        if(b.tag==2&&(instantiatedLevelEqual(state,b.fields[0],left)||instantiatedLevelEqual(state,b.fields[1],left))) return right;
        if(a.tag==2&&(instantiatedLevelEqual(state,a.fields[0],right)||instantiatedLevelEqual(state,a.fields[1],right))) return left;
        if(y==null) y=levelOffset(state,right);
        if(instantiatedLevelEqual(state,x.base,y.base)) {
            require(x.offset!=y.offset,"Level instantiation inconsistent equal offsets outside profile");
            return x.offset>y.offset?left:right;
        }
        return null;
    }
    private Object smartLevelIMax(LevelSession state,Object left,Object right,boolean nonzero) {
        if(nonzero) return smartLevelMax(state,left,right);
        if(sameLevel(right,ERASED)||sameLevel(left,ERASED)||levelOne(state,left)) return right;
        if(instantiatedLevelEqual(state,left,right)) return left;
        return null;
    }
    private LevelCredit retainedLevel(LevelSession state,Object value) {
        levelWork(state,1); LevelCredit credit=new LevelCredit(value,false);
        // Caller must publish the credit BEFORE invoking inc; this routine is
        // used only where the resulting credit is immediately stored below.
        return credit;
    }
    private void ownLevelCredit(LevelCredit credit) { inc(credit.value,1); credit.owned=true; }
    private void pushLevelFrame(LevelSession state,Object original) {
        require(state.frames.size()<MAX_LEVEL_INSTANTIATION_FRAMES,"Level instantiation frame limit");
        state.frames.addLast(new LevelFrame(original));
    }
    private void validateLevelArguments(Function function,Object[] args) {
        levelInstantiationProfile(function);
        require(args!=null&&args.length==2,"Level instantiation native arity mismatch");
        validateHostObject(args[0]); levelNode(args[1]);
        if(args[0]==args[1]&&args[0] instanceof Node) {
            Node node=(Node)args[0]; require(node.rc==0||node.rc>=2,"Insufficient aliased Level instantiation input credits");
        }
    }
    private void checkLevelPacket(LevelPacket packet) {
        IdentityHashMap<Node,Integer> credits=new IdentityHashMap<>();
        for(int i=0;i<packet.arguments.length;i++) {
            require(packet.owned[i],"Level helper packet argument is not owned"); validateHostObject(packet.arguments[i]);
            if(packet.arguments[i] instanceof Node) credits.merge((Node)packet.arguments[i],1,Integer::sum);
        }
        for(Map.Entry<Node,Integer> item:credits.entrySet())
            require(item.getKey().rc==0||item.getKey().rc>=item.getValue(),"Insufficient Level helper packet alias credits");
    }
    private void callLevelHelper(RuntimeAction action,LevelSession state,LevelFrame frame,int role) {
        levelWork(state,1); require(state.call==null&&objects[action.slot]==null,"Level helper receiver already occupied");
        Function helper=levelInstantiationHelper(state.policy,role);
        int arity=role==0||role>=3?2:role==1?3:1;
        LevelPacket packet=new LevelPacket(); packet.function=helper; packet.role=role; packet.frame=frame;
        packet.arguments=new Object[arity]; packet.owned=new boolean[arity]; state.call=packet;
        if(role==0||role==1) {
            require(state.context.current!=null&&state.context.current.owned,"Level helper lacks current context owner");
            packet.arguments[0]=state.context.current.value;
            if(role==1) { packet.owned[0]=true; state.context.current.owned=false; state.context.current=null; }
            else { inc(packet.arguments[0],1); packet.owned[0]=true; }
            nameNode(frame.name); packet.arguments[1]=frame.name; inc(frame.name,1); packet.owned[1]=true;
            if(role==1) { packet.arguments[2]=frame.result.value; inc(packet.arguments[2],1); packet.owned[2]=true; }
        } else {
            packet.arguments[0]=frame.left.value; inc(packet.arguments[0],1); packet.owned[0]=true;
            if(arity==2) { packet.arguments[1]=frame.right.value; inc(packet.arguments[1],1); packet.owned[1]=true; }
        }
        checkLevelPacket(packet); packet.entryStarted=true;
        enterExplicit(helper,null,packet.arguments,ACTION_BODY,action.slot,ASSIGN,null);
        require(packet.entered,"Level helper did not publish a frame or CodeRequest");
    }
    private void receiveLevelHelper(RuntimeAction action,LevelSession state) {
        LevelPacket packet=state.call; require(packet.entered,"Level helper has not committed entry");
        Object value=objects[action.slot]; LevelFrame frame=packet.frame;
        // The existing receiver slot owns VALUE already, even before any local
        // flag is set. Invalid results remain there on terminal failure.
        if(packet.role==0) {
            if(!sameLevel(value,ERASED)) {
                Node option=constructorNode(value);
                require(option.closure==null&&option.tag==1&&option.fields.length==1&&option.scalars.length==0,"Level getter returned malformed Option");
                levelNode(option.fields[0]);
            }
            frame.option=new LevelCredit(value,true); objects[action.slot]=null; state.call=null;
            if(sameLevel(value,ERASED)) {
                frame.result=retainedLevel(state,frame.original); ownLevelCredit(frame.result); frame.stage=LF_FINISH;
            } else {
                Object assigned=((Node)value).fields[0];
                frame.assignment=retainedLevel(state,assigned); ownLevelCredit(frame.assignment);
                if(!levelHasMVar(assigned)) { frame.result=frame.assignment; frame.assignment=null; frame.stage=LF_FINISH; }
                else { frame.stage=LF_ASSIGN; pushLevelFrame(state,assigned); }
            }
        } else if(packet.role==1) {
            validateHostObject(value); require(state.context.current==null,"Level setter would replace a live context owner");
            state.context.current=new LevelCredit(value,true); objects[action.slot]=null; state.call=null; frame.stage=LF_FINISH;
        } else {
            Node level=levelNode(value); int tag=packet.role==2?1:packet.role==3?2:3;
            require(level!=null&&level.tag==tag&&sameLevel(level.fields[0],packet.arguments[0])
                    &&(tag==1||sameLevel(level.fields[1],packet.arguments[1])),"Original Level constructor returned unexpected head/children");
            frame.result=new LevelCredit(value,true); objects[action.slot]=null; state.call=null; frame.stage=LF_FINISH;
        }
    }
    private boolean releaseLevelCredit(RuntimeAction action,LevelSession state,LevelCredit credit) {
        if(credit==null||!credit.owned) return false;
        state.retiring=credit; action.retiring=credit.value; action.releaseClaimed=false;
        boolean dispatch;
        try { dispatch=beginRelease(credit.value,1,ACTION_BODY); credit.owned=false; }
        finally { if(action.releaseClaimed) credit.owned=false; }
        if(!dispatch) { state.retiring=null; action.retiring=null; action.releaseClaimed=false; }
        return dispatch;
    }
    private void completeLevelFrame(LevelSession state,LevelFrame frame) {
        require(frame.result!=null&&frame.result.owned,"Level frame has no owned result");
        if(frame.active) state.active.remove((Node)frame.original);
        require(state.frames.removeLast()==frame,"Level frame stack differs");
        LevelCredit result=frame.result; frame.result=null;
        frame.original=null; frame.name=null; frame.left=null; frame.right=null; frame.assignment=null; frame.option=null;
        if(state.frames.isEmpty()) { state.result=result; state.phase=LS_RESULT; return; }
        LevelFrame parent=state.frames.peekLast();
        if(parent.stage==LF_LEFT) parent.left=result;
        else if(parent.stage==LF_RIGHT) parent.right=result;
        else if(parent.stage==LF_ASSIGN) { parent.result=result; parent.stage=LF_ASSIGNED; }
        else throw error("Level instantiation child continuation differs");
    }
    private void stepLevelJob(RuntimeAction action,LevelSession state) {
        require(state.phase==LS_RUNNING,"Level session has no running job"); levelWork(state,1);
        if(state.retiring!=null) {
            require(!state.retiring.owned,"Level cleanup returned without claiming retiring owner");
            state.retiring=null; action.retiring=null; action.releaseClaimed=false;
        }
        if(state.call!=null) { receiveLevelHelper(action,state); return; }
        {
            LevelFrame frame=state.frames.peekLast(); require(frame!=null,"Missing Level traversal frame");
            if(frame.stage==LF_ENTER) {
                Node node=levelNode(frame.original); frame.tag=node==null?0:node.tag;
                if(!levelHasMVar(frame.original)) {
                    frame.result=retainedLevel(state,frame.original); ownLevelCredit(frame.result); frame.stage=LF_FINISH; return;
                }
                require(node!=null&&node.tag!=4,"Inconsistent Level hasMVar cache on Zero/Param");
                frame.shared=!exclusive(node);
                LevelCredit cached=frame.shared?state.cache.get(node):null;
                if(cached!=null) {
                    require(cached.owned,"Level cache value owner is missing");
                    frame.result=retainedLevel(state,cached.value); ownLevelCredit(frame.result); frame.cached=true; frame.stage=LF_FINISH; return;
                }
                require(!state.active.containsKey(node),"Level instantiation assignment/structural cycle outside profile");
                state.active.put(node,Boolean.TRUE); frame.active=true;
                if(node.tag==5) { frame.name=node.fields[0]; frame.stage=LF_GET; callLevelHelper(action,state,frame,0); }
                else { frame.stage=LF_LEFT; pushLevelFrame(state,node.fields[0]); }
                return;
            }
            if(frame.stage==LF_LEFT) {
                require(frame.left!=null&&frame.left.owned,"Level left result missing");
                if(frame.tag==1) frame.stage=LF_BUILD;
                else { frame.stage=LF_RIGHT; pushLevelFrame(state,((Node)frame.original).fields[1]); }
                return;
            }
            if(frame.stage==LF_RIGHT) frame.stage=LF_BUILD;
            if(frame.stage==LF_BUILD) {
                Node original=(Node)frame.original; Object selected; int role=frame.tag==1?2:frame.tag==2?3:4;
                if(sameLevel(frame.left.value,original.fields[0])&&(frame.tag==1||sameLevel(frame.right.value,original.fields[1]))) selected=original;
                else if(frame.tag==1) selected=null;
                else if(frame.tag==2) selected=smartLevelMax(state,frame.left.value,frame.right.value);
                else {
                    boolean nonzero=levelNotZero(state,frame.right.value); if(nonzero) role=3;
                    selected=smartLevelIMax(state,frame.left.value,frame.right.value,nonzero);
                }
                if(selected!=null) { frame.result=retainedLevel(state,selected); ownLevelCredit(frame.result); frame.stage=LF_FINISH; }
                else callLevelHelper(action,state,frame,role);
                return;
            }
            if(frame.stage==LF_ASSIGNED) {
                if(sameLevel(frame.assignment.value,frame.result.value)) frame.stage=LF_FINISH;
                else {
                    require(state.saved.size()<MAX_LEVEL_INSTANTIATION_SAVED,"Level instantiation saved-assignment limit");
                    LevelCredit saved=retainedLevel(state,frame.assignment.value); state.saved.add(saved); ownLevelCredit(saved);
                    frame.stage=LF_SET; callLevelHelper(action,state,frame,1);
                }
                return;
            }
            if(frame.stage==LF_FINISH) {
                if(frame.tag>=1&&frame.tag<=3&&frame.shared&&!frame.cached) {
                    require(state.cache.size()<MAX_LEVEL_INSTANTIATION_CACHE&&!state.cache.containsKey((Node)frame.original),"Level instantiation cache limit/duplicate");
                    LevelCredit cached=retainedLevel(state,frame.result.value);
                    state.cache.put((Node)frame.original,cached); state.cacheValues.add(cached); ownLevelCredit(cached); frame.cached=true;
                }
                frame.stage=LF_CLEAN; frame.cleanup=0;
            }
            if(frame.stage==LF_CLEAN) {
                if(frame.cleanup<4) {
                    LevelCredit credit=frame.cleanup==0?frame.right:frame.cleanup==1?frame.left:frame.cleanup==2?frame.assignment:frame.option;
                    frame.cleanup++; releaseLevelCredit(action,state,credit); return;
                }
                completeLevelFrame(state,frame); return;
            }
            throw error("Level instantiation helper continuation did not return");
        }
    }
    private LevelSession newLevelSession(MVarContextCell context,InstantiationBudget budget,LevelInstantiationPolicy policy) {
        require(context!=null&&context.current!=null&&context.current.owned&&budget!=null&&policy!=null,"Level session requires current context owner, budget and policy");
        for(int role=0;role<5;role++) levelInstantiationHelper(policy,role);
        LevelSession session=new LevelSession(); session.context=context; session.budget=budget; session.policy=policy; return session;
    }
    private LevelSession currentLevelSession(RuntimeAction action) {
        return action==null?null:action.levelMvars!=null?action.levelMvars.session:
                action.mvarSessionResearch!=null?action.mvarSessionResearch.session:
                currentDirectSession(action)!=null?currentDirectSession(action).levels:null;
    }
    /** Caller anchors all original cache keys through seal. No input retain. */
    private void startLevelJob(LevelSession session,Object borrowedInput) {
        require(session.phase==LS_IDLE&&session.result==null&&session.call==null&&session.retiring==null
                &&session.frames.isEmpty()&&session.active.isEmpty(),"Level session is not idle for a new job");
        require(session.context.current!=null&&session.context.current.owned,"Level session context owner is absent");
        levelNode(borrowedInput);
        for(int role=0;role<5;role++) levelInstantiationHelper(session.policy,role);
        pushLevelFrame(session,borrowedInput); session.phase=LS_RUNNING;
    }
    private LevelCredit takeLevelJobResult(LevelSession session) {
        require(session.phase==LS_RESULT&&session.result!=null&&session.result.owned&&session.call==null&&session.retiring==null
                &&session.frames.isEmpty()&&session.active.isEmpty(),"Level session has no completed owned result");
        LevelCredit result=session.result; session.result=null; session.phase=LS_IDLE; return result;
    }
    private void sealLevelSession(LevelSession session) {
        require(session.phase==LS_IDLE&&session.result==null&&session.call==null&&session.retiring==null
                &&session.frames.isEmpty()&&session.active.isEmpty(),"Level session must be idle with result taken before seal");
        session.cache.clear(); session.active.clear(); session.phase=LS_SEALED;
    }
    private void resumeLevelRetiring(RuntimeAction action,LevelSession session) {
        if(session.retiring!=null) {
            require(!session.retiring.owned,"Level cleanup returned without claiming retiring owner");
            session.retiring=null; action.retiring=null; action.releaseClaimed=false;
        }
    }
    /** Drain only this worker's saved/cache owners; never consume its shared cell. */
    private void stepLevelSessionDrain(RuntimeAction action,LevelSession session) {
        require(session.phase==LS_SEALED||session.phase==LS_DRAINING,"Level session is not sealed for drain");
        levelWork(session,1); resumeLevelRetiring(action,session);
        session.phase=LS_DRAINING;
        if(session.drainStage==0) {
            if(session.drainCursor<session.saved.size()) {
                LevelCredit credit=session.saved.get(session.saved.size()-1-session.drainCursor++);
                releaseLevelCredit(action,session,credit); return;
            }
            session.drainStage=1; session.drainCursor=0;
        }
        if(session.drainStage==1) {
            if(session.drainCursor<session.cacheValues.size()) {
                LevelCredit credit=session.cacheValues.get(session.cacheValues.size()-1-session.drainCursor++);
                releaseLevelCredit(action,session,credit); return;
            }
            session.drainStage=2;
        }
        require(session.retiring==null&&session.cache.isEmpty()&&session.active.isEmpty(),"Level session drain retains a pending cursor");
        session.saved.clear(); session.cacheValues.clear(); session.phase=LS_DRAINED;
    }
    private void stepLevelInstantiation(RuntimeAction action) {
        LevelInstantiationState state=action.levelMvars; require(state!=null,"Missing Level instantiation state");
        LevelSession session=state.session;
        if(state.stage==0) {
            stepLevelJob(action,session);
            if(session.phase==LS_RESULT) { state.result=takeLevelJobResult(session); state.stage=1; }
            return;
        }
        if(state.stage==3||state.stage==4) {
            stepLevelSessionDrain(action,session);
            state.stage=session.phase==LS_DRAINED?5:session.drainStage==0?3:4;
            if(state.stage!=5) return;
        } else { levelWork(session,1); resumeLevelRetiring(action,session); }
        if(state.stage==1) {
            require(session.context.current!=null&&session.context.current.owned&&state.result!=null&&state.result.owned,"Level result/context owners missing");
            Node pair=new Node(0,2,0); state.pair=new LevelCredit(pair,true); allocations++;
            pair.fields[0]=session.context.current.value; session.context.current.owned=false; session.context.current=null; state.pairFields=1;
            pair.fields[1]=state.result.value; state.result.owned=false; state.pairFields=2;
            // No pause/tick/helper can observe a restartable session after ctx transfer.
            sealLevelSession(session); state.stage=2; return;
        }
        if(state.stage==2) { state.stage=3; releaseLevelCredit(action,session,state.input); return; }
        require(state.stage==5&&session.phase==LS_DRAINED&&state.pair!=null&&state.pair.owned&&state.pairFields==2,"Incomplete Level instantiation pair");
        Object pair=state.pair.value; action.output=pair; state.pair.owned=false;
        state.input=null; state.result=null; state.pair=null; action.arguments=null; action.levelMvars=null; finishAction(action,pair);
    }
    private static final boolean MVAR_SESSION_RESEARCH_READY=true;
    private static final int MB_LEVEL0=0,MB_TAKE0=1,MB_ENTER_EXPR=2,MB_WAIT_EXPR=3,MB_START1=4,
            MB_LEVEL1=5,MB_TAKE1=6,MB_OUTPUT=7,MB_RELEASE_INPUTS=8,MB_DRAIN=9,MB_FINISH=10;
    private static final class MVarSessionResearchState {
        MVarContextCell context;
        InstantiationBudget budget;
        LevelSession session;
        ExprConstructorPolicy exprPolicy;
        final LevelCredit[] inputs=new LevelCredit[2],levels=new LevelCredit[2];
        ExprCredit exprInput,exprResult;
        LevelCredit output;
        int stage,cursor,outputFields,liftAmount;
    }
    /** Private fixed mixed-worker test caller, not an original Lean ABI. */
    private void startMVarSessionResearch(Header[] exprHeaders,Object ownedContext,Object[] ownedLevels,Object ownedExpr,long liftAmount) {
        explicitOnly(); require(MVAR_SESSION_RESEARCH_READY,"Private mixed MVar session is not yet enabled");
        require(taskRuntime!=null,"Private mixed MVar session requires active explicit runtime");
        if(closed||disposed||untrackedFailure||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||continuationDepth!=0
                ||runtimeAction!=null||hostCompletion!=null||hostGuestRecord!=null||quietCurrent!=null||releasePending!=0
                ||releaseTransaction!=null||releaseRoot)
            throw new IllegalStateException("Private mixed MVar session requires an open idle engine");
        require(levelInstantiationPolicy!=null,"Private mixed MVar session requires original Level policy");
        require(ownedLevels!=null&&ownedLevels.length==2,"Private mixed MVar session requires two owned Level anchors");
        require(liftAmount>=0&&liftAmount<=MAX_EXPR_JOB_OFFSET,"Private mixed MVar lift amount outside profile");
        ExprConstructorPolicy policy=ExprConstructorPolicy.originalHeaders(exprHeaders);
        require(policy.helpers[0].source==levelInstantiationPolicy.helpers[0].source,"Mixed MVar helper source bindings differ");
        for(int role=0;role<9;role++) exprConstructor(policy,role);
        for(int role=0;role<5;role++) levelInstantiationHelper(levelInstantiationPolicy,role);
        validateHostObject(ownedContext); levelNode(ownedLevels[0]); levelNode(ownedLevels[1]); exprNode(ownedExpr);
        IdentityHashMap<Node,Integer> owners=new IdentityHashMap<>();
        for(Object value:new Object[]{ownedContext,ownedLevels[0],ownedLevels[1],ownedExpr})
            if(value instanceof Node) owners.merge((Node)value,1,Integer::sum);
        for(Map.Entry<Node,Integer> item:owners.entrySet())
            require(item.getKey().rc==0||item.getKey().rc>=item.getValue(),"Private mixed MVar input alias credits differ");
        RuntimeAction action=newAction(ACTION_MVAR_SESSION_RESEARCH,null,null,0,ROOT,null);
        MVarSessionResearchState state=new MVarSessionResearchState(); state.context=new MVarContextCell();
        state.context.current=new LevelCredit(ownedContext,true); state.budget=new InstantiationBudget();
        state.session=newLevelSession(state.context,state.budget,levelInstantiationPolicy); state.exprPolicy=policy;
        state.inputs[0]=new LevelCredit(ownedLevels[0],true); state.inputs[1]=new LevelCredit(ownedLevels[1],true);
        state.exprInput=new ExprCredit(ownedExpr,true); state.liftAmount=(int)liftAmount;
        action.mvarSessionResearch=state; startLevelJob(state.session,ownedLevels[0]); objects[action.slot]=null;
        publishAction(action); callsLeft=10_000_000; instructions=0; entry=null; result=null; releaseRoot=false; phase=RUNNING;
    }
    private void enterMVarExprChild(RuntimeAction parent,MVarSessionResearchState state) {
        require(runtimeAction==parent&&state.stage==MB_WAIT_EXPR&&objects[parent.slot]==null,"Mixed MVar parent is not waiting for an empty Expr receiver");
        require(state.session.phase==LS_IDLE&&state.session.call==null&&state.session.retiring==null
                &&state.exprInput!=null&&state.exprInput.owned,"Mixed MVar Expr child input/session is not ready");
        for(int role=0;role<9;role++) exprConstructor(state.exprPolicy,role);
        exprNode(state.exprInput.value);
        RuntimeAction child=newAction(ACTION_EXPR_MACHINERY,null,ACTION_BODY,parent.slot,ASSIGN,null);
        ExprMachineryState worker=new ExprMachineryState(); worker.policy=state.exprPolicy; worker.budget=state.budget;
        worker.input=state.exprInput; pushReplaceJob(worker,EXPR_LIFT_JOB,worker.input.value,0,state.liftAmount,new Object[0]);
        child.exprMachinery=worker; objects[child.slot]=null;
        // One credit record is aliased during this atomic control handoff, not
        // copied/INC'd. No tick/helper/release occurs after publication and before clear.
        publishAction(child); state.exprInput=null;
    }
    private void stepMVarSessionResearch(RuntimeAction action) {
        MVarSessionResearchState state=action.mvarSessionResearch; require(state!=null,"Missing private mixed MVar session");
        instantiationWork(state.budget,1,"Mixed MVar session work outside bounded profile","Mixed MVar session interrupted");
        LevelSession session=state.session; resumeLevelRetiring(action,session);
        if(state.stage==MB_LEVEL0||state.stage==MB_LEVEL1) {
            stepLevelJob(action,session);
            if(session.phase==LS_RESULT) state.stage=state.stage==MB_LEVEL0?MB_TAKE0:MB_TAKE1;
            return;
        }
        if(state.stage==MB_TAKE0) { state.levels[0]=takeLevelJobResult(session); state.stage=MB_ENTER_EXPR; return; }
        if(state.stage==MB_ENTER_EXPR) { state.stage=MB_WAIT_EXPR; enterMVarExprChild(action,state); return; }
        if(state.stage==MB_WAIT_EXPR) {
            require(state.exprResult==null,"Mixed MVar Expr result receiver occupied");
            Object value=objects[action.slot]; exprNode(value);
            state.exprResult=new ExprCredit(value,true); objects[action.slot]=null; state.stage=MB_START1; return;
        }
        if(state.stage==MB_START1) { startLevelJob(session,state.inputs[1].value); state.stage=MB_LEVEL1; return; }
        if(state.stage==MB_TAKE1) { state.levels[1]=takeLevelJobResult(session); state.stage=MB_OUTPUT; return; }
        if(state.stage==MB_OUTPUT) {
            require(state.context.current!=null&&state.context.current.owned&&state.levels[0]!=null&&state.levels[0].owned
                    &&state.levels[1]!=null&&state.levels[1].owned&&state.exprResult!=null&&state.exprResult.owned,
                    "Mixed MVar output occurrences missing");
            Node output=new Node(0,4,0); state.output=new LevelCredit(output,true); allocations++;
            output.fields[0]=state.context.current.value; state.context.current.owned=false; state.context.current=null; state.outputFields=1;
            output.fields[1]=state.levels[0].value; state.levels[0].owned=false; state.outputFields=2;
            output.fields[2]=state.exprResult.value; state.exprResult.owned=false; state.outputFields=3;
            output.fields[3]=state.levels[1].value; state.levels[1].owned=false; state.outputFields=4;
            sealLevelSession(session); state.stage=MB_RELEASE_INPUTS; state.cursor=0; return;
        }
        if(state.stage==MB_RELEASE_INPUTS) {
            if(state.cursor<2) { LevelCredit credit=state.inputs[state.cursor++]; releaseLevelCredit(action,session,credit); return; }
            state.stage=MB_DRAIN;
        }
        if(state.stage==MB_DRAIN) {
            stepLevelSessionDrain(action,session); if(session.phase!=LS_DRAINED) return; state.stage=MB_FINISH;
        }
        require(state.stage==MB_FINISH&&session.phase==LS_DRAINED&&state.context.current==null&&state.exprInput==null
                &&state.output!=null&&state.output.owned&&state.outputFields==4,"Mixed MVar output is incomplete");
        Object output=state.output.value; state.output.owned=false; action.output=output;
        Arrays.fill(state.inputs,null); Arrays.fill(state.levels,null); state.exprResult=null; state.output=null;
        state.session=null; state.context=null; state.budget=null; action.mvarSessionResearch=null; finishAction(action,output);
    }
    private void validateFindCallback(Object value) {
        require(explicit&&taskRuntime!=null,"Expr.find requires the active explicit runtime");
        Node predicate=node(value); acceptsClosure(predicate);
        Function target=predicate.closure; rootEntry(target); requireExecutableAbi(target);
        require(predicate.tag==245&&!predicate.array&&!predicate.ref&&!predicate.readyTask
                &&predicate.scalars.length==0&&predicate.fields.length+1==target.params.length,
                "Expr.find requires a one-argument partial predicate closure");
        for(int lane:target.paramTypes) require(lane==OBJ,"Expr.find predicate requires boxed parameters");
        require(target.resultType==OBJ||target.resultType==U8,"Expr.find predicate requires a boxed Bool-compatible result");
        for(Object capture:predicate.fields) validateHostObject(capture);
        preflightCallable(target,true);
    }
    private void validateFind(Object[] args) {
        require(args!=null&&args.length==2,"Expr.find native arity mismatch");
        validateFindCallback(args[0]);
        require(node(args[0]).rc>=0&&exprNode(args[1]).rc>=0,"Invalid Expr.find borrowed owner counts");
    }
    private void pushFind(FindState state,Object value) { pushFind(state,value,false); }
    private void pushFind(FindState state,Object value,boolean functionSpine) {
        require(value!=null,"Null child outside Expr.find storage profile");
        require(state.pending.size()<MAX_FIND_PENDING,"Expr.find pending stack outside bounded runtime profile");
        state.pending.push(value); state.functionSpines.push(functionSpine);
    }
    private void finishFind(RuntimeAction action,Object answer) {
        // Publish result escrow before detaching all borrowed search history.
        action.output=answer; FindState state=action.find;
        state.predicate=null; state.root=null; state.current=null; state.found=null;
        state.option=null; state.packet=null; state.pending.clear(); state.functionSpines.clear(); state.visited.clear();
        state.foundOwned=false; action.find=null; action.arguments=null;
        finishAction(action,answer);
    }
    private void stepFind(RuntimeAction action) {
        FindState state=action.find; require(state!=null,"Missing Expr.find state");
        if(state.stage==0) {
            if(state.pending.isEmpty()) { finishFind(action,ERASED); return; }
            require(state.encounters<MAX_FIND_ENCOUNTERS,"Expr.find encounters outside bounded runtime profile");
            state.encounters++;
            if((state.encounters&1023)==0&&Thread.currentThread().isInterrupted())
                throw error("Expr.find interrupted outside bounded runtime profile");
            boolean functionSpine=state.functionSpines.pop();
            state.current=exprNode(state.pending.pop());
            require(state.current.rc>=0,"Invalid Expr.find current owner count");
            int tag=state.current.tag;
            // for_each_fn<false>::apply_fn traverses an App function spine
            // without callback or visited-cache lookup for intermediate Apps.
            if(functionSpine&&tag==5) {
                require(2<=MAX_FIND_PENDING-state.pending.size(),"Expr.find pending stack outside bounded runtime profile");
                pushFind(state,state.current.fields[1]); pushFind(state,state.current.fields[0],true);
                state.current=null; return;
            }
            // Native is_likely_unshared is RC +1/-1: logical MT does NOT
            // turn a unique positive Java count into a cached encounter.
            if(tag!=0&&tag!=3&&tag!=4&&state.current.rc!=1) {
                if(state.visited.containsKey(state.current)) { state.current=null; return; }
                require(state.visited.size()<MAX_FIND_VISITED,"Expr.find visited set outside bounded runtime profile");
                state.visited.put(state.current,Boolean.TRUE);
            }
            validateFindCallback(state.predicate);
            state.packet=new Object[]{state.current};
            inc(state.predicate,1); state.predicateCredit=true;
            inc(state.current,1); state.currentCredit=true;
            state.stage=1; state.callbackStarted=true;
            // AP publishes its owned input packet before any preparation or
            // guest execution. These flags now designate aliases, not owners.
            state.predicateCredit=false; state.currentCredit=false;
            applyExplicit(state.predicate,state.packet,ACTION_BODY,action.slot); return;
        }
        require(state.stage==1,"Invalid Expr.find continuation");
        Object answer=objects[action.slot]; state.receiverOwned=true;
        require(answer instanceof Long&&((Long)answer)>=0&&((Long)answer)<=(state.extended?2:1),
                state.extended?"Expr.findExt predicate did not return canonical FindStep":"Expr.find predicate did not return canonical boxed Bool");
        objects[action.slot]=null; state.receiverOwned=false; state.packet=null; state.callbackStarted=false;
        if(((Long)answer)==(state.extended?0:1)) {
            state.stage=2; state.found=state.current;
            inc(state.found,1); state.foundOwned=true;
            Node option=new Node(1,1,0); state.option=option; allocations++;
            option.fields[0]=state.found; state.foundOwned=false;
            finishFind(action,option); return;
        }
        if(state.extended&&((Long)answer)==2) { state.current=null; state.stage=0; return; }
        Node current=state.current;
        int children=current.tag==5||current.tag==6||current.tag==7?2:current.tag==8?3:current.tag==10||current.tag==11?1:0;
        require(children<=MAX_FIND_PENDING-state.pending.size(),"Expr.find pending stack outside bounded runtime profile");
        switch(current.tag) {
            case 5: pushFind(state,current.fields[1]); pushFind(state,current.fields[0],state.extended); break;
            case 6: case 7: pushFind(state,current.fields[2]); pushFind(state,current.fields[1]); break;
            case 8: pushFind(state,current.fields[3]); pushFind(state,current.fields[2]); pushFind(state,current.fields[1]); break;
            case 10: pushFind(state,current.fields[1]); break;
            case 11: pushFind(state,current.fields[2]); break;
            default: break;
        }
        state.current=null; state.stage=0;
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
            if(op==VOID_MK) { old=args[1]; action.output=ERASED; action.stage=2; }
            else if(op==REF_SET) {
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
        else if(action.operation==ACTION_FIND) stepFind(action);
        else if(action.operation==ACTION_SHARECOMMON) stepShareCommon(action);
        else if(action.operation==ACTION_LEVEL_MVARS) stepLevelInstantiation(action);
        else if(action.operation==ACTION_EXPR_MACHINERY||action.operation==ACTION_EXPR_REPLACE||action.operation==ACTION_EXPR_ABSTRACT||action.operation==ACTION_EXPR_PURE) stepExprMachinery(action);
        else if(action.operation==ACTION_MVAR_SESSION_RESEARCH) stepMVarSessionResearch(action);
        else if(action.operation==ACTION_EXPR_DIRECT_RESEARCH) stepExprDirectResearch(action);
        else if(action.operation==ACTION_DELAYED_FOUNDATION_RESEARCH) stepDelayedFoundationResearch(action);
        else if(action.operation==ACTION_EXPR_FULL_RESEARCH) stepExprFullResearch(action);
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
        if(closed||disposed||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||untrackedFailure
                ||pendingInitializerGlobal!=null||initializerFailed)
            throw new IllegalStateException("Initialization completion requires an open idle successful engine");
        initializing=false;
    }

    /** Begin one source-bound interpreted regular [init] pair. The trusted
     * adapter owns module order and must mark its module entered BEFORE calling.
     * Only the ordinary (World : void) -> object action ABI is admitted. This
     * does not eagerly evaluate ordinary nullary constants or run native init.
     * An attempted global is never replayed, including after IO.error. */
    public void startInitializer(Header global,Header action) {
        explicitOnly();
        require(initializing&&taskRuntime==null&&!initializerFailed,
                "Initializer requires a fresh task-free initialization engine");
        require(!closed&&!disposed&&!advancing&&!untrackedFailure&&phase==IDLE&&!pendingOwnedResult
                &&sp==0&&pendingInitializerGlobal==null,"Initializer requires an open idle engine");
        require(global!=null&&action!=null&&global.source==action.source,
                "Initializer pair requires one SourceBinding");
        int globalId=program.functionId(global),actionId=program.functionId(action);
        Function gf=program.functions[globalId],af=program.functions[actionId];
        require(gf.header==global&&af.header==action,"Initializer requires original registered Headers");
        require(global.kind.equals("fdecl")&&global.initialized()&&gf.params.length==0
                &&global.resultType.equals("object"),"Initializer global requires boxed initialized fdecl");
        Map<String,Object> runtime=map(global.evidence.get("runtime"));
        require(action.exactName.equals(frozenName(runtime.get("initializer"))),
                "Initializer action Name differs from global evidence");
        require(action.kind.equals("fdecl")&&!action.initialized()&&action.params.length==1
                &&action.paramTypes[0].equals("void")&&!action.borrowed[0]
                &&action.resultType.equals("object"),"Initializer action ABI must be (void) -> object");
        require(!constantReady[globalId]&&!constantRetired[globalId]&&!initializerAttempts.get(globalId),
                "Initializer global is occupied, retired or already attempted");
        // All rejection that can be checked without executing guest code precedes
        // claiming the attempt. start can still fail terminally; it is not replayed.
        rootEntry(af); preflightCallable(af,true); validateEntryArguments(af,new Object[]{ERASED});
        initializerAttempts.set(globalId);
        try { start(actionId,new Object[]{ERASED}); }
        catch(Throwable failure) { initializerFailed=true; throw failure; }
        pendingInitializerGlobal=global; pendingInitializerAction=action;
    }

    /** Consume ONLY the result of this engine's pending initializer invocation.
     * IO.error transfers the original result unchanged and forbids finishing
     * startup. On IO.ok publish the SAME payload after markPersistent, consume
     * the wrapper, and return an owned IO.ok Unit. No supplied value can be
     * installed. Validation/cancellation/allocation precede the nonthrowing
     * RC-and-cache commit; a rejected completion retains its original result. */
    public Object completeInitializer() {
        explicitOnly();
        require(!closed&&!disposed&&!advancing&&initializing&&taskRuntime==null
                &&pendingInitializerGlobal!=null&&phase==COMPLETE&&pendingOwnedResult
                &&entry!=null&&entry.header==pendingInitializerAction,
                "No completed initializer result available");
        int id=program.functionId(pendingInitializerGlobal);
        require(program.functions[id].header==pendingInitializerGlobal
                &&!constantReady[id]&&!constantRetired[id],"Initializer global changed or is occupied");
        Node wrapper=node(result);
        require(kindMetadata(wrapper)==null&&!wrapper.array&&!wrapper.ref&&!wrapper.readyTask
                &&wrapper.closure==null&&wrapper.scalars.length==0&&wrapper.fields.length==1
                &&(wrapper.tag==0||wrapper.tag==1)&&wrapper.rc>=0,
                "Initializer must return a plain IO.Result");
        validateHostObject(wrapper.fields[0]);
        if(wrapper.tag==1) {
            Object error=detachCompletedResult();
            pendingInitializerGlobal=null; pendingInitializerAction=null; initializerFailed=true;
            return error;
        }
        Object payload=wrapper.fields[0];
        ArrayList<Node> commit=persistentPreflight(payload);
        require(releaseTransaction==null&&!releaseRoot&&releasePending==0&&quietCurrent==null,
                "Initializer completion cannot overlap release work");
        Node status=new Node(0,1,0); status.fields[0]=ERASED;
        if(Thread.currentThread().isInterrupted()) throw error("Initializer completion interrupted");
        // No allocations, validation, callbacks or cancellation points below.
        // Payload persistence makes consuming this known wrapper finalizer-free.
        for(int i=0;i<commit.size();i++) commit.get(i).rc=0;
        if(wrapper.rc!=0) {
            wrapper.rc--; releases++;
            if(wrapper.rc==0) { wrapper.dead=true; wrapper.fields[0]=null; }
        }
        constants[id]=payload; constantReady[id]=true; allocations++;
        detachCompletedResult();
        pendingInitializerGlobal=null; pendingInitializerAction=null;
        return status;
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
        if(pendingInitializerGlobal!=null) throw error("Cannot fork a pending initializer");
        if(externalRoots==null) throw error("Explicit fork roots required");
        // phase RUNNING between advance calls is a paused dispatch/release-work
        // boundary. No Java call frame is captured in that state.
        Interpreter child=new Interpreter(program,explicit,initializing,buildIdentity,taskRuntime,profilingPolicy);
        child.initializerAttempts=(BitSet)initializerAttempts.clone(); child.initializerFailed=initializerFailed;
        child.pointerHashPolicy=pointerHashPolicy; child.levelInstantiationPolicy=levelInstantiationPolicy; child.exprInstantiationPolicy=exprInstantiationPolicy; child.shareCommonLayout=shareCommonLayout; child.exprTransformPolicy=exprTransformPolicy;
        ForkCopy copy=new ForkCopy(child);
        copy.bind(constants,child.constants);
        child.objects=(Object[])copy.value(objects);
        child.numbers=numbers.clone(); child.joins=joins.clone();
        System.arraycopy(constantReady,0,child.constantReady,0,constantReady.length);
        child.constantRetired=constantRetired.clone(); child.disposed=disposed;
        child.graphInstalled=graphInstalled; child.preparedGlobalSources=preparedGlobalSources;
        child.moduleGraphInstalled=moduleGraphInstalled; child.preparedModuleSource=preparedModuleSource;
        child.bp=bp; child.sp=sp; child.jbp=jbp; child.jsp=jsp;
        child.result=copy.value(result); child.scalarResult=scalarResult;
        child.stdoutRoot=(Node)copy.value(stdoutRoot);
        child.stdinDefaultRoot=(Node)copy.value(stdinDefaultRoot); child.stderrRoot=(Node)copy.value(stderrRoot);
        if(stdioContext!=null) {
            child.stdioContext=new StdioContext();
            for(int i=0;i<3;i++) child.stdioContext.current[i]=(Node)copy.value(stdioContext.current[i]);
        }
        child.output.append(output); child.stderrOutput.append(stderrOutput);
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
            if(source==null||source instanceof Long||source instanceof BigInteger||source instanceof String||source instanceof F64Bits||source instanceof F32Bits||source instanceof Double||source instanceof Float) return source;
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
                        old.resultType,old.intrinsic,old.hostExtern,child.runtimeIdentity,old.header,old.borrowedUtf8);
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
            if(source instanceof ExprFullResearchState||source instanceof DelayedTransform||source instanceof DelayedTransformTask) {
                Object out=source instanceof ExprFullResearchState?new ExprFullResearchState():source instanceof DelayedTransform?new DelayedTransform():
                        source instanceof DelayedVisitFrame?new DelayedVisitFrame(null):source instanceof DelayedFVarFrame?new DelayedFVarFrame(null):
                        source instanceof DelayedAssignmentFrame?new DelayedAssignmentFrame(null):source instanceof DelayedAppFrame?new DelayedAppFrame(null):
                        source instanceof DelayedPrefixFrame?new DelayedPrefixFrame(null):new DelayedResolveFrame(null,null,null);
                copies.put(source,out); pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof ScopeGeneration||source instanceof DelayedCommand) return source;
            if(source instanceof DelayedResearchState||source instanceof DelayedSession||source instanceof ScopedExprCache||source instanceof ScopedBucket
                    ||source instanceof ScopedEntry||source instanceof ScopedCacheOperation||source instanceof PendingNameEntry||source instanceof SubstitutionEntry
                    ||source instanceof SavedSubstitution||source instanceof SubstitutionFrame||source instanceof SubstitutionLookup||source instanceof DelayedHelperPacket||source instanceof ResolverTask) {
                Object out=source instanceof DelayedResearchState?new DelayedResearchState():source instanceof DelayedSession?new DelayedSession():
                        source instanceof ScopedExprCache?new ScopedExprCache():source instanceof ScopedBucket?new ScopedBucket():source instanceof ScopedEntry?new ScopedEntry():
                        source instanceof ScopedCacheOperation?new ScopedCacheOperation():source instanceof PendingNameEntry?new PendingNameEntry():
                        source instanceof SubstitutionEntry?new SubstitutionEntry():source instanceof SavedSubstitution?new SavedSubstitution():
                        source instanceof SubstitutionFrame?new SubstitutionFrame():source instanceof SubstitutionLookup?new SubstitutionLookup():source instanceof DelayedHelperPacket?new DelayedHelperPacket():
                        source instanceof ResolvableExprFrame?new ResolvableExprFrame(null):source instanceof ResolvablePendingFrame?new ResolvablePendingFrame(null):new ResolvableAppFrame(null);
                copies.put(source,out); pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof ExprDirectResearchState||source instanceof ExprDirectSession||source instanceof DirectHelperPacket
                    ||source instanceof DirectNameEntry||source instanceof ExprDirectTask) {
                Object out=source instanceof ExprDirectResearchState?new ExprDirectResearchState():source instanceof ExprDirectSession?new ExprDirectSession():
                        source instanceof DirectHelperPacket?new DirectHelperPacket():source instanceof DirectNameEntry?new DirectNameEntry(0,null):
                        source instanceof DirectVisitFrame?new DirectVisitFrame(null):source instanceof DirectMVarFrame?new DirectMVarFrame(null):
                        source instanceof DirectAssignmentFrame?new DirectAssignmentFrame(null):source instanceof DirectDelayedFrame?new DirectDelayedFrame(null):
                        source instanceof DirectAppFrame?new DirectAppFrame(null):source instanceof DirectNonMvarAppFrame?new DirectNonMvarAppFrame(null):
                        source instanceof DirectAppBetaFrame?new DirectAppBetaFrame(null,null):source instanceof DirectLevelFrame?new DirectLevelFrame(null):new DirectLevelsFrame(null);
                copies.put(source,out); pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof ExprSubstSlice) {
                ExprSubstSlice old=(ExprSubstSlice)source;
                ExprSubstSlice out=new ExprSubstSlice((Node)value(old.array),value(old.single),old.begin,old.end,old.reverse);
                copies.put(source,out); return out;
            }
            if(source instanceof ExprMachineryState||source instanceof ReplaceJob||source instanceof BetaJob
                    ||source instanceof ExprReplaceFrame||source instanceof ExprBetaFrame||source instanceof ExprPacket||source instanceof ExprCallbackPacket||source instanceof ExprCredit) {
                Object out=source instanceof ExprMachineryState?new ExprMachineryState():source instanceof ReplaceJob?new ReplaceJob():
                        source instanceof BetaJob?new BetaJob():source instanceof ExprReplaceFrame?new ExprReplaceFrame(null,0):
                        source instanceof ExprBetaFrame?new ExprBetaFrame(null):source instanceof ExprPacket?new ExprPacket():
                        source instanceof ExprCallbackPacket?new ExprCallbackPacket():new ExprCredit(null,false);
                copies.put(source,out); pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof MVarSessionResearchState||source instanceof LevelInstantiationState||source instanceof LevelSession||source instanceof MVarContextCell||source instanceof InstantiationBudget||source instanceof LevelFrame||source instanceof LevelPacket||source instanceof LevelCredit) {
                Object out=source instanceof MVarSessionResearchState?new MVarSessionResearchState():source instanceof LevelInstantiationState?new LevelInstantiationState():source instanceof LevelSession?new LevelSession():
                        source instanceof MVarContextCell?new MVarContextCell():source instanceof InstantiationBudget?new InstantiationBudget():source instanceof LevelFrame?new LevelFrame(null):
                        source instanceof LevelPacket?new LevelPacket():new LevelCredit(null,false);
                copies.put(source,out); pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof ShareState) {
                ShareState out=new ShareState(); copies.put(source,out); pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof ShareFrame) {
                ShareFrame out=new ShareFrame(null); copies.put(source,out); pending.addLast(new Object[]{source,out}); return out;
            }
            if(source instanceof FindState) {
                FindState out=new FindState(); copies.put(source,out);
                pending.addLast(new Object[]{source,out}); return out;
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
                    out.parent=(RuntimeAction)value(old.parent); out.guest=(HostGuestRecord)value(old.guest); out.find=(FindState)value(old.find); out.share=(ShareState)value(old.share); out.levelMvars=(LevelInstantiationState)value(old.levelMvars); out.exprMachinery=(ExprMachineryState)value(old.exprMachinery); out.mvarSessionResearch=(MVarSessionResearchState)value(old.mvarSessionResearch); out.exprDirect=(ExprDirectResearchState)value(old.exprDirect); out.delayedResearch=(DelayedResearchState)value(old.delayedResearch); out.exprFull=(ExprFullResearchState)value(old.exprFull); out.operation=old.operation; out.stage=old.stage;
                    out.savedSp=old.savedSp; out.slot=old.slot; out.dest=old.dest; out.kind=old.kind;
                    out.cursor=old.cursor; out.limit=old.limit; out.pending=old.pending;
                    out.function=(Function)value(old.function); out.next=old.next;
                    out.surplus=(Object[])value(old.surplus); out.work=(Object[])value(old.work);
                    out.arguments=(Object[])value(old.arguments); out.completion=(HostCall)value(old.completion);
                    out.request=(HostRequest)value(old.request);
                    out.task=(TaskRecord)value(old.task); out.scope=(TaskRecord)value(old.scope); out.batch=(DependencyList)value(old.batch);
                    out.output=value(old.output); out.retiring=value(old.retiring); out.releaseClaimed=old.releaseClaimed; out.current=(Node)value(old.current); out.origin=(Node)value(old.origin);

                } else if(source instanceof ExprFullResearchState) {
                    ExprFullResearchState old=(ExprFullResearchState)source,out=(ExprFullResearchState)target;
                    out.context=(MVarContextCell)value(old.context); out.budget=(InstantiationBudget)value(old.budget);
                    out.direct=(ExprDirectSession)value(old.direct); out.delayed=(DelayedTransform)value(old.delayed);
                    out.input=(ExprCredit)value(old.input); out.e1=(ExprCredit)value(old.e1); out.e2=(ExprCredit)value(old.e2); out.pair=(ExprCredit)value(old.pair);
                    out.stage=old.stage; out.pairFields=old.pairFields;
                } else if(source instanceof DelayedTransform) {
                    DelayedTransform old=(DelayedTransform)source,out=(DelayedTransform)target;
                    out.foundation=(DelayedSession)value(old.foundation); out.input=value(old.input); out.result=(ExprCredit)value(old.result); out.phase=old.phase;
                    for(DelayedTransformTask frame:old.tasks) out.tasks.addLast((DelayedTransformTask)value(frame));
                } else if(source instanceof DelayedTransformTask) {
                    DelayedTransformTask old=(DelayedTransformTask)source,out=(DelayedTransformTask)target;
                    out.child=(DelayedTransformTask)value(old.child); out.result=(ExprCredit)value(old.result); out.received=(ExprCredit)value(old.received);
                    out.stage=old.stage; out.cleanup=old.cleanup; out.completed=old.completed; out.helperDone=old.helperDone;
                    if(source instanceof DelayedVisitFrame) {
                        DelayedVisitFrame a=(DelayedVisitFrame)old,b=(DelayedVisitFrame)out; b.original=(Node)value(a.original);
                        b.entryDepth=a.entryDepth; b.savedWatermark=a.savedWatermark; b.cursor=a.cursor; b.shared=a.shared; b.cacheHit=a.cacheHit; b.skipInsert=a.skipInsert;
                        for(int i=0;i<3;i++) b.children[i]=(ExprCredit)value(a.children[i]);
                    } else if(source instanceof DelayedFVarFrame) {
                        DelayedFVarFrame a=(DelayedFVarFrame)old,b=(DelayedFVarFrame)out; b.original=(Node)value(a.original); b.name=value(a.name);
                    } else if(source instanceof DelayedAssignmentFrame) {
                        DelayedAssignmentFrame a=(DelayedAssignmentFrame)old,b=(DelayedAssignmentFrame)out; b.name=value(a.name);
                        b.option=(ExprCredit)value(a.option); b.assigned=(ExprCredit)value(a.assigned); b.newValue=(ExprCredit)value(a.newValue); b.present=a.present; b.outer=a.outer;
                    } else if(source instanceof DelayedAppFrame) {
                        DelayedAppFrame a=(DelayedAppFrame)old,b=(DelayedAppFrame)out; b.original=(Node)value(a.original); b.head=value(a.head); b.cursor=value(a.cursor);
                        b.argumentCount=a.argumentCount; b.option=(ExprCredit)value(a.option); b.recordTemporary=(ExprCredit)value(a.recordTemporary);
                        b.fvars=(ExprCredit)value(a.fvars); b.pendingName=(ExprCredit)value(a.pendingName); b.discardedAssignment=(ExprCredit)value(a.discardedAssignment);
                    } else if(source instanceof DelayedPrefixFrame) {
                        DelayedPrefixFrame a=(DelayedPrefixFrame)old,b=(DelayedPrefixFrame)out; b.original=(Node)value(a.original);
                        b.argument=(ExprCredit)value(a.argument); b.function=(ExprCredit)value(a.function);
                    } else {
                        DelayedResolveFrame a=(DelayedResolveFrame)old,b=(DelayedResolveFrame)out; b.original=(Node)value(a.original); b.cursor=value(a.cursor);
                        b.fvars=value(a.fvars); b.pendingName=value(a.pendingName); b.argumentTemporary=(ExprCredit)value(a.argumentTemporary);
                        b.option=(ExprCredit)value(a.option); b.expressionTemporary=(ExprCredit)value(a.expressionTemporary); b.newValue=(ExprCredit)value(a.newValue);
                        b.betaParameter=(ExprCredit)value(a.betaParameter); b.substitutions=(SubstitutionFrame)value(a.substitutions);
                        b.argumentCount=a.argumentCount; b.extraCount=a.extraCount;
                        for(ExprCredit argument:a.arguments) b.arguments.add((ExprCredit)value(argument));
                    }
                } else if(source instanceof DelayedResearchState) {
                    DelayedResearchState old=(DelayedResearchState)source,out=(DelayedResearchState)target;
                    out.context=(MVarContextCell)value(old.context); out.budget=(InstantiationBudget)value(old.budget); out.session=(DelayedSession)value(old.session);
                    for(ExprCredit anchor:old.anchors) out.anchors.add((ExprCredit)value(anchor));
                    out.commands=old.commands==null?null:old.commands.clone(); out.lastResult=(ExprCredit)value(old.lastResult); out.output=(ExprCredit)value(old.output); out.pendingInput=(ExprCredit)value(old.pendingInput); out.lastObservation=old.lastObservation;
                    out.mode=old.mode; out.commandCursor=old.commandCursor; out.stage=old.stage; out.cleanup=old.cleanup; out.outputFields=old.outputFields;
                    out.observations.addAll(old.observations);
                } else if(source instanceof DelayedSession) {
                    DelayedSession old=(DelayedSession)source,out=(DelayedSession)target;
                    out.context=(MVarContextCell)value(old.context); out.budget=(InstantiationBudget)value(old.budget); out.policy=old.policy;
                    out.cache=(ScopedExprCache)value(old.cache);
                    for(Map.Entry<Node,Boolean> item:old.resolvableExpressions.entrySet()) out.resolvableExpressions.put((Node)value(item.getKey()),item.getValue());
                    for(Map.Entry<Integer,ArrayList<PendingNameEntry>> bucket:old.pending.entrySet()) {
                        ArrayList<PendingNameEntry> entries=new ArrayList<>(); for(PendingNameEntry entry:bucket.getValue()) entries.add((PendingNameEntry)value(entry));
                        out.pending.put(bucket.getKey(),entries);
                    }
                    for(PendingNameEntry entry:old.pendingOwners) out.pendingOwners.add((PendingNameEntry)value(entry));
                    for(ExprCredit credit:old.saved) out.saved.add((ExprCredit)value(credit));
                    for(DirectNameEntry entry:old.nameOwners) out.nameOwners.add((DirectNameEntry)value(entry));
                    for(Map.Entry<Integer,ArrayList<DirectNameEntry>> item:old.normalized.entrySet()) {
                        ArrayList<DirectNameEntry> entries=new ArrayList<>(); for(DirectNameEntry entry:item.getValue()) entries.add((DirectNameEntry)value(entry));
                        out.normalized.put(item.getKey(),entries);
                    }
                    for(Map.Entry<Integer,ArrayList<SubstitutionEntry>> bucket:old.substitutions.entrySet()) {
                        ArrayList<SubstitutionEntry> entries=new ArrayList<>(); for(SubstitutionEntry entry:bucket.getValue()) entries.add((SubstitutionEntry)value(entry));
                        out.substitutions.put(bucket.getKey(),entries);
                    }
                    for(SubstitutionEntry entry:old.substitutionOwners) out.substitutionOwners.add((SubstitutionEntry)value(entry));
                    for(ResolverTask frame:old.resolver) out.resolver.addLast((ResolverTask)value(frame));
                    out.call=(DelayedHelperPacket)value(old.call); out.constructorCall=(ExprPacket)value(old.constructorCall);
                    out.cacheOperation=(ScopedCacheOperation)value(old.cacheOperation); out.substitution=(SubstitutionFrame)value(old.substitution); out.lookup=(SubstitutionLookup)value(old.lookup);
                    for(SubstitutionFrame frame:old.substitutionFrames) out.substitutionFrames.addLast((SubstitutionFrame)value(frame));
                    out.retiring=(ExprCredit)value(old.retiring); out.result=(ExprCredit)value(old.result);
                    out.depth=old.depth; out.resultScope=old.resultScope; out.phase=old.phase; out.drainStage=old.drainStage; out.drainCursor=old.drainCursor;
                    out.booleanResult=old.booleanResult;
                } else if(source instanceof ScopedExprCache) {
                    ScopedExprCache old=(ScopedExprCache)source,out=(ScopedExprCache)target;
                    for(Map.Entry<Node,HashMap<Integer,ScopedBucket>> item:old.index.entrySet()) {
                        HashMap<Integer,ScopedBucket> depths=new HashMap<>();
                        for(Map.Entry<Integer,ScopedBucket> entry:item.getValue().entrySet()) depths.put(entry.getKey(),(ScopedBucket)value(entry.getValue()));
                        out.index.put((Node)value(item.getKey()),depths);
                    }
                    for(ScopedBucket bucket:old.buckets) out.buckets.add((ScopedBucket)value(bucket));
                    out.current=old.current; out.scope=old.scope; out.generationCounter=old.generationCounter; out.generationCount=old.generationCount;
                    out.liveEntries=old.liveEntries; out.sealed=old.sealed; out.drainBucket=old.drainBucket; out.drainEntry=old.drainEntry; out.retiringEntry=(ScopedEntry)value(old.retiringEntry);
                } else if(source instanceof ScopedBucket) {
                    ScopedBucket old=(ScopedBucket)source,out=(ScopedBucket)target; out.key=(Node)value(old.key); out.depth=old.depth;
                    for(ScopedEntry entry:old.entries) out.entries.add((ScopedEntry)value(entry));
                } else if(source instanceof ScopedEntry) {
                    ScopedEntry old=(ScopedEntry)source,out=(ScopedEntry)target; out.result=(ExprCredit)value(old.result); out.generation=old.generation;
                    out.validLevel=old.validLevel; out.resultScope=old.resultScope; out.reserved=old.reserved;
                } else if(source instanceof ScopedCacheOperation) {
                    ScopedCacheOperation old=(ScopedCacheOperation)source,out=(ScopedCacheOperation)target;
                    out.bucket=(ScopedBucket)value(old.bucket); out.top=(ScopedEntry)value(old.top); out.retiringEntry=(ScopedEntry)value(old.retiringEntry); out.newEntry=(ScopedEntry)value(old.newEntry);
                    out.currentCursor=old.currentCursor; out.entryCursor=old.entryCursor; out.computed=(ExprCredit)value(old.computed); out.shared=(ExprCredit)value(old.shared);
                    out.optional=(ExprCredit)value(old.optional); out.returned=(ExprCredit)value(old.returned); out.replacement=(ExprCredit)value(old.replacement); out.key=(Node)value(old.key);
                    out.kind=old.kind; out.depth=old.depth; out.resultScope=old.resultScope; out.stage=old.stage; out.walkLevel=old.walkLevel; out.rewindStage=old.rewindStage; out.hit=old.hit; out.completed=old.completed; out.rewound=old.rewound;
                } else if(source instanceof PendingNameEntry) {
                    PendingNameEntry old=(PendingNameEntry)source,out=(PendingNameEntry)target; out.name=(ExprCredit)value(old.name); out.hash=old.hash; out.state=old.state;
                } else if(source instanceof SubstitutionEntry) {
                    SubstitutionEntry old=(SubstitutionEntry)source,out=(SubstitutionEntry)target;
                    out.name=(ExprCredit)value(old.name); out.value=(ExprCredit)value(old.value); out.hash=old.hash; out.depth=old.depth; out.scope=old.scope; out.live=old.live;
                } else if(source instanceof SavedSubstitution) {
                    SavedSubstitution old=(SavedSubstitution)source,out=(SavedSubstitution)target;
                    out.name=(ExprCredit)value(old.name); out.oldValue=(ExprCredit)value(old.oldValue); out.oldDepth=old.oldDepth; out.oldScope=old.oldScope; out.hadOld=old.hadOld;
                } else if(source instanceof SubstitutionFrame) {
                    SubstitutionFrame old=(SubstitutionFrame)source,out=(SubstitutionFrame)target;
                    out.fvars=value(old.fvars); out.sourceArguments=value(old.sourceArguments); for(ExprCredit argument:old.arguments) out.arguments.add((ExprCredit)value(argument));
                    for(SavedSubstitution saved:old.saved) out.saved.add((SavedSubstitution)value(saved));
                    out.existing=(SubstitutionEntry)value(old.existing); out.replacement=(SubstitutionEntry)value(old.replacement);
                    out.newName=(ExprCredit)value(old.newName); out.newValue=(ExprCredit)value(old.newValue); out.retiringName=(ExprCredit)value(old.retiringName); out.retiringValue=(ExprCredit)value(old.retiringValue);
                    out.depth=old.depth; out.index=old.index; out.stage=old.stage; out.cleanup=old.cleanup;
                    out.scopePushed=old.scopePushed; out.restored=old.restored; out.completed=old.completed; out.ownsArguments=old.ownsArguments; out.erasing=old.erasing;
                } else if(source instanceof SubstitutionLookup) {
                    SubstitutionLookup old=(SubstitutionLookup)source,out=(SubstitutionLookup)target;
                    out.name=value(old.name); out.entry=(SubstitutionEntry)value(old.entry); out.optional=(ExprCredit)value(old.optional); out.returned=(ExprCredit)value(old.returned);
                    out.depth=old.depth; out.stage=old.stage; out.present=old.present; out.completed=old.completed;
                } else if(source instanceof DelayedHelperPacket) {
                    DelayedHelperPacket old=(DelayedHelperPacket)source,out=(DelayedHelperPacket)target;
                    out.function=(Function)value(old.function); out.arguments=(Object[])value(old.arguments); out.owned=old.owned.clone(); out.target=(ResolverTask)value(old.target); out.transformTarget=(DelayedTransformTask)value(old.transformTarget);
                    out.role=old.role; out.started=old.started; out.entered=old.entered;
                } else if(source instanceof ResolverTask) {
                    ResolverTask old=(ResolverTask)source,out=(ResolverTask)target; out.child=(ResolverTask)value(old.child); out.received=(ExprCredit)value(old.received);
                    out.stage=old.stage; out.cursor=old.cursor; out.cleanup=old.cleanup; out.result=old.result; out.completed=old.completed;
                    if(source instanceof ResolvableExprFrame) {
                        ResolvableExprFrame a=(ResolvableExprFrame)old,b=(ResolvableExprFrame)out; b.original=(Node)value(a.original); b.entryShared=a.entryShared;
                    } else if(source instanceof ResolvablePendingFrame) {
                        ResolvablePendingFrame a=(ResolvablePendingFrame)old,b=(ResolvablePendingFrame)out; b.name=value(a.name); b.entry=(PendingNameEntry)value(a.entry);
                        b.option=(ExprCredit)value(a.option); b.temporary=(ExprCredit)value(a.temporary);
                    } else {
                        ResolvableAppFrame a=(ResolvableAppFrame)old,b=(ResolvableAppFrame)out; b.original=(Node)value(a.original); b.head=value(a.head); b.cursor=value(a.cursor); b.argumentCount=a.argumentCount;
                        b.option=(ExprCredit)value(a.option); b.recordTemporary=(ExprCredit)value(a.recordTemporary); b.fvars=(ExprCredit)value(a.fvars); b.pendingName=(ExprCredit)value(a.pendingName);
                    }
                } else if(source instanceof ExprDirectResearchState) {
                    ExprDirectResearchState old=(ExprDirectResearchState)source,out=(ExprDirectResearchState)target;
                    out.context=(MVarContextCell)value(old.context); out.budget=(InstantiationBudget)value(old.budget);
                    out.session=(ExprDirectSession)value(old.session); out.input=(ExprCredit)value(old.input); out.e1=(ExprCredit)value(old.e1);
                    out.output=(ExprCredit)value(old.output); out.reportExprLoan=(ExprCredit)value(old.reportExprLoan); out.stage=old.stage; out.outputFields=old.outputFields;
                } else if(source instanceof ExprDirectSession) {
                    ExprDirectSession old=(ExprDirectSession)source,out=(ExprDirectSession)target;
                    out.context=(MVarContextCell)value(old.context); out.budget=(InstantiationBudget)value(old.budget); out.levels=(LevelSession)value(old.levels); out.policy=old.policy;
                    for(ExprDirectTask directTask:old.tasks) out.tasks.addLast((ExprDirectTask)value(directTask));
                    for(Map.Entry<Node,ExprCredit> item:old.cache.entrySet()) out.cache.put((Node)value(item.getKey()),(ExprCredit)value(item.getValue()));
                    for(ExprCredit credit:old.cacheValues) out.cacheValues.add((ExprCredit)value(credit));
                    for(ExprCredit credit:old.saved) out.saved.add((ExprCredit)value(credit));
                    for(Map.Entry<Integer,ArrayList<DirectNameEntry>> bucket:old.normalized.entrySet()) {
                        ArrayList<DirectNameEntry> entries=new ArrayList<>(); for(DirectNameEntry entry:bucket.getValue()) entries.add((DirectNameEntry)value(entry));
                        out.normalized.put(bucket.getKey(),entries);
                    }
                    for(DirectNameEntry entry:old.nameOwners) out.nameOwners.add((DirectNameEntry)value(entry));
                    out.call=(DirectHelperPacket)value(old.call); out.constructorCall=(ExprPacket)value(old.constructorCall);
                    out.result=(ExprCredit)value(old.result); out.retiring=(ExprCredit)value(old.retiring);
                    out.hasUpdateableDelayed=old.hasUpdateableDelayed; out.phase=old.phase; out.drainStage=old.drainStage; out.drainCursor=old.drainCursor;
                } else if(source instanceof DirectHelperPacket) {
                    DirectHelperPacket old=(DirectHelperPacket)source,out=(DirectHelperPacket)target;
                    out.function=(Function)value(old.function); out.role=old.role; out.arguments=(Object[])value(old.arguments); out.owned=old.owned.clone();
                    out.started=old.started; out.entered=old.entered; out.target=(ExprDirectTask)value(old.target);
                } else if(source instanceof DirectNameEntry) {
                    DirectNameEntry old=(DirectNameEntry)source,out=(DirectNameEntry)target; out.hash=old.hash; out.name=(ExprCredit)value(old.name);
                } else if(source instanceof ExprDirectTask) {
                    ExprDirectTask old=(ExprDirectTask)source,out=(ExprDirectTask)target;
                    out.child=(ExprDirectTask)value(old.child); out.result=(ExprCredit)value(old.result); out.received=(ExprCredit)value(old.received);
                    out.stage=old.stage; out.cleanup=old.cleanup; out.completed=old.completed; out.helperDone=old.helperDone;
                    if(source instanceof DirectVisitFrame) {
                        DirectVisitFrame a=(DirectVisitFrame)old,b=(DirectVisitFrame)out; b.original=(Node)value(a.original); b.shared=a.shared; b.cursor=a.cursor; b.cacheTemporary=(ExprCredit)value(a.cacheTemporary);
                        for(int i=0;i<3;i++) b.children[i]=(ExprCredit)value(a.children[i]); b.level=(LevelCredit)value(a.level); b.levels=(ExprCredit)value(a.levels);
                    } else if(source instanceof DirectMVarFrame) {
                        DirectMVarFrame a=(DirectMVarFrame)old,b=(DirectMVarFrame)out; b.original=(Node)value(a.original); b.name=value(a.name);
                        b.assigned=(ExprCredit)value(a.assigned); b.delayed=(ExprCredit)value(a.delayed);
                    } else if(source instanceof DirectAssignmentFrame) {
                        DirectAssignmentFrame a=(DirectAssignmentFrame)old,b=(DirectAssignmentFrame)out; b.name=value(a.name); b.option=(ExprCredit)value(a.option);
                        b.assigned=(ExprCredit)value(a.assigned); b.newValue=(ExprCredit)value(a.newValue); b.present=a.present;
                    } else if(source instanceof DirectDelayedFrame) {
                        DirectDelayedFrame a=(DirectDelayedFrame)old,b=(DirectDelayedFrame)out; b.name=value(a.name); b.option=(ExprCredit)value(a.option);
                        b.recordTemporary=(ExprCredit)value(a.recordTemporary); b.pendingName=(ExprCredit)value(a.pendingName); b.conditionResult=(ExprCredit)value(a.conditionResult);
                    } else if(source instanceof DirectAppFrame) {
                        DirectAppFrame a=(DirectAppFrame)old,b=(DirectAppFrame)out; b.original=(Node)value(a.original); b.cursor=value(a.cursor); b.name=value(a.name);
                        b.assigned=(ExprCredit)value(a.assigned); b.delayed=(ExprCredit)value(a.delayed);
                    } else if(source instanceof DirectNonMvarAppFrame) {
                        DirectNonMvarAppFrame a=(DirectNonMvarAppFrame)old,b=(DirectNonMvarAppFrame)out; b.original=(Node)value(a.original);
                        b.argument=(ExprCredit)value(a.argument); b.function=(ExprCredit)value(a.function);
                    } else if(source instanceof DirectAppBetaFrame) {
                        DirectAppBetaFrame a=(DirectAppBetaFrame)old,b=(DirectAppBetaFrame)out; b.cursor=value(a.cursor); b.functionOptional=(ExprCredit)value(a.functionOptional);
                        b.betaParameter=(ExprCredit)value(a.betaParameter); b.argumentTemporary=(ExprCredit)value(a.argumentTemporary);
                        for(ExprCredit credit:a.arguments) b.arguments.add((ExprCredit)value(credit));
                    } else if(source instanceof DirectLevelFrame) {
                        DirectLevelFrame a=(DirectLevelFrame)old,b=(DirectLevelFrame)out; b.input=value(a.input); b.levelResult=(LevelCredit)value(a.levelResult);
                    } else {
                        DirectLevelsFrame a=(DirectLevelsFrame)old,b=(DirectLevelsFrame)out; b.original=value(a.original); b.cursor=value(a.cursor);
                        for(Node node:a.cells) b.cells.add((Node)value(node)); b.firstChanged=(LevelCredit)value(a.firstChanged);
                        b.currentHead=(LevelCredit)value(a.currentHead); b.headLoan=(LevelCredit)value(a.headLoan);
                        b.list=(ExprCredit)value(a.list); b.replacement=(ExprCredit)value(a.replacement); b.tailLoan=(ExprCredit)value(a.tailLoan); b.consCredit=(ExprCredit)value(a.consCredit);
                        b.building=(Node)value(a.building); b.index=a.index; b.builtFields=a.builtFields;
                    }
                } else if(source instanceof ExprCredit) {
                    ExprCredit old=(ExprCredit)source,out=(ExprCredit)target; out.value=value(old.value); out.owned=old.owned;
                } else if(source instanceof ExprReplaceFrame) {
                    ExprReplaceFrame old=(ExprReplaceFrame)source,out=(ExprReplaceFrame)target;
                    out.original=(Node)value(old.original); out.offset=old.offset; out.stage=old.stage; out.cursor=old.cursor; out.cleanup=old.cleanup; out.abstractScan=old.abstractScan;
                    out.shared=old.shared; out.active=old.active; out.result=(ExprCredit)value(old.result);
                    for(int i=0;i<old.children.length;i++) out.children[i]=(ExprCredit)value(old.children[i]);
                } else if(source instanceof ExprBetaFrame) {
                    ((ExprBetaFrame)target).expression=(ExprCredit)value(((ExprBetaFrame)source).expression);
                } else if(source instanceof ExprCallbackPacket) {
                    ExprCallbackPacket old=(ExprCallbackPacket)source,out=(ExprCallbackPacket)target;
                    out.frame=(ExprReplaceFrame)value(old.frame); out.arguments=(Object[])value(old.arguments);
                    out.current=(ExprCredit)value(old.current); out.predicate=(ExprCredit)value(old.predicate); out.option=(ExprCredit)value(old.option);
                    out.stage=old.stage; out.started=old.started; out.receiverOwned=old.receiverOwned;
                } else if(source instanceof ExprPacket) {
                    ExprPacket old=(ExprPacket)source,out=(ExprPacket)target; out.function=(Function)value(old.function);
                    out.arguments=(Object[])value(old.arguments); out.expectedFields=(Object[])value(old.expectedFields); out.owned=old.owned.clone();
                    out.role=old.role; out.expectedTag=old.expectedTag; out.expectedFlag=old.expectedFlag;
                    out.started=old.started; out.entered=old.entered; out.replaceFrame=(ExprReplaceFrame)value(old.replaceFrame); out.beta=(BetaJob)value(old.beta); out.directTarget=(ExprDirectTask)value(old.directTarget); out.delayedTarget=(DelayedTransformTask)value(old.delayedTarget);
                } else if(source instanceof ExprJob) {
                    ExprJob old=(ExprJob)source,out=(ExprJob)target;
                    out.result=(ExprCredit)value(old.result); out.childResult=(ExprCredit)value(old.childResult); out.completed=old.completed; out.cleanup=old.cleanup;
                    if(source instanceof ReplaceJob) {
                        ReplaceJob r=(ReplaceJob)old,t=(ReplaceJob)out;
                        t.input=value(r.input); t.slice=(ExprSubstSlice)value(r.slice); t.mode=r.mode; t.cutoff=r.cutoff; t.amount=r.amount; t.abstractArray=(Node)value(r.abstractArray); t.prefixLength=r.prefixLength; t.substitutions=(Object[])value(r.substitutions); t.stage=r.stage; t.reservedCacheEntries=r.reservedCacheEntries;
                        for(ExprReplaceFrame frame:r.frames) t.frames.addLast((ExprReplaceFrame)value(frame));
                        for(Map.Entry<Node,ExprCredit> entry:r.callbackCache.entrySet()) t.callbackCache.put((Node)value(entry.getKey()),(ExprCredit)value(entry.getValue()));
                        for(Map.Entry<Node,HashMap<Integer,ExprCredit>> entry:r.cache.entrySet()) {
                            HashMap<Integer,ExprCredit> offsets=new HashMap<>();
                            for(Map.Entry<Integer,ExprCredit> item:entry.getValue().entrySet()) offsets.put(item.getKey(),(ExprCredit)value(item.getValue()));
                            t.cache.put((Node)value(entry.getKey()),offsets);
                        }
                        for(ExprCredit credit:r.cacheValues) t.cacheValues.add((ExprCredit)value(credit));
                        for(Node node:r.active.keySet()) t.active.put((Node)value(node),Boolean.TRUE);
                    } else {
                        BetaJob b=(BetaJob)old,t=(BetaJob)out;
                        t.function=(ExprCredit)value(b.function); t.temporary=(ExprCredit)value(b.temporary);
                        t.accumulator=(ExprCredit)value(b.accumulator); t.replacement=(ExprCredit)value(b.replacement);
                        t.reverseArgs=(Object[])value(b.reverseArgs); t.consumed=b.consumed; t.remaining=b.remaining; t.stage=b.stage;
                        for(ExprBetaFrame frame:b.frames) t.frames.addLast((ExprBetaFrame)value(frame));
                    }
                } else if(source instanceof ExprMachineryState) {
                    ExprMachineryState old=(ExprMachineryState)source,out=(ExprMachineryState)target;
                    out.policy=old.policy; out.borrowedPredicate=(Node)value(old.borrowedPredicate); out.callback=(ExprCallbackPacket)value(old.callback); out.input=(ExprCredit)value(old.input); out.result=(ExprCredit)value(old.result); out.retiring=(ExprCredit)value(old.retiring);
                    for(ExprJob job:old.jobs) out.jobs.addLast((ExprJob)value(job));
                    for(ExprCredit credit:old.arguments) out.arguments.add((ExprCredit)value(credit));
                    out.call=(ExprPacket)value(old.call); out.budget=(InstantiationBudget)value(old.budget); out.stage=old.stage; out.cleanup=old.cleanup; out.liveFrames=old.liveFrames; out.liveCacheEntries=old.liveCacheEntries;
                } else if(source instanceof LevelCredit) {
                    LevelCredit old=(LevelCredit)source,out=(LevelCredit)target;
                    out.value=value(old.value); out.owned=old.owned;
                } else if(source instanceof LevelPacket) {
                    LevelPacket old=(LevelPacket)source,out=(LevelPacket)target;
                    out.function=(Function)value(old.function); out.role=old.role;
                    out.arguments=(Object[])value(old.arguments); out.owned=old.owned.clone();
                    out.entryStarted=old.entryStarted; out.entered=old.entered; out.frame=(LevelFrame)value(old.frame);
                } else if(source instanceof LevelFrame) {
                    LevelFrame old=(LevelFrame)source,out=(LevelFrame)target;
                    out.original=value(old.original); out.name=value(old.name); out.tag=old.tag; out.stage=old.stage; out.cleanup=old.cleanup;
                    out.shared=old.shared; out.active=old.active; out.cached=old.cached;
                    out.left=(LevelCredit)value(old.left); out.right=(LevelCredit)value(old.right);
                    out.option=(LevelCredit)value(old.option); out.assignment=(LevelCredit)value(old.assignment); out.result=(LevelCredit)value(old.result);
                } else if(source instanceof MVarSessionResearchState) {
                    MVarSessionResearchState old=(MVarSessionResearchState)source,out=(MVarSessionResearchState)target;
                    out.context=(MVarContextCell)value(old.context); out.budget=(InstantiationBudget)value(old.budget);
                    out.session=(LevelSession)value(old.session); out.exprPolicy=old.exprPolicy;
                    for(int i=0;i<2;i++) { out.inputs[i]=(LevelCredit)value(old.inputs[i]); out.levels[i]=(LevelCredit)value(old.levels[i]); }
                    out.exprInput=(ExprCredit)value(old.exprInput); out.exprResult=(ExprCredit)value(old.exprResult); out.output=(LevelCredit)value(old.output);
                    out.stage=old.stage; out.cursor=old.cursor; out.outputFields=old.outputFields; out.liftAmount=old.liftAmount;
                } else if(source instanceof InstantiationBudget) {
                    ((InstantiationBudget)target).work=((InstantiationBudget)source).work;
                } else if(source instanceof MVarContextCell) {
                    ((MVarContextCell)target).current=(LevelCredit)value(((MVarContextCell)source).current);
                } else if(source instanceof LevelInstantiationState) {
                    LevelInstantiationState old=(LevelInstantiationState)source,out=(LevelInstantiationState)target;
                    out.session=(LevelSession)value(old.session); out.input=(LevelCredit)value(old.input);
                    out.result=(LevelCredit)value(old.result); out.pair=(LevelCredit)value(old.pair);
                    out.stage=old.stage; out.pairFields=old.pairFields;
                } else if(source instanceof LevelSession) {
                    LevelSession old=(LevelSession)source,out=(LevelSession)target;
                    out.context=(MVarContextCell)value(old.context); out.budget=(InstantiationBudget)value(old.budget); out.policy=old.policy;
                    out.result=(LevelCredit)value(old.result); out.retiring=(LevelCredit)value(old.retiring); out.call=(LevelPacket)value(old.call);
                    out.phase=old.phase; out.drainStage=old.drainStage; out.drainCursor=old.drainCursor;
                    for(LevelFrame frame:old.frames) out.frames.addLast((LevelFrame)value(frame));
                    for(Map.Entry<Node,LevelCredit> item:old.cache.entrySet()) out.cache.put((Node)value(item.getKey()),(LevelCredit)value(item.getValue()));
                    for(LevelCredit credit:old.cacheValues) out.cacheValues.add((LevelCredit)value(credit));
                    for(LevelCredit credit:old.saved) out.saved.add((LevelCredit)value(credit));
                    for(Node node:old.active.keySet()) out.active.put((Node)value(node),Boolean.TRUE);
                } else if(source instanceof ShareState) {
                    ShareState old=(ShareState)source,out=(ShareState)target;
                    out.input=value(old.input); out.result=value(old.result); out.resultOwned=old.resultOwned; out.discarding=old.discarding;
                    out.nextIdentity=old.nextIdentity; out.entries=old.entries; out.work=old.work; out.outputBytes=old.outputBytes;
                    for(ShareFrame frame:old.frames) out.frames.addLast((ShareFrame)value(frame));
                    for(Map.Entry<Node,Node> entry:old.memo.entrySet()) out.memo.put((Node)value(entry.getKey()),(Node)value(entry.getValue()));
                    for(Node node:old.active.keySet()) out.active.put((Node)value(node),Boolean.TRUE);
                    for(Map.Entry<Object,Integer> entry:old.identities.entrySet()) out.identities.put(value(entry.getKey()),entry.getValue());
                    for(Map.Entry<Integer,ArrayList<Object>> entry:old.canonical.entrySet()) {
                        ArrayList<Object> bucket=new ArrayList<>();
                        for(Object item:entry.getValue()) bucket.add(value(item));
                        out.canonical.put(entry.getKey(),bucket);
                    }
                } else if(source instanceof ShareFrame) {
                    ShareFrame old=(ShareFrame)source,out=(ShareFrame)target;
                    out.input=value(old.input); out.representative=value(old.representative); out.candidate=(Node)value(old.candidate);
                    out.kind=old.kind; out.stage=old.stage; out.cursor=old.cursor; out.scalarCursor=old.scalarCursor; out.hash=old.hash;
                    out.bucketCursor=old.bucketCursor; out.compareCursor=old.compareCursor;
                    out.memoEligible=old.memoEligible; out.candidateOwned=old.candidateOwned;
                } else if(source instanceof FindState) {
                    FindState old=(FindState)source,out=(FindState)target;
                    out.predicate=(Node)value(old.predicate); out.root=(Node)value(old.root); out.current=(Node)value(old.current);
                    out.found=(Node)value(old.found); out.option=(Node)value(old.option); out.packet=(Object[])value(old.packet);
                    out.encounters=old.encounters; out.extended=old.extended; out.functionSpines.addAll(old.functionSpines);
                    out.stage=old.stage; out.predicateCredit=old.predicateCredit;
                    out.currentCredit=old.currentCredit; out.callbackStarted=old.callbackStarted;
                    out.receiverOwned=old.receiverOwned; out.foundOwned=old.foundOwned;
                    for(Object item:old.pending) out.pending.addLast(value(item));
                    for(Node item:old.visited.keySet()) out.visited.put((Node)value(item),Boolean.TRUE);
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
        if("uint16".equals(x)) return U16;
        if("uint32".equals(x)) return U32;
        if("usize".equals(x)) return USIZE;
        if("uint64".equals(x)) return U64;
        if("float".equals(x)) return F64;
        if("float32".equals(x)) return F32;
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
                                    resultType,intrinsic,hostExtern,null,null,
                                    intrinsic==STR_TO_UTF8&&Boolean.TRUE.equals(map(list(d.get("xs")).get(0)).get("borrow")));
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
                    case SPROJ: require((b.type==U8||b.type==U16||b.type==U32||b.type==U64||b.type==F64||b.type==F32)&&lane(env,e.a)==OBJ,"Scalar projection lane mismatch"); break;
                    case UPROJ: require(b.type==USIZE&&lane(env,e.a)==OBJ,"USize projection lane mismatch"); break;
                    case FAP: requireExecutableAbi(e.target); checkArgs(env,e.args,e.target.paramTypes); require(b.type==e.target.resultType,"Call result lane mismatch"); break;
                    case PAP: requireExecutableAbi(e.target); require(e.target.intrinsic!=PROFILE_IT,"Borrowed profiling primitive requires an owned guest wrapper"); require(!borrowedTaskPrimitive(e.target.intrinsic),"Borrowed task primitive requires owned closure wrapper"); require(b.type==OBJ&&e.args.length<e.target.params.length,"Invalid partial application"); require(!borrowedArrayPrimitive(e.target.intrinsic),"Borrowed array primitive requires owned closure wrapper"); require(!borrowedIntPrimitive(e.target.intrinsic),"Borrowed Int primitive requires owned closure wrapper"); require(!borrowedStringPositionPrimitive(e.target.intrinsic),"Borrowed String position primitive requires owned closure wrapper"); require(!borrowedStringCompletionPrimitive(e.target.intrinsic),"Borrowed String range primitive requires owned closure wrapper"); require(!borrowedBytePrimitive(e.target.intrinsic),"Borrowed ByteArray primitive requires owned closure wrapper"); require(!e.target.borrowedUtf8,"Borrowed UTF8 conversion requires owned closure wrapper"); require(e.target.intrinsic!=NAME_EQ,"Borrowed Name equality requires an owned guest wrapper"); require(e.target.intrinsic!=EXPR_CACHE,"Borrowed Expr data requires an owned guest wrapper"); require(!borrowedExprEquality(e.target.intrinsic),"Borrowed Expr equality requires an owned guest wrapper"); require(e.target.intrinsic!=LEVEL_EQUAL,"Borrowed Level equality requires an owned guest wrapper"); require(!borrowedExprLooseQuery(e.target.intrinsic),"Borrowed Expr loose search requires an owned guest wrapper"); require(!borrowedExprOrder(e.target.intrinsic),"Borrowed Expr quick ordering requires an owned guest wrapper"); require(!findPrimitive(e.target.intrinsic),"Borrowed Expr.find requires an owned guest wrapper"); require(e.target.intrinsic!=SHARECOMMON_QUICK,"Borrowed ShareCommon requires an owned guest wrapper"); require(e.target.intrinsic!=EXPR_REPLACE,"Borrowed Expr.replace requires an owned guest wrapper"); require(!abstractPrimitive(e.target.intrinsic),"Borrowed Expr abstraction requires an owned guest wrapper"); require(!pureExprTransform(e.target.intrinsic),"Borrowed Expr instantiation/lift requires an owned guest wrapper"); require(e.target.intrinsic!=POINTER_IDENTITY,"Pointer identity requires a certified direct FAP site"); require(!borrowedRefPrimitive(e.target.intrinsic),"Borrowed ref primitive requires owned closure wrapper"); for(int i=0;i<e.target.paramTypes.length;i++) require(e.target.paramTypes[i]==OBJ,"Unboxed partial target unsupported; boxed wrapper required"); for(int a:e.args) require(lane(env,a)==OBJ,"Partial argument must be boxed"); break;
                    case AP: require(b.type==OBJ&&lane(env,e.a)==OBJ&&e.args.length>0,"Unsupported closure application"); for(int a:e.args) require(lane(env,a)==OBJ,"Closure argument must be boxed"); break;
                    case BOX: require(b.type==OBJ&&e.b!=OBJ&&lane(env,e.a)==e.b,"Box lane mismatch"); break;
                    case UNBOX: require(b.type!=OBJ&&lane(env,e.a)==OBJ,"Unbox lane mismatch"); break;
                    case SHARED: require(b.type==U8&&lane(env,e.a)==OBJ,"Sharing-test lane mismatch"); break;
                    case LIT: if(b.type==F64) e.literal=Long.valueOf(Double.doubleToRawLongBits(nat(e.literal).doubleValue()));
                              else if(b.type==F32) e.literal=Long.valueOf(Integer.toUnsignedLong(Float.floatToRawIntBits(nat(e.literal).floatValue())));
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
            case CASE: require(b.type!=F64&&b.type!=F32,"Float case outside execution profile"); require(lane(env,b.a)==b.type,"Case lane mismatch"); for(Body alt:b.alternatives) validateBody(alt,f,env,joins,seen); break;
            case RET: require(lane(env,b.a)==f.resultType,"Return lane mismatch"); break;
            case SET: require(lane(env,b.a)==OBJ&&lane(env,b.args[0])==OBJ,"Field store lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
            case SSET: require(lane(env,b.a)==OBJ&&(b.type==U8||b.type==U16||b.type==U32||b.type==U64||b.type==F64||b.type==F32)&&lane(env,b.args[0])==b.type,"Scalar store lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
            case USET: require(lane(env,b.a)==OBJ&&lane(env,b.args[0])==USIZE,"USize store lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
            case INC: case DEC: case DEL: case SETTAG: require(lane(env,b.a)==OBJ,"Object instruction lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
            case UNREACHABLE: break;
            default: throw error("Invalid body opcode");
        }
    }
    /** Separate immutable capabilities: local equality and the exact hash chain.
     * Structural recognition alone never authorizes execution of a hash body. */
    private static final class PointerCertificates {
        final Set<Expr> equality,hash;
        PointerCertificates(Set<Expr> equality,Set<Expr> hash) {
            this.equality=equality.isEmpty()?null:Collections.unmodifiableSet(equality);
            this.hash=hash.isEmpty()?null:Collections.unmodifiableSet(hash);
        }
    }
    private static Set<Expr> pointerIdentitySet() { return Collections.newSetFromMap(new IdentityHashMap<>()); }
    private static PointerCertificates certifyPointerObservations(Body body) {
        Set<Expr> equality=pointerIdentitySet(),hash=pointerIdentitySet();
        if(body==null) return new PointerCertificates(equality,hash);
        Map<Integer,Expr> definitions=new HashMap<>(); collectPointerDefinitions(body,definitions);
        if(definitions.isEmpty()) return new PointerCertificates(equality,hash);
        Map<Integer,Expr> converted=new HashMap<>(); Set<Integer> salts=new HashSet<>();
        collectPointerHashDefinitions(body,definitions,converted,salts);
        Set<Integer> used=new HashSet<>(),convertedUsed=new HashSet<>();
        checkPointerUses(body,definitions,converted,salts,used,convertedUsed,equality,hash);
        require(used.containsAll(definitions.keySet()),"Unused pointer identity observation is outside the certified profile");
        require(convertedUsed.containsAll(converted.keySet()),"Unused pointer hash conversion is outside the certified profile");
        return new PointerCertificates(equality,hash);
    }
    // Retained private checker entry used by the original equality audit tests.
    private static Set<Expr> certifyPointerSites(Body body) { return certifyPointerObservations(body).equality; }
    private static void collectPointerDefinitions(Body body,Map<Integer,Expr> definitions) {
        switch(body.op) {
            case VDECL:
                if(body.expr.op==FAP&&body.expr.target.intrinsic==POINTER_IDENTITY) {
                    require(body.type==USIZE,"Invalid pointer identity result lane"); definitions.put(body.a,body.expr);
                }
                collectPointerDefinitions(body.next,definitions); break;
            case JDECL: collectPointerDefinitions(body.body,definitions); collectPointerDefinitions(body.next,definitions); break;
            case CASE: for(Body alternative:body.alternatives) collectPointerDefinitions(alternative,definitions); break;
            case SET: case SSET: case USET: case SETTAG: case INC: case DEC: case DEL: collectPointerDefinitions(body.next,definitions); break;
            case RET: case JMP: case UNREACHABLE: break;
            default: throw error("Unaudited pointer identity body opcode");
        }
    }
    private static void collectPointerHashDefinitions(Body body,Map<Integer,Expr> raw,Map<Integer,Expr> converted,Set<Integer> salts) {
        switch(body.op) {
            case VDECL: {
                Expr e=body.expr;
                if(e.op==LIT&&body.type==U64&&Long.valueOf(11).equals(e.literal)) salts.add(body.a);
                if(e.op==FAP&&e.target.intrinsic==USIZE_TO_U64&&e.args.length==1&&raw.containsKey(e.args[0])) {
                    require(body.type==U64,"Pointer hash conversion requires U64 result"); converted.put(body.a,e);
                }
                collectPointerHashDefinitions(body.next,raw,converted,salts); break;
            }
            case JDECL: collectPointerHashDefinitions(body.body,raw,converted,salts); collectPointerHashDefinitions(body.next,raw,converted,salts); break;
            case CASE: for(Body alternative:body.alternatives) collectPointerHashDefinitions(alternative,raw,converted,salts); break;
            case SET: case SSET: case USET: case SETTAG: case INC: case DEC: case DEL: collectPointerHashDefinitions(body.next,raw,converted,salts); break;
            case RET: case JMP: case UNREACHABLE: break;
            default: throw error("Unaudited pointer hash body opcode");
        }
    }
    private static void noPointerUse(int variable,Map<Integer,Expr> raw,Map<Integer,Expr> converted) {
        require(!raw.containsKey(variable)&&!converted.containsKey(variable),"Pointer observation escapes certified equality/hash uses");
    }
    private static void noPointerUses(int[] variables,Map<Integer,Expr> raw,Map<Integer,Expr> converted) {
        for(int variable:variables) noPointerUse(variable,raw,converted);
    }
    private static void checkPointerUses(Body body,Map<Integer,Expr> raw,Map<Integer,Expr> converted,Set<Integer> salts,
                                         Set<Integer> used,Set<Integer> convertedUsed,Set<Expr> equality,Set<Expr> hash) {
        switch(body.op) {
            case VDECL: {
                Expr e=body.expr;
                switch(e.op) {
                    case FAP:
                        if(e.target.intrinsic==USIZE_EQ&&e.args.length==2&&(raw.containsKey(e.args[0])||raw.containsKey(e.args[1]))) {
                            require(raw.containsKey(e.args[0])&&raw.containsKey(e.args[1]),"Pointer identity equality requires two direct fresh-pointer definitions");
                            for(int argument:e.args) { used.add(argument); equality.add(raw.get(argument)); }
                        } else if(converted.get(body.a)==e) { used.add(e.args[0]); }
                        else if(e.target.intrinsic==U64_MIX&&e.args.length==2&&converted.containsKey(e.args[0])) {
                            require(salts.contains(e.args[1]),"Pointer hash requires dominating direct U64 literal salt 11");
                            convertedUsed.add(e.args[0]); hash.add(raw.get(converted.get(e.args[0]).args[0]));
                            noPointerUse(e.args[1],raw,converted);
                        } else noPointerUses(e.args,raw,converted);
                        break;
                    case CTOR: case PAP: noPointerUses(e.args,raw,converted); break;
                    case AP: noPointerUse(e.a,raw,converted); noPointerUses(e.args,raw,converted); break;
                    case PROJ: case SPROJ: case UPROJ: case BOX: case UNBOX: case SHARED: noPointerUse(e.a,raw,converted); break;
                    case LIT: break;
                    default: throw error("Unaudited pointer identity expression opcode");
                }
                checkPointerUses(body.next,raw,converted,salts,used,convertedUsed,equality,hash); break;
            }
            case JDECL: checkPointerUses(body.body,raw,converted,salts,used,convertedUsed,equality,hash); checkPointerUses(body.next,raw,converted,salts,used,convertedUsed,equality,hash); break;
            case CASE: noPointerUse(body.a,raw,converted); for(Body alternative:body.alternatives) checkPointerUses(alternative,raw,converted,salts,used,convertedUsed,equality,hash); break;
            case SET: case SSET: case USET: noPointerUse(body.a,raw,converted); noPointerUses(body.args,raw,converted); checkPointerUses(body.next,raw,converted,salts,used,convertedUsed,equality,hash); break;
            case INC: case DEC: case DEL: case SETTAG: noPointerUse(body.a,raw,converted); checkPointerUses(body.next,raw,converted,salts,used,convertedUsed,equality,hash); break;
            case JMP: noPointerUses(body.args,raw,converted); break;
            case RET: noPointerUse(body.a,raw,converted); break;
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
        if(type==F32) {
            require(value instanceof Float,"Expected Float Float32 scalar");
            return Integer.toUnsignedLong(Float.floatToRawIntBits((Float)value));
        }
        if(type==F64) {
            require(value instanceof Double,"Expected Double Float scalar");
            return Double.doubleToRawLongBits((Double)value);
        }
        BigInteger n;
        if(value instanceof BigInteger) n=(BigInteger)value;
        else if(value instanceof Long||value instanceof Integer||value instanceof Short||value instanceof Byte)
            n=BigInteger.valueOf(((Number)value).longValue());
        else throw error("Expected exact unsigned scalar");
        int bits=type==U8?8:type==U16?16:type==U32?32:64;
        if(n.signum()<0||n.bitLength()>bits) throw error("Unsigned scalar outside "+bits+"-bit range");
        return n.longValue();
    }
    private static Object externalScalar(long value,int type) {
        if(type==F32) return Float.valueOf(Float.intBitsToFloat((int)value));
        if(type==F64) return Double.valueOf(Double.longBitsToDouble(value));
        if((type==USIZE||type==U64)&&value<0) return BigInteger.valueOf(value&Long.MAX_VALUE).setBit(63);
        return Long.valueOf(value);
    }
    /** Typed suspended control state only; never an admitted OBJ carrier. */
    private static final class F64Bits {
        final long bits;
        F64Bits(long bits) { this.bits=bits; }
    }
    private static final class F32Bits {
        final int bits;
        F32Bits(int bits) { this.bits=bits; }
    }
    private static Object saveScalar(long bits,int lane) {
        return lane==F32?new F32Bits((int)bits):lane==F64?new F64Bits(bits):externalScalar(bits,lane);
    }
    private static long readSavedScalar(Object value,int lane) {
        if(lane==F32&&value instanceof F32Bits) return Integer.toUnsignedLong(((F32Bits)value).bits);
        return lane==F64&&value instanceof F64Bits?((F64Bits)value).bits:inputScalar(value,lane);
    }
    private static Object[] argumentViews(Function function,Object[] arguments) {
        Object[] views=arguments.clone();
        for(int i=0;i<views.length;i++) if(function.paramTypes[i]==F64||function.paramTypes[i]==F32)
            views[i]=externalScalar(readSavedScalar(views[i],function.paramTypes[i]),function.paramTypes[i]);
        return views;
    }
    private static int scalarWidth(int type) { return type==U8?1:type==U16?2:(type==U32||type==F32)?4:8; }
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
        if(type==F32) {
            Node n=new Node(0,0,4); writeScalar(n,0,type,value); allocations++; return n;
        }
        if(type==USIZE||type==U64||type==F64) {
            Node n=new Node(0,0,8); writeScalar(n,0,type,value); allocations++; return n;
        }
        return Long.valueOf(type==U8?value&255:type==U16?value&65535:value&0xffffffffL);
    }
    private long unboxScalar(Object value,int type) {
        if(type==F32) {
            Node n=constructorNode(value);
            require(n.tag==0&&n.fields.length==0&&n.scalars.length==4&&n.closure==null,"Expected boxed Float32");
            return readScalar(n,0,type);
        }
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
        if(f.intrinsic==BYTE_COPY_SLICE) {
            byteCopySlice(obj(slots[0]),obj(slots[1]),obj(slots[2]),obj(slots[3]),obj(slots[4]),numbers[bp+slots[5]]); return;
        }
        if(f.intrinsic==MARK_PERSISTENT) { persistentIntrinsic(obj(slots[0]),obj(slots[1]),obj(slots[2])); return; }
        if(f.intrinsic==VOID_MK) { voidIntrinsic(obj(slots[0]),obj(slots[1])); return; }
        require(f.intrinsic!=TASK_MAP,"Task.map requires its runtime frame");
        if(floatPrimitive(f.intrinsic)) {
            floatIntrinsic(f,numbers[bp+slots[0]],slots.length<2?0:numbers[bp+slots[1]]); return;
        }
        require(f.intrinsic!=POINTER_IDENTITY,"Pointer identity requires a certified direct FAP site");
        if(borrowedExprEquality(f.intrinsic)) { scalarResult=new ExprEquality(f.intrinsic==EXPR_EQUAL).apply(obj(slots[0]),obj(slots[1]))?1:0; return; }
        if(f.intrinsic==LEVEL_EQUAL) { scalarResult=new ExprEquality(false).applyLevel(obj(slots[0]),obj(slots[1]))?1:0; return; }
        if(f.intrinsic==EXPR_CACHE) { scalarResult=exprCachedData(obj(slots[0])); return; }
        if(f.intrinsic==EXPR_HAS_LOOSE) { scalarResult=new LooseBVarSearch().apply(obj(slots[0]),obj(slots[1]))?1:0; return; }
        if(f.intrinsic==EXPR_QUICK_LT) { scalarResult=new ExprOrder().apply(obj(slots[0]),obj(slots[1]))?1:0; return; }
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
        if(f.intrinsic==BYTE_COPY_SLICE) {
            byteCopySlice(args[0],args[1],args[2],args[3],args[4],inputScalar(args[5],U8)); return;
        }
        if(f.intrinsic==MARK_PERSISTENT) { persistentIntrinsic(args[0],args[1],args[2]); return; }
        if(f.intrinsic==VOID_MK) { voidIntrinsic(args[0],args[1]); return; }
        require(f.intrinsic!=TASK_MAP,"Task.map requires its runtime frame");
        if(floatPrimitive(f.intrinsic)) {
            floatIntrinsic(f,readSavedScalar(args[0],f.paramTypes[0]),args.length<2?0:readSavedScalar(args[1],f.paramTypes[1])); return;
        }
        require(f.intrinsic!=POINTER_IDENTITY,"Pointer identity requires a certified direct FAP site");
        if(borrowedExprEquality(f.intrinsic)) { scalarResult=new ExprEquality(f.intrinsic==EXPR_EQUAL).apply(args[0],args[1])?1:0; return; }
        if(f.intrinsic==LEVEL_EQUAL) { scalarResult=new ExprEquality(false).applyLevel(args[0],args[1])?1:0; return; }
        if(f.intrinsic==EXPR_CACHE) { scalarResult=exprCachedData(args[0]); return; }
        if(f.intrinsic==EXPR_HAS_LOOSE) { scalarResult=new LooseBVarSearch().apply(args[0],args[1])?1:0; return; }
        if(f.intrinsic==EXPR_QUICK_LT) { scalarResult=new ExprOrder().apply(args[0],args[1])?1:0; return; }
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
    private static boolean floatPrimitive(int op) { return op>=FLOAT_BITS&&op<=FLOAT_STRING||op==FLOAT_LE; }
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
            case FLOAT_LE: scalarResult=x<=y?1:0; break;
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
    private static boolean advancedArrayPrimitive(int op) { return op>=ARRAY_EMPTY&&op<=ARRAY_REPLICATE||op==ARRAY_CHECKED_GET||op==ARRAY_CHECKED_BORROWED||op==ARRAY_CHECKED_SET; }
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
        if(f.intrinsic!=ARRAY_CHECKED_GET&&f.intrinsic!=ARRAY_CHECKED_BORROWED&&f.intrinsic!=ARRAY_CHECKED_SET&&f.params.length>=4)
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
    /** Native set! has a distinct panic path; the current profile rejects it
     * before claims instead of executing the pure source fallback. */
    private static int checkedArraySetIndex(Node array,Object index) {
        BigInteger n=nat(index);
        require(n.compareTo(BigInteger.valueOf(arrayState(array).size))<0,
                "Array.set! panic path outside bounded runtime profile");
        return n.intValue();
    }
    private void validateCheckedArraySet(Object[] args) {
        require(args!=null&&args.length==4,"Array.set! native arity mismatch");
        require(ERASED.equals(args[0]),"Array erased parameter requires erased placeholder");
        Node source=array(args[1]); int index=checkedArraySetIndex(source,args[2]);
        validateHostObject(args[3]); refIncomingAlias(source.fields[index],args[3]);
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
            case ARRAY_FSET: case ARRAY_USET: case ARRAY_CHECKED_SET: {
                int index=f.intrinsic==ARRAY_CHECKED_SET?checkedArraySetIndex(n,b):arrayIndex(n,b); validateHostObject(c);
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
    private static boolean borrowedBytePrimitive(int op) {
        return op==BYTE_GET||op==BYTE_SIZE||op==BYTE_EMPTY||op==STR_VALIDATE_UTF8||op==BYTE_COPY_SLICE;
    }
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
        if(f.intrinsic==BYTE_EMPTY) {
            // lean.h lean_mk_empty_byte_array borrows Nat capacity, rejects a
            // non-scalar Nat via OOM, and allocates element-size 1 / live-size 0.
            // The supported profile bounds scalar capacity to the existing 16MiB
            // ByteArray limit; reject before allocation or any ownership change.
            BigInteger capacity=nat(a);
            require(capacity.compareTo(BigInteger.valueOf(MAX_BYTE_CAPACITY))<=0,
                    "ByteArray capacity outside bounded runtime profile");
            result=newByteArray(0,capacity.intValue()); return;
        }
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
    /** Pinned runtime/utf8.cpp validator over the live prefix, with no ownership effects. */
    private static boolean validUtf8(byte[] bytes,int size) {
        for(int at=0;at<size;) {
            int c=Byte.toUnsignedInt(bytes[at]);
            if(c<0x80) { at++; continue; }
            int length,min,code;
            if((c&0xe0)==0xc0) { length=2; min=0x80; code=c&0x1f; }
            else if((c&0xf0)==0xe0) { length=3; min=0x800; code=c&0x0f; }
            else if((c&0xf8)==0xf0) { length=4; min=0x10000; code=c&7; }
            else return false;
            if(length>size-at) return false;
            for(int i=1;i<length;i++) {
                int continuation=Byte.toUnsignedInt(bytes[at+i]);
                if((continuation&0xc0)!=0x80) return false;
                code=(code<<6)|(continuation&0x3f);
            }
            if(code<min||code>0x10ffff||(code>=0xd800&&code<=0xdfff)) return false;
            at+=length;
        }
        return true;
    }
    private int utf8Extent(Object value) {
        String text=text(value); long size=0;
        for(int i=0;i<text.length();i++) {
            char ch=text.charAt(i);
            if(Character.isHighSurrogate(ch)) {
                require(i+1<text.length()&&Character.isLowSurrogate(text.charAt(i+1)),"Invalid Unicode String"); i++; size+=4;
            } else {
                require(!Character.isLowSurrogate(ch),"Invalid Unicode String");
                size+=ch<0x80?1:ch<0x800?2:3;
            }
            require(size<=MAX_BYTE_CAPACITY,"UTF8 conversion outside bounded byte capacity profile");
        }
        return (int)size;
    }
    private void stringToUtf8(Object value) {
        int size=utf8Extent(value); byte[] encoded=utf8(value);
        require(encoded.length==size,"UTF8 encoded extent differs");
        Node out=newByteArray(size,size);
        // utf8() may return the immutable String cache; never expose its array.
        System.arraycopy(encoded,0,out.scalars,0,size); result=out;
    }
    private Node validateFromUtf8(Object value,Object proof) {
        require(ERASED.equals(proof),"String.ofByteArray proof requires erased placeholder");
        Node bytes=byteArray(value); int size=((ByteArrayState)kindMetadata(bytes)).size;
        require(validUtf8(bytes.scalars,size),"Malformed unchecked UTF8 String outside JVM Unicode profile");
        return bytes;
    }
    private void stringFromUtf8(Object value,Object proof) {
        Node bytes=validateFromUtf8(value,proof); int size=((ByteArrayState)kindMetadata(bytes)).size;
        String out=new String(bytes.scalars,0,size,StandardCharsets.UTF_8);
        // ByteArray storage has no guest-valued fields/finalizers.
        releaseQuiet(bytes,1); result=out;
    }
    private static BigInteger byteSizeT(Object value) {
        require(!(value instanceof BigInteger)||value.getClass()==BigInteger.class,"ByteArray size_t requires immutable Nat carrier");
        BigInteger n=nat(value);
        require(n.bitLength()<=64,"ByteArray size_t argument outside native unsigned64 profile"); return n;
    }
    private void byteCopySlice(Object source,Object sourceOffset,Object destination,Object destinationOffset,Object length,long exact) {
        Node src=byteArray(source),dest=byteArray(destination);
        require(exact==0||exact==1,"ByteArray.copySlice exact requires canonical Bool");
        int sourceSize=((ByteArrayState)kindMetadata(src)).size,destSize=((ByteArrayState)kindMetadata(dest)).size;
        BigInteger sourceStart=byteSizeT(sourceOffset);
        // The pinned native returns before converting the other owned Nat arguments.
        if(sourceStart.compareTo(BigInteger.valueOf(sourceSize))>0) { result=dest; return; }
        int from=sourceStart.intValue();
        int count=byteSizeT(length).min(BigInteger.valueOf(sourceSize-from)).intValue();
        int to=byteSizeT(destinationOffset).min(BigInteger.valueOf(destSize)).intValue();
        int next=Math.max(destSize,Math.addExact(to,count));
        int capacity=next<=dest.scalars.length?dest.scalars.length:exact==1?next:Math.multiplyExact(next,2);
        require(capacity<=MAX_BYTE_CAPACITY,"ByteArray capacity outside bounded runtime profile");
        boolean copy=!exclusive(dest)||capacity!=dest.scalars.length;
        if(src==dest&&dest.rc==1) {
            require(!copy,"One-credit source/destination alias cannot outlive ByteArray copy");
            require(count==0||to+count<=from||from+count<=to,
                    "Overlapping exclusive ByteArray memcpy outside native-safe profile");
        }
        Node out=dest;
        if(copy) {
            out=newByteArray(destSize,capacity);
            System.arraycopy(dest.scalars,0,out.scalars,0,destSize);
            releaseQuiet(dest,1);
        }
        System.arraycopy(src.scalars,from,out.scalars,to,count);
        ((ByteArrayState)kindMetadata(out)).size=next; stores++; result=out;
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
    private Node capturedStream(boolean stderr) {
        Node stream=new Node(0,6,0); allocations++;
        for(int i=0;i<6;i++) {
            int arity=i==1||i==2||i==4?2:1;
            int[] parameters=new int[arity],paramTypes=new int[arity];
            for(int p=0;p<arity;p++) parameters[p]=p+1;
            Function f=new Function((stderr?"<captured-stderr.":"<captured-stream.")+i+">",-1,parameters,paramTypes,
                                    OBJ,stderr&&i==4?STDERR_PUT:STREAM_FLUSH+i,null,runtimeIdentity);
            stream.fields[i]=closure(f,new Object[0]);
        }
        return stream;
    }
    private Node defaultStream(int channel) {
        if(channel==0) { require(stdinDefaultRoot!=null,"Configured stdin default is unavailable"); return stdinDefaultRoot; }
        if(channel==1) { if(stdoutRoot==null) stdoutRoot=capturedStream(false); return stdoutRoot; }
        if(stderrRoot==null) stderrRoot=capturedStream(true); return stderrRoot;
    }
    private Node stdout() {
        if(stdioContext!=null) return standardStream(1,false,null);
        Node stream=defaultStream(1); inc(stream,1); return stream;
    }
    public String capturedStdout() { return output.toString(); }
    public String capturedStderr() { return stderrOutput.toString(); }
    private Node streamNode(Object value) {
        Node stream=constructorNode(value);
        require(stream.rc>=0,"Invalid FS.Stream reference count");
        require(stream.tag==0&&stream.fields.length==6&&stream.scalars.length==0&&stream.closure==null,
                "Expected six-method FS.Stream");
        for(int i=0;i<6;i++) {
            Node method=node(stream.fields[i]); acceptsClosure(method);
            int remaining=method.closure.params.length-method.fields.length;
            require(method.tag==245&&method.scalars.length==0&&remaining==(i==1||i==2||i==4?2:1)
                    &&method.closure.resultType==OBJ,"Invalid FS.Stream method closure ABI");
            for(int j=method.fields.length;j<method.closure.paramTypes.length;j++)
                require(method.closure.paramTypes[j]==OBJ,"FS.Stream method needs an original boxed facade");
        }
        return stream;
    }
    /** Read-only bounded graph proof, INCLUDING persistent rc0 subgraphs. This
     * is a quiet default-release profile, not a universal branch ownership seal. */
    private void quietStdioGraph(Object root) {
        IdentityHashMap<Node,Boolean> seen=new IdentityHashMap<>(); ArrayDeque<Object> todo=new ArrayDeque<>();
        todo.push(root); int edges=0;
        while(!todo.isEmpty()) {
            Object value=todo.pop();
            if(!(value instanceof Node)) { validateHostObject(value); continue; }
            Node n=node(value); require(n.rc>=0,"Invalid stdio default reference count"); if(seen.put(n,Boolean.TRUE)!=null) continue;
            require(seen.size()<=300_000,"Stdio default graph node bound exceeded");
            NodeMetadata kind=kindMetadata(n);
            require(!(kind instanceof TaskMetadata)&&!n.readyTask,"Stdio defaults reject Task/Promise lifecycle");
            if(n.array) array(n);
            else if(isByteArray(n)) byteArray(n);
            else if(n.ref) reference(n);
            else if(n.closure!=null) {
                require(n.tag==245&&n.scalars.length==0,"Unknown stdio default closure kind"); acceptsClosure(n);
            } else require(kind==null&&n.tag>=0&&n.tag<=243,"Unsupported stdio default object kind");
            int live=owningFieldCount(n);
            require(live>=0&&live<=n.fields.length&&edges<=1_000_000-live,"Stdio default graph edge bound exceeded"); edges+=live;
            for(int i=0;i<live;i++) { require(n.fields[i]!=null,"Absent stdio default owning field"); todo.push(n.fields[i]); }
            if(Thread.currentThread().isInterrupted()) throw error("Stdio default validation interrupted");
        }
    }
    private static final String[] STDIN_METHOD_LABELS={
        "IO.FS.Stream.ofBuffer._lam_4._boxed","IO.FS.Stream.ofBuffer._lam_0._boxed",
        "IO.FS.Stream.ofBuffer._lam_1._boxed","IO.FS.Stream.ofBuffer._lam_3._boxed",
        "IO.FS.Stream.ofBuffer._lam_2._boxed","IO.FS.instInhabitedStream.default._lam_5._boxed"};
    // These exact original body identities are checked against issued Headers;
    // accepted raw CAS/index authentication remains the trusted source adapter's job.
    private static final String[] STDIN_METHOD_SHA={
        "e832604259e5794a331574c8a391637cde19e6f28ec322fc86a376a87b6c0c83","29e0f37498cc280d39c84ad0fa70336c5713b90308e32ee960d4ba28a7afbcac",
        "370ad89209e61c6fbe137e22e27d42200c02f50bb90cbaff442868ca0ecbd24a","41ab29cdd05e589e44148a3f6051b995992290d55733ab2bd234a1bed4c13ae6",
        "27399d0e9fd073070f6cc12f7d726b8c3d91cf17ec30e478eca80a81becfaa35","67b99a70a0d3bacecd41baf5e321468782636888e2b7a45febc15918216a7e89"};
    /** Borrow an actual original empty Stream.ofBuffer; acquire one default
     * owner only after all graph/header/layout/RC checks. No guest call occurs.
     * Caller authenticates source/CAS and keeps its borrowed input owner alive. */
    public void installStdioDefaults(Header ofBuffer,Object input) {
        if(closed||disposed||advancing||phase!=IDLE||pendingOwnedResult||sp!=0||continuationDepth!=0
                ||runtimeAction!=null||hostCompletion!=null||untrackedFailure||stdioContext!=null)
            throw new IllegalStateException("Stdio defaults require an open idle unconfigured engine");
        require(ofBuffer!=null&&ofBuffer.kind.equals("fdecl")
                &&Interpreter.name(ofBuffer.exactName).equals("IO.FS.Stream.ofBuffer")
                &&ofBuffer.originalSha256.equals("c98d47dcb02a469b6615689c519e3f000251ce95be5363c67a5354e8fc43108e"),
                "Actual original Stream.ofBuffer Header required");
        program.functionId(ofBuffer);
        Node stream=streamNode(input); quietStdioGraph(stream);
        Node ref=null;
        for(int i=0;i<6;i++) {
            Node method=node(stream.fields[i]); Header h=method.closure.header;
            require(h!=null&&h.source==ofBuffer.source&&Interpreter.name(h.exactName).equals(STDIN_METHOD_LABELS[i])
                    &&h.originalSha256.equals(STDIN_METHOD_SHA[i])&&method.fields.length==1,
                    "Default stdin differs from original Stream.ofBuffer method source");
            if(i==0||i==5) require(ERASED.equals(method.fields[0]),"Default stdin pure method capture differs");
            else { Node r=reference(method.fields[0]); if(ref==null) ref=r;
                   else require(ref==r,"Default stdin methods do not share the same buffer Ref"); }
        }
        Node buffer=constructorNode(ref.fields[0]);
        require(buffer.closure==null&&buffer.tag==0&&buffer.fields.length==2&&buffer.scalars.length==0
                &&ERASED.equals(buffer.fields[1])&&byteArray(buffer.fields[0]).byteArraySize()==0,
                "Default stdin requires an actual initially empty Stream.Buffer");
        if(stdoutRoot!=null) { streamNode(stdoutRoot); quietStdioGraph(stdoutRoot); }
        StdioContext context=new StdioContext(); // allocation before owner acquisition/publication
        if(stream.rc!=0) Math.addExact(stream.rc,1);
        inc(stream,1); stdinDefaultRoot=stream; stdioContext=context;
    }
    private Node ownedStdioReplacement(Object replacement) {
        require(stdioContext!=null,"Explicit configured stdio profile required");
        Node next=streamNode(replacement);
        int known=(next==stdinDefaultRoot?1:0)+(next==stdoutRoot?1:0)+(next==stderrRoot?1:0);
        for(Node stream:stdioContext.current) if(stream==next) known++;
        // Reserve EACH private owning occurrence, including cross-channel
        // aliases. An incoming owned argument must exist beyond those roots.
        // This is a narrow known-credit defense, not a universal heap ledger.
        require(next.rc==0||next.rc>known,"Stdio replacement requires an owner beyond known default/current roots");
        return next;
    }
    private Node standardStream(int channel,boolean swap,Object replacement) {
        require(stdioContext!=null,"Explicit configured stdio profile required");
        Node next=swap?ownedStdioReplacement(replacement):null; // validate before lazy/default mutation
        Node old=stdioContext.current[channel];
        Node seed=streamNode(old==null?defaultStream(channel):old);
        int credits=(old==null?1:0)+(swap?0:1);
        if(seed.rc!=0) Math.addExact(seed.rc,credits);
        if(old==null) { inc(seed,1); stdioContext.current[channel]=seed; }
        if(swap) { stdioContext.current[channel]=next; return seed; }
        inc(seed,1); return seed;
    }
    private Node stdioDefault(int channel) { return channel==0?stdinDefaultRoot:channel==1?stdoutRoot:stderrRoot; }
    private void clearStdioDefault(int channel) {
        if(channel==0) stdinDefaultRoot=null; else if(channel==1) stdoutRoot=null; else stderrRoot=null;
    }
    private boolean currentStdioRoots() {
        for(Node stream:stdioContext.current) if(stream!=null) return true; return false;
    }
    private boolean stdioRoots() {
        return stdoutRoot!=null||stdinDefaultRoot!=null||stderrRoot!=null||(stdioContext!=null&&currentStdioRoots());
    }
    private void stepStdioDispose(RuntimeAction action) {
        if(action.stage==0) {
            if(action.cursor<3) {
                int channel=action.cursor++; Node old=stdioContext.current[channel];
                action.retiring=old; action.releaseClaimed=false; stdioContext.current[channel]=null;
                if(old!=null) { beginRelease(old,1,ACTION_BODY); action.releaseClaimed=true; }
            } else if(action.cursor<constants.length+3) {
                int index=action.cursor++-3;
                if(constantReady[index]) {
                    Object old=constants[index]; action.retiring=old; action.releaseClaimed=false;
                    constants[index]=null; constantReady[index]=false; constantRetired[index]=true;
                    if(program.functions[index].resultType==OBJ) { beginRelease(old,1,ACTION_BODY); action.releaseClaimed=true; }
                }
            } else {
                if(currentStdioRoots()) { action.cursor=0; return; }
                for(boolean ready:constantReady) if(ready) { action.cursor=0; return; }
                for(TaskRecord record:taskRecords.values()) if(record.keepalive) { phase=WAITING; return; }
                action.stage=1; action.cursor=0;
            }
        } else if(action.cursor<3) {
            // Validate all owned defaults immediately before the FIRST claim;
            // no guest advance or owner transfer separates this check/claim.
            // Also recheck each remaining graph at its own claim boundary.
            if(action.cursor==0) for(int i=0;i<3;i++) if(stdioDefault(i)!=null) quietStdioGraph(stdioDefault(i));
            int channel=action.cursor; Node old=stdioDefault(channel);
            if(old!=null) quietStdioGraph(old);
            action.cursor++;
            action.retiring=old; action.releaseClaimed=false; clearStdioDefault(channel);
            if(old!=null) { beginRelease(old,1,ACTION_BODY); action.releaseClaimed=true; }
        } else { require(!stdioRoots(),"Stdio roots recreated during callback-free default retirement"); disposed=true; finishAction(action,ERASED); }
    }
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
    private boolean nameEquals(Object left,Object right) { return nameEquals(left,right,null); }
    private boolean nameEquals(Object left,Object right,ExprEquality budget) {
        Node a=nameNode(left),b=nameNode(right);
        if(a==null||b==null) return a==b;
        if(a==b) return true;
        if(readScalar(a,0,U64)!=readScalar(b,0,U64)) return false;
        for(int steps=0;steps<MAX_NAME_COMPARISON_STEPS;steps++) {
            if(budget!=null) budget.charge(1);
            if(a.tag!=b.tag) return false;
            Object x=a.fields[1],y=b.fields[1];
            if(a.tag==1) {
                if(budget!=null) { if(!budget.string(x,y)) return false; }
                else if(!((String)x).equals((String)y)) return false;
            } else if(x instanceof Long&&y instanceof Long) {
                if(((Long)x).longValue()!=((Long)y).longValue()) return false;
            } else if(budget!=null) { if(!budget.number(x,y,false)) return false; }
            else if(!nat(x).equals(nat(y))) return false;
            a=nameNode(a.fields[0]); b=nameNode(b.fields[0]);
            if(a==null||b==null) return a==b;
            if(a==b) return true;
            // Native lean_name_eq deliberately omits repeated parent hash tests.
        }
        throw error("Name equality depth/cycle outside bounded runtime profile");
    }
    private Node levelNode(Object value) {
            if(value instanceof Long&&((Long)value)==0) return null;
            Node n=constructorNode(value); require(n.closure==null&&n.rc>=0&&n.tag>=1&&n.tag<=5,"Expected Level constructor kind");
            require(n.fields.length==(n.tag==2||n.tag==3?2:1)&&n.scalars.length==8,"Unexpected Level cached-data storage layout"); return n;
    }
    private static final int EQ_EXPR=1,EQ_APP_SPINE=2,EQ_LEVEL=3,EQ_LEVELS=4,EQ_MDATA=5,EQ_PAIR=6,
            EQ_VALUE=7,EQ_LITERAL=8,EQ_SYNTAX=9,EQ_SYNTAX_ARRAY=10,EQ_PRERESOLVED=11,
            EQ_PRERESOLVED_LIST=12,EQ_STRINGS=13,EQ_NAME=14,EQ_NAT=15,EQ_INT=16,
            EQ_STRING=17,EQ_SUBSTRING=18,EQ_BOOL=19,EQ_BINDER=20;
    private static final int MAX_EXPR_EQUALITY_WORK=1_000_000,MAX_EXPR_EQUALITY_PAIRS=100_000,MAX_EXPR_EQUALITY_STACK=100_000;
    private static final class EqualityKey {
        final int kind; final Object left,right;
        EqualityKey(int kind,Object left,Object right) { this.kind=kind; this.left=left; this.right=right; }
        public int hashCode() { return 31*(31*kind+System.identityHashCode(left))+System.identityHashCode(right); }
        public boolean equals(Object other) {
            if(!(other instanceof EqualityKey)) return false;
            EqualityKey key=(EqualityKey)other; return kind==key.kind&&left==key.left&&right==key.right;
        }
    }
    private static final class EqualityFrame {
        final EqualityKey key; final boolean finish;
        EqualityFrame(EqualityKey key,boolean finish) { this.key=key; this.finish=finish; }
    }
    /** Invocation-local, read-only bounded equality. No scratch escapes through
     * Program/Node metadata or failures. This is not native heartbeat accounting. */
    private final class ExprEquality {
        final boolean compareBinders;
        final ArrayDeque<EqualityFrame> stack=new ArrayDeque<>();
        final HashMap<EqualityKey,Boolean> states=new HashMap<>();
        long work;
        ExprEquality(boolean compareBinders) { this.compareBinders=compareBinders; }
        void charge(long amount) {
            require(amount>=0&&amount<=MAX_EXPR_EQUALITY_WORK-work,"Expr equality work outside bounded runtime profile");
            long before=work; work+=amount;
            if((before>>>10)!=(work>>>10)&&Thread.currentThread().isInterrupted()) throw error("Expr equality interrupted outside bounded runtime profile");
        }
        void push(int kind,Object left,Object right) {
            require(stack.size()<MAX_EXPR_EQUALITY_STACK,"Expr equality stack outside bounded runtime profile");
            stack.push(new EqualityFrame(new EqualityKey(kind,left,right),false));
        }
        boolean string(Object left,Object right) {
            require(left instanceof String&&right instanceof String,"Expected equality String carriers");
            charge((long)((String)left).length()+((String)right).length());
            return left.equals(right);
        }
        boolean number(Object left,Object right,boolean signed) {
            BigInteger a=signed?signedInteger(left):nat(left),b=signed?signedInteger(right):nat(right);
            charge(1L+(a.bitLength()+63L)/64+(b.bitLength()+63L)/64); return a.equals(b);
        }
        Node ctor(Object value,int fields,int scalarBytes) {
            Node n=constructorNode(value); require(n.closure==null&&n.rc>=0,"Expected live ordinary equality constructor");
            require(n.fields.length==fields&&n.scalars.length==scalarBytes,"Unexpected equality constructor storage layout"); return n;
        }
        Node list(Object value) {
            if(value instanceof Long&&((Long)value)==0) return null;
            Node n=ctor(value,2,0); require(n.tag==1,"Expected equality List.cons layout"); return n;
        }
        Node level(Object value) { return levelNode(value); }
        Node syntax(Object value) {
            if(value instanceof Long&&((Long)value)==0) return null;
            Node n=constructorNode(value); require(n.closure==null&&n.rc>=0&&n.tag>=1&&n.tag<=3,"Expected Syntax constructor kind");
            require(n.fields.length==(n.tag==1?3:n.tag==2?2:4)&&n.scalars.length==0,"Unexpected Syntax storage layout"); return n;
        }
        boolean apply(Object left,Object right) { return applyRoot(EQ_EXPR,left,right); }
        boolean applyLevel(Object left,Object right) { return applyRoot(EQ_LEVEL,left,right); }
        private boolean applyRoot(int rootKind,Object left,Object right) {
            push(rootKind,left,right);
            while(!stack.isEmpty()) {
                EqualityFrame frame=stack.pop(); EqualityKey key=frame.key;
                if(frame.finish) { states.put(key,Boolean.TRUE); continue; }
                charge(1); Object x=key.left,y=key.right; int kind=key.kind;
                // Leaf helpers validate before their identity/equality shortcuts.
                if(kind==EQ_NAME) { if(!nameEquals(x,y,this)) return false; continue; }
                if(kind==EQ_NAT||kind==EQ_INT) { if(!number(x,y,kind==EQ_INT)) return false; continue; }
                if(kind==EQ_STRING) { if(!string(x,y)) return false; continue; }
                if(kind==EQ_BOOL||kind==EQ_BINDER) {
                    require(x instanceof Long&&y instanceof Long,"Expected cached annotation byte");
                    long a=(Long)x,b=(Long)y,max=kind==EQ_BOOL?1:3;
                    require(a>=0&&a<=max&&b>=0&&b<=max,"Annotation byte outside bounded equality profile");
                    if(a!=b) return false; continue;
                }
                if(kind==EQ_SUBSTRING) {
                    Node a=ctor(x,3,0),b=ctor(y,3,0); require(a.tag==0&&b.tag==0,"Expected Substring.Raw equality layout");
                    require(a.fields[0] instanceof String&&b.fields[0] instanceof String,"Expected Substring.Raw String");
                    charge((long)((String)a.fields[0]).length()+((String)b.fields[0]).length());
                    SubstringView av=substringView(x),bv=substringView(y);
                    if(av.size!=bv.size||!Arrays.equals(av.bytes,av.start,av.start+av.size,bv.bytes,bv.start,bv.start+bv.size)) return false;
                    continue;
                }
                Node a=null,b=null;
                switch(kind) {
                    case EQ_EXPR: case EQ_APP_SPINE: a=exprNode(x); b=exprNode(y); break;
                    case EQ_LEVEL: a=level(x); b=level(y); break;
                    case EQ_LEVELS: case EQ_MDATA: case EQ_PRERESOLVED_LIST: case EQ_STRINGS: a=list(x); b=list(y); break;
                    case EQ_PAIR: a=ctor(x,2,0); b=ctor(y,2,0); require(a.tag==0&&b.tag==0,"Expected metadata pair layout"); break;
                    case EQ_SYNTAX: a=syntax(x); b=syntax(y); break;
                    case EQ_SYNTAX_ARRAY:
                        a=array(x); b=array(y);
                        require(arrayState(a).size>=0&&arrayState(a).size<=a.fields.length&&arrayState(b).size>=0&&arrayState(b).size<=b.fields.length,"Invalid Syntax array live extent"); break;
                    case EQ_VALUE: case EQ_LITERAL: case EQ_PRERESOLVED: {
                        a=constructorNode(x); b=constructorNode(y);
                        require(a.closure==null&&b.closure==null&&a.rc>=0&&b.rc>=0,"Expected ordinary equality value constructor");
                        int max=kind==EQ_VALUE?5:1;
                        require(a.tag>=0&&a.tag<=max&&b.tag>=0&&b.tag<=max,"Unsupported equality value tag");
                        int af=kind==EQ_PRERESOLVED?(a.tag==0?1:2):kind==EQ_VALUE&&a.tag==1?0:1;
                        int bf=kind==EQ_PRERESOLVED?(b.tag==0?1:2):kind==EQ_VALUE&&b.tag==1?0:1;
                        require(a.fields.length==af&&b.fields.length==bf
                                &&(kind==EQ_VALUE&&a.tag==1?(a.scalars.length==1||a.scalars.length==8):a.scalars.length==0)
                                &&(kind==EQ_VALUE&&b.tag==1?(b.scalars.length==1||b.scalars.length==8):b.scalars.length==0),"Unexpected equality value storage layout"); break;
                    }
                    default: throw error("Invalid private equality work kind");
                }
                if(kind==EQ_LEVEL) {
                    int at=a==null?0:a.tag,bt=b==null?0:b.tag;
                    if(at!=bt) return false;
                    long ad=a==null?2221:readScalar(a,0,U64),bd=b==null?2221:readScalar(b,0,U64);
                    if((ad&0xffffffffL)!=(bd&0xffffffffL)) return false;
                    if(a==b) continue;
                    if(at<=3&&(ad>>>40)!=(bd>>>40)) return false;
                } else if(kind==EQ_EXPR) {
                    if(a==b) continue;
                    if((readScalar(a,0,U64)&0xffffffffL)!=(readScalar(b,0,U64)&0xffffffffL)) return false;
                    if(a.tag!=b.tag) return false;
                } else if(kind==EQ_APP_SPINE) {
                    // Native compares arguments while flattening the left fn
                    // spine: it does NOT compare intermediate App cached hashes.
                    if(a.tag!=5) { push(EQ_EXPR,x,y); continue; }
                    if(b.tag!=5) return false;
                    if(a==b) continue;
                } else {
                    if(a==null||b==null) { if(a!=b) return false; continue; }
                    if(a==b) continue;
                    if(a.tag!=b.tag) return false;
                }
                Boolean status=states.get(key);
                if(status!=null) { require(status,"Expr equality cycle outside bounded runtime profile"); continue; }
                require(states.size()<MAX_EXPR_EQUALITY_PAIRS,"Expr equality pair count outside bounded runtime profile");
                states.put(key,Boolean.FALSE);
                require(stack.size()<MAX_EXPR_EQUALITY_STACK,"Expr equality stack outside bounded runtime profile");
                stack.push(new EqualityFrame(key,true));
                switch(kind) {
                    case EQ_EXPR: case EQ_APP_SPINE:
                        switch(a.tag) {
                            case 0: push(EQ_NAT,a.fields[0],b.fields[0]); break;
                            case 1: case 2: push(EQ_NAME,a.fields[0],b.fields[0]); break;
                            case 3: push(EQ_LEVEL,a.fields[0],b.fields[0]); break;
                            case 4: push(EQ_LEVELS,a.fields[1],b.fields[1]); push(EQ_NAME,a.fields[0],b.fields[0]); break;
                            case 5: push(EQ_APP_SPINE,a.fields[0],b.fields[0]); push(EQ_EXPR,a.fields[1],b.fields[1]); break;
                            case 6: case 7:
                                if(compareBinders) { push(EQ_BINDER,Long.valueOf(a.scalars[8]&255),Long.valueOf(b.scalars[8]&255)); push(EQ_NAME,a.fields[0],b.fields[0]); }
                                push(EQ_EXPR,a.fields[2],b.fields[2]); push(EQ_EXPR,a.fields[1],b.fields[1]); break;
                            case 8:
                                if(compareBinders) push(EQ_NAME,a.fields[0],b.fields[0]);
                                push(EQ_BOOL,Long.valueOf(a.scalars[8]&255),Long.valueOf(b.scalars[8]&255));
                                push(EQ_EXPR,a.fields[3],b.fields[3]); push(EQ_EXPR,a.fields[2],b.fields[2]); push(EQ_EXPR,a.fields[1],b.fields[1]); break;
                            case 9: push(EQ_LITERAL,a.fields[0],b.fields[0]); break;
                            case 10: push(EQ_MDATA,a.fields[0],b.fields[0]); push(EQ_EXPR,a.fields[1],b.fields[1]); break;
                            case 11: push(EQ_NAT,a.fields[1],b.fields[1]); push(EQ_NAME,a.fields[0],b.fields[0]); push(EQ_EXPR,a.fields[2],b.fields[2]); break;
                            default: throw error("Invalid Expr equality tag");
                        } break;
                    case EQ_LEVEL:
                        if(a.tag>=4) push(EQ_NAME,a.fields[0],b.fields[0]);
                        else { if(a.tag!=1) push(EQ_LEVEL,a.fields[1],b.fields[1]); push(EQ_LEVEL,a.fields[0],b.fields[0]); } break;
                    case EQ_LEVELS: case EQ_MDATA: case EQ_PRERESOLVED_LIST: case EQ_STRINGS:
                        push(kind,a.fields[1],b.fields[1]);
                        push(kind==EQ_LEVELS?EQ_LEVEL:kind==EQ_MDATA?EQ_PAIR:kind==EQ_STRINGS?EQ_STRING:EQ_PRERESOLVED,a.fields[0],b.fields[0]); break;
                    case EQ_PAIR: push(EQ_VALUE,a.fields[1],b.fields[1]); push(EQ_NAME,a.fields[0],b.fields[0]); break;
                    case EQ_VALUE:
                        if(a.tag==1) push(EQ_BOOL,Long.valueOf(a.scalars[0]&255),Long.valueOf(b.scalars[0]&255));
                        else push(a.tag==0?EQ_STRING:a.tag==2?EQ_NAME:a.tag==3?EQ_NAT:a.tag==4?EQ_INT:EQ_SYNTAX,a.fields[0],b.fields[0]); break;
                    case EQ_LITERAL: push(a.tag==0?EQ_NAT:EQ_STRING,a.fields[0],b.fields[0]); break;
                    case EQ_SYNTAX:
                        if(a.tag==1) { push(EQ_SYNTAX_ARRAY,a.fields[2],b.fields[2]); push(EQ_NAME,a.fields[1],b.fields[1]); }
                        else if(a.tag==2) push(EQ_STRING,a.fields[1],b.fields[1]);
                        else { push(EQ_PRERESOLVED_LIST,a.fields[3],b.fields[3]); push(EQ_NAME,a.fields[2],b.fields[2]); push(EQ_SUBSTRING,a.fields[1],b.fields[1]); } break;
                    case EQ_SYNTAX_ARRAY:
                        int size=arrayState(a).size; if(size!=arrayState(b).size) return false;
                        charge(size); for(int i=size-1;i>=0;i--) push(EQ_SYNTAX,a.fields[i],b.fields[i]); break;
                    case EQ_PRERESOLVED:
                        if(a.tag==1) push(EQ_STRINGS,a.fields[1],b.fields[1]); push(EQ_NAME,a.fields[0],b.fields[0]); break;
                    default: throw error("Invalid private equality continuation");
                }
            }
            return true;
        }
    }
    private static final int LT_EXPR=1,LT_LEVEL=2,LT_LEVELS=3,LT_MDATA=4,LT_PAIR=5,LT_VALUE=6,
            LT_LITERAL=7,LT_NAME=8,LT_NAT=9,LT_STRING=10;
    private static final int MAX_EXPR_ORDER_SCRATCH=100_000,MAX_EXPR_ORDER_TOTAL_SCRATCH=300_000;
    private static final class OrderFrame {
        final EqualityKey key;
        Node left,right;
        int stage;
        boolean child,hasChild,completed,result;
        OrderFrame(int kind,Object left,Object right) { key=new EqualityKey(kind,left,right); }
    }
    /** Atomic borrowed LT, separate from semantic EQ. In particular Int/Syntax
     * metadata may be unequal while neither ordering direction is true. */
    private final class ExprOrder {
        final ArrayDeque<OrderFrame> stack=new ArrayDeque<>();
        final HashMap<EqualityKey,Byte> states=new HashMap<>(); // 0 active,1 false,2 true
        long work;
        void charge(long amount) {
            require(amount>=0&&amount<=MAX_EXPR_EQUALITY_WORK-work,"Expr ordering work outside bounded runtime profile");
            long before=work; work+=amount;
            if((before>>>10)!=(work>>>10)&&Thread.currentThread().isInterrupted()) throw error("Expr ordering interrupted");
        }
        void scratch(int extra) {
            require(extra>=0&&(long)stack.size()+states.size()+extra<=MAX_EXPR_ORDER_SCRATCH,
                    "Expr ordering combined scratch outside bounded profile");
        }
        void push(int kind,Object left,Object right) { scratch(1); stack.push(new OrderFrame(kind,left,right)); }
        void done(OrderFrame frame,boolean result) { frame.result=result; frame.completed=true; }
        boolean equal(int kind,Object left,Object right) {
            // Reserve the complete existing equality implementation's maximum
            // stack+state footprint from one explicit combined live budget.
            require((long)stack.size()+states.size()+MAX_EXPR_EQUALITY_STACK+MAX_EXPR_EQUALITY_PAIRS<=MAX_EXPR_ORDER_TOTAL_SCRATCH,
                    "Expr ordering equality reservation outside combined scratch profile");
            ExprEquality comparison=new ExprEquality(false); comparison.work=work;
            try { return comparison.applyRoot(kind,left,right); }
            finally { work=comparison.work; }
        }
        int number(Object left,Object right) {
            BigInteger a=pureExprNat(left),b=pureExprNat(right);
            charge(1L+(a.bitLength()+63L)/64+(b.bitLength()+63L)/64); return a.compareTo(b);
        }
        int codePoint(String s,int at) {
            char c=s.charAt(at);
            if(Character.isHighSurrogate(c)) {
                require(at+1<s.length()&&Character.isLowSurrogate(s.charAt(at+1)),"Expr ordering String has unpaired surrogate");
                return Character.toCodePoint(c,s.charAt(at+1));
            }
            require(!Character.isLowSurrogate(c),"Expr ordering String has unpaired surrogate"); return c;
        }
        int string(Object left,Object right) {
            require(left instanceof String&&right instanceof String,"Expr ordering requires String carriers");
            String a=(String)left,b=(String)right; charge((long)a.length()+b.length());
            // Valid Unicode scalar order equals unsigned lexicographic UTF8.
            // Validate before comparing; avoid byte-array allocation entirely.
            for(int i=0;i<a.length();) { int cp=codePoint(a,i); i+=Character.charCount(cp); }
            for(int i=0;i<b.length();) { int cp=codePoint(b,i); i+=Character.charCount(cp); }
            int i=0,j=0;
            while(i<a.length()&&j<b.length()) {
                charge(1); int x=codePoint(a,i),y=codePoint(b,j); if(x!=y) return Integer.compare(x,y);
                i+=Character.charCount(x); j+=Character.charCount(y);
            }
            return i==a.length()?(j==b.length()?0:-1):1;
        }
        int name(Object left,Object right) {
            ArrayList<Node> a=new ArrayList<>(),b=new ArrayList<>();
            Object x=left,y=right;
            while(true) {
                charge(1); Node n=nameNode(x); if(n==null) break;
                scratch(a.size()+b.size()+1); a.add(n); x=n.fields[0];
            }
            while(true) {
                charge(1); Node n=nameNode(y); if(n==null) break;
                scratch(a.size()+b.size()+1); b.add(n); y=n.fields[0];
            }
            int i=a.size()-1,j=b.size()-1;
            while(i>=0&&j>=0) {
                charge(1); Node an=a.get(i--),bn=b.get(j--);
                if(an.tag!=bn.tag) return an.tag==2?-1:1; // numeric BEFORE string
                int cmp=an.tag==2?number(an.fields[1],bn.fields[1]):string(an.fields[1],bn.fields[1]);
                if(cmp!=0) return cmp;
            }
            return Integer.compare(a.size(),b.size());
        }
        Node ctor(Object value,int fields,int bytes) {
            Node n=constructorNode(value);
            require(n.closure==null&&n.rc>=0&&n.fields.length==fields&&n.scalars.length==bytes,"Expr ordering constructor storage differs"); return n;
        }
        Node list(Object value) {
            if(ERASED.equals(value)) return null;
            Node n=ctor(value,2,0); require(n.tag==1,"Expr ordering List.cons tag differs"); return n;
        }
        Node taggedValue(Object value,boolean literal) {
            Node n=constructorNode(value); int max=literal?1:5;
            require(n.closure==null&&n.rc>=0&&n.tag>=0&&n.tag<=max,"Expr ordering value kind differs");
            boolean bool=!literal&&n.tag==1;
            require(n.fields.length==(bool?0:1)&&(bool?(n.scalars.length==1||n.scalars.length==8):n.scalars.length==0),
                    "Expr ordering value storage differs"); return n;
        }
        void choose(OrderFrame parent,int kind,Object left,Object right) { parent.stage=1; push(kind,left,right); }
        void validate(OrderFrame frame) {
            Object x=frame.key.left,y=frame.key.right;
            switch(frame.key.kind) {
                case LT_EXPR: frame.left=exprNode(x); frame.right=exprNode(y); break;
                case LT_LEVEL: frame.left=levelNode(x); frame.right=levelNode(y); break;
                case LT_LEVELS: case LT_MDATA: frame.left=list(x); frame.right=list(y); break;
                case LT_PAIR:
                    frame.left=ctor(x,2,0); frame.right=ctor(y,2,0);
                    require(frame.left.tag==0&&frame.right.tag==0,"Expr ordering metadata pair tag differs"); break;
                case LT_VALUE: case LT_LITERAL: frame.left=taggedValue(x,frame.key.kind==LT_LITERAL); frame.right=taggedValue(y,frame.key.kind==LT_LITERAL); break;
                case LT_NAME: nameNode(x); nameNode(y); break;
                case LT_NAT: pureExprNat(x); pureExprNat(y); break;
                case LT_STRING: require(x instanceof String&&y instanceof String,"Expr ordering String carrier differs"); break;
                default: throw error("Unknown Expr ordering domain");
            }
        }
        boolean takeChild(OrderFrame frame) { require(frame.hasChild,"Expr ordering child receiver empty"); frame.hasChild=false; return frame.child; }
        void step(OrderFrame frame) {
            int kind=frame.key.kind; Object x=frame.key.left,y=frame.key.right;
            if(frame.stage==1) { done(frame,takeChild(frame)); return; }
            if(frame.stage==2) {
                if(takeChild(frame)) { done(frame,true); return; }
                frame.stage=3; push(LT_PAIR,frame.right.fields[0],frame.left.fields[0]); return;
            }
            if(frame.stage==3) {
                if(takeChild(frame)) { done(frame,false); return; }
                choose(frame,LT_MDATA,frame.left.fields[1],frame.right.fields[1]); return;
            }
            require(frame.stage==0,"Expr ordering continuation differs"); validate(frame);
            if(x==y) { done(frame,false); return; }
            Byte state=states.get(frame.key);
            if(state!=null) { require(state!=0,"Expr ordering cycle outside bounded profile"); done(frame,state==2); return; }
            scratch(1); states.put(frame.key,(byte)0);
            Node a=frame.left,b=frame.right;
            if(kind==LT_NAT) { done(frame,number(x,y)<0); return; }
            if(kind==LT_STRING) { done(frame,string(x,y)<0); return; }
            if(kind==LT_NAME) { done(frame,name(x,y)<0); return; }
            if(kind==LT_LEVELS||kind==LT_MDATA) {
                if(a==null||b==null) { done(frame,a==null&&b!=null); return; }
                if(kind==LT_MDATA) { frame.stage=2; push(LT_PAIR,a.fields[0],b.fields[0]); return; }
                if(equal(EQ_LEVEL,a.fields[0],b.fields[0])) choose(frame,LT_LEVELS,a.fields[1],b.fields[1]);
                else choose(frame,LT_LEVEL,a.fields[0],b.fields[0]);
                return;
            }
            if(kind==LT_PAIR) {
                if(equal(EQ_NAME,a.fields[0],b.fields[0])) choose(frame,LT_VALUE,a.fields[1],b.fields[1]);
                else choose(frame,LT_NAME,a.fields[0],b.fields[0]);
                return;
            }
            if(kind==LT_VALUE||kind==LT_LITERAL) {
                if(a.tag!=b.tag) { done(frame,a.tag<b.tag); return; }
                if(kind==LT_LITERAL) { choose(frame,a.tag==0?LT_NAT:LT_STRING,a.fields[0],b.fields[0]); return; }
                switch(a.tag) {
                    case 0: choose(frame,LT_STRING,a.fields[0],b.fields[0]); return;
                    case 1:
                        int av=a.scalars[0]&255,bv=b.scalars[0]&255;
                        require(av<=1&&bv<=1,"Expr ordering Bool byte differs"); done(frame,av<bv); return;
                    case 2: choose(frame,LT_NAME,a.fields[0],b.fields[0]); return;
                    case 3: choose(frame,LT_NAT,a.fields[0],b.fields[0]); return;
                    case 4: case 5: done(frame,false); return; // pinned TODO: Int/Syntax incomparable
                    default: throw error("Expr ordering DataValue kind differs");
                }
            }
            if(kind==LT_LEVEL) {
                long ad=a==null?0:readScalar(a,0,U64)>>>40,bd=b==null?0:readScalar(b,0,U64)>>>40;
                if(ad!=bd) { done(frame,ad<bd); return; }
                int at=a==null?0:a.tag,bt=b==null?0:b.tag;
                if(at!=bt) { done(frame,at<bt); return; }
                long ah=a==null?2221:readScalar(a,0,U64)&0xffffffffL,bh=b==null?2221:readScalar(b,0,U64)&0xffffffffL;
                if(ah!=bh) { done(frame,ah<bh); return; }
                if(equal(EQ_LEVEL,x,y)) { done(frame,false); return; }
                require(a!=null&&b!=null,"Unequal zero Levels outside ordering profile");
                if(a.tag>=4) choose(frame,LT_NAME,a.fields[0],b.fields[0]);
                else if(a.tag==1||!equal(EQ_LEVEL,a.fields[0],b.fields[0])) choose(frame,LT_LEVEL,a.fields[0],b.fields[0]);
                else choose(frame,LT_LEVEL,a.fields[1],b.fields[1]);
                return;
            }
            require(kind==LT_EXPR,"Expr ordering dispatch domain differs");
            if(a.tag!=b.tag) { done(frame,a.tag<b.tag); return; }
            long ah=exprCachedData(a)&0xffffffffL,bh=exprCachedData(b)&0xffffffffL;
            if(ah!=bh) { done(frame,ah<bh); return; }
            if(equal(EQ_EXPR,x,y)) { done(frame,false); return; }
            switch(a.tag) {
                case 0: choose(frame,LT_NAT,a.fields[0],b.fields[0]); return;
                case 1: case 2: choose(frame,LT_NAME,a.fields[0],b.fields[0]); return;
                case 3: choose(frame,LT_LEVEL,a.fields[0],b.fields[0]); return;
                case 4:
                    if(equal(EQ_NAME,a.fields[0],b.fields[0])) choose(frame,LT_LEVELS,a.fields[1],b.fields[1]);
                    else choose(frame,LT_NAME,a.fields[0],b.fields[0]); return;
                case 5:
                    if(equal(EQ_EXPR,a.fields[0],b.fields[0])) choose(frame,LT_EXPR,a.fields[1],b.fields[1]);
                    else choose(frame,LT_EXPR,a.fields[0],b.fields[0]); return;
                case 6: case 7:
                    if(equal(EQ_EXPR,a.fields[1],b.fields[1])) choose(frame,LT_EXPR,a.fields[2],b.fields[2]);
                    else choose(frame,LT_EXPR,a.fields[1],b.fields[1]); return;
                case 8:
                    int av=a.scalars[8]&255,bv=b.scalars[8]&255;
                    require(av<=1&&bv<=1,"Expr ordering let nondep byte differs");
                    if(av!=bv) { done(frame,av<bv); return; }
                    if(!equal(EQ_EXPR,a.fields[1],b.fields[1])) choose(frame,LT_EXPR,a.fields[1],b.fields[1]);
                    else if(!equal(EQ_EXPR,a.fields[2],b.fields[2])) choose(frame,LT_EXPR,a.fields[2],b.fields[2]);
                    else choose(frame,LT_EXPR,a.fields[3],b.fields[3]); return;
                case 9: choose(frame,LT_LITERAL,a.fields[0],b.fields[0]); return;
                case 10:
                    if(equal(EQ_EXPR,a.fields[1],b.fields[1])) choose(frame,LT_MDATA,a.fields[0],b.fields[0]);
                    else choose(frame,LT_EXPR,a.fields[1],b.fields[1]); return;
                case 11:
                    if(!equal(EQ_EXPR,a.fields[2],b.fields[2])) choose(frame,LT_EXPR,a.fields[2],b.fields[2]);
                    else if(!equal(EQ_NAME,a.fields[0],b.fields[0])) choose(frame,LT_NAME,a.fields[0],b.fields[0]);
                    else choose(frame,LT_NAT,a.fields[1],b.fields[1]); return;
                default: throw error("Expr ordering Expr kind differs");
            }
        }
        boolean apply(Object left,Object right) {
            push(LT_EXPR,left,right);
            while(!stack.isEmpty()) {
                charge(1); OrderFrame frame=stack.peek();
                if(!frame.completed) { step(frame); continue; }
                if(!states.containsKey(frame.key)) scratch(1);
                states.put(frame.key,frame.result?(byte)2:(byte)1); stack.pop();
                if(stack.isEmpty()) return frame.result;
                OrderFrame parent=stack.peek(); require(!parent.hasChild,"Expr ordering child receiver occupied");
                parent.child=frame.result; parent.hasChild=true;
            }
            throw error("Expr ordering root result missing");
        }
    }
    private static boolean borrowedExprOrder(int op) { return op==EXPR_QUICK_LT; }

    private static boolean borrowedExprEquality(int intrinsic) { return intrinsic==EXPR_EQV||intrinsic==EXPR_EQUAL; }

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
        if(f.intrinsic==STR_TO_UTF8) { stringToUtf8(a); return; }
        if(f.intrinsic==STR_FROM_UTF8) { stringFromUtf8(a,b); return; }
        if(f.intrinsic==STR_VALIDATE_UTF8) {
            Node bytes=byteArray(a); scalarResult=validUtf8(bytes.scalars,((ByteArrayState)kindMetadata(bytes)).size)?1:0; return;
        }
        if(f.intrinsic>=STR_SUBSTRING_EQ&&f.intrinsic<=STR_PUSHN) { stringCompletionIntrinsic(f,a,b,c); return; }
        if(f.intrinsic>=INT_OF_NAT&&f.intrinsic<=INT_LE) { intIntrinsic(f,a,b); return; }
        if(f.intrinsic==NAME_EQ) { scalarResult=nameEquals(a,b)?1:0; return; }
        if(buildIdentityPrimitive(f.intrinsic)) {
            requireBuildIdentity(); requireBuildUnit(a);
            result=f.intrinsic==BUILD_GITHASH?buildIdentity.githash():buildIdentity.target(); return;
        }
        if((f.intrinsic>=BYTE_MK&&f.intrinsic<=BYTE_PUSH)||f.intrinsic==BYTE_EMPTY) { byteArrayIntrinsic(f,a,b,c); return; }
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
            case GET_STDOUT: if(stdioContext!=null) require(ERASED.equals(a),"Stdio world placeholder required"); result=stdout(); break;
            case GET_STDIN: case GET_STDERR:
                require(ERASED.equals(a),"Stdio world placeholder required");
                result=standardStream(f.intrinsic==GET_STDIN?0:2,false,null); break;
            case SET_STDIN: case SET_STDOUT: case SET_STDERR:
                require(ERASED.equals(b),"Stdio world placeholder required");
                result=standardStream(f.intrinsic==SET_STDIN?0:f.intrinsic==SET_STDOUT?1:2,true,a); break;
            case STREAM_FLUSH: result=ioUnit(); break;
            case STREAM_PUT: utf8(a); output.append(text(a)); result=ioUnit(); break;
            case STDERR_PUT: utf8(a); stderrOutput.append(text(a)); result=ioUnit(); break;
            case STREAM_TTY: result=ERASED; break;
            case STREAM_READ: case STREAM_WRITE: case STREAM_LINE:
                throw new UnsupportedOperationException("Captured-output stream operation not implemented: "+f.label);
            case PANIC: throw new UnsupportedOperationException("panicCore default-return policy outside captured-output profile: "+text(c));
            default: throw error("Invalid runtime intrinsic");
        }
    }
    /** Pinned lean_expr_data reads the first scalar word after the object
     * fields. Validate only the known storage family; do not infer AST flags. */
    private long exprCachedData(Object value) { return readScalar(exprNode(value),0,U64); }
    private Node exprNode(Object value) {
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
        return node;
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
            case U16_EQ: case U16_NAT:
            case LAYOUT_FIELDS: case LAYOUT_SCALARS: case LAYOUT_TAG: case LAYOUT_USIZE: case U32_LT: case U64_TO_NAT:
            case STR_HASH: case U64_MIX: case U64_NAT: case U64_SHR: case U64_XOR: case U64_USIZE:
            case U64_LT: case U64_EQ: case U64_OWNED_NAT: case U64_TO_U32:
            case BOOL_U64: case U64_ADD: case U64_SUB: case U64_MUL: case U64_DIV: case U64_MOD:
            case U64_AND: case U64_OR: case U64_NOT: case U64_NEG: case U64_LOG2: case U64_SHL: case U64_LE:
            case U8_TO_U64: case U32_TO_U64: case USIZE_TO_U64: case U8_TO_U32: case U64_TO_U8:
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
            case U16_NAT: case U32_NAT: result=a; break;
            case U16_EQ: case U32_EQ: scalarResult=((Long)a).longValue()==((Long)b).longValue()?1:0; break;
            case U32_LT: scalarResult=(Long)a<(Long)b?1:0; break;
            case U64_TO_NAT: result=externalScalar((Long)a,U64); break;
            case LAYOUT_FIELDS: case LAYOUT_SCALARS: case LAYOUT_TAG: case LAYOUT_USIZE:
                requireLayoutUnit(a);
                result=Long.valueOf(f.intrinsic==LAYOUT_FIELDS?256:f.intrinsic==LAYOUT_SCALARS?1024:f.intrinsic==LAYOUT_TAG?243:8); break;
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
            case U8_TO_U64: case U32_TO_U64: case USIZE_TO_U64: case U8_TO_U32: scalarResult=(Long)a; break;
            case U64_TO_U8: scalarResult=(Long)a&255L; break;
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
    /** Pinned 64-bit Lean target layout, not Java object dimensions. */
    private static boolean layoutPrimitive(int op) { return op>=LAYOUT_FIELDS&&op<=LAYOUT_USIZE; }
    private static void requireLayoutUnit(Object value) {
        require(value instanceof Long&&((Long)value).longValue()==0,"Layout query requires canonical Unit zero");
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
        if(findPrimitive(function.intrinsic)) require(explicit&&taskRuntime!=null,"Expr.find requires the active explicit runtime");
        if(function.intrinsic==LEVEL_INSTANTIATE) levelInstantiationProfile(function);
        if(function.intrinsic==EXPR_INSTANTIATE_MVARS) exprInstantiationProfile(function);
        if(function.intrinsic==SHARECOMMON_QUICK) shareCommonProfile();
        if(function.intrinsic==EXPR_REPLACE) exprTransformsProfile(function);
        if(abstractPrimitive(function.intrinsic)||pureExprTransform(function.intrinsic)) exprTransformsProfile(function);
        if(buildIdentityPrimitive(function.intrinsic)) requireBuildIdentity();
        if(taskPrimitive(function.intrinsic)) require(taskRuntime!=null,"Logical synchronous task runtime is inactive");
        if(function.params.length==0&&constantReady[function.id]) return function;
        Header header=function.header;
        if(header!=null&&header.initialized()) throw error("Initialized global is unavailable: "+function.label);
        if(function.hostExtern!=null||function.intrinsic!=0) return function;
        if(header!=null&&header.kind.equals("extern")) throw error("Extern implementation unavailable: "+function.label);
        if(allowCodeRequest&&header!=null&&program.preparedBodies[function.id]==null) return function;
        PreparedBody prepared=preparedBody(function); pointerHashEntry(function,prepared,program); return function;
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
            if(layoutPrimitive(f.intrinsic)) requireLayoutUnit(closure.fields.length==0?args[0]:closure.fields[0]);
            if(f.intrinsic==BOOL_U64) requireBoolScalar(closure.fields.length==0?args[0]:closure.fields[0]);
        }
        Object[] combined=new Object[closure.fields.length+args.length];
        System.arraycopy(closure.fields,0,combined,0,closure.fields.length);
        System.arraycopy(args,0,combined,closure.fields.length,args.length);
        if(combined.length>=f.params.length&&called.intrinsic==MARK_PERSISTENT)
            validatePersistentArguments(combined[0],combined[1],combined[2]);
        if(combined.length>=f.params.length&&called.intrinsic==VOID_MK) validateVoidArguments(combined[0],combined[1]);
        if(combined.length>=f.params.length&&called.intrinsic==ARRAY_CHECKED_SET)
            validateCheckedArraySet(combined.length==f.params.length?combined:Arrays.copyOf(combined,f.params.length));
        if(combined.length>=f.params.length&&called.intrinsic==STR_TO_UTF8) utf8Extent(combined[0]);
        if(combined.length>=f.params.length&&called.intrinsic==STR_FROM_UTF8) validateFromUtf8(combined[0],combined[1]);
        // A shared closure keeps ownership of its captured arguments.
        if(!exclusive(closure)) for(Object a:closure.fields) inc(a,1);
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
    private void expression(Expr e,int type,int dest,PreparedBody prepared,Function caller) {
        switch(e.op) {
            case CTOR: {
                if(e.size==0&&e.scalarBytes==0) objects[dest]=Long.valueOf(e.tag);
                else { Node n=new Node(e.tag,e.size,e.scalarBytes); for(int i=0;i<e.size;i++) n.fields[i]=obj(e.args[i]); objects[dest]=n; allocations++; } break;
            }
            case PROJ: objects[dest]=constructorNode(obj(e.a)).fields[e.b]; break;
            case SPROJ: { Node n=constructorNode(obj(e.a)); numbers[dest]=readScalar(n,rawOffset(n,e.size,e.b),type); break; }
            case UPROJ: { Node n=constructorNode(obj(e.a)); numbers[dest]=readScalar(n,rawOffset(n,e.b,0),USIZE); break; }
            case FAP:
                if(e.target.intrinsic==POINTER_IDENTITY) pointerIdentity(e.target,e.args,prepared,e,caller);
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
                    expression(e,b.type,bp+b.a,prepared,f); b=b.next; break;
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
        require(!function.borrowedUtf8,"Borrowed UTF8 conversion cannot be admitted as a first-class closure");
        require(function.intrinsic!=STR_VALIDATE_UTF8&&function.intrinsic!=BYTE_COPY_SLICE,
                "Borrowed UTF8/buffer primitive requires an owned guest wrapper");
        require(!borrowedTaskPrimitive(function.intrinsic),"Borrowed task primitive requires owned guest wrapper");
        require(function.intrinsic!=NAME_EQ,"Borrowed Name equality cannot be admitted as a first-class closure");
        require(function.intrinsic!=EXPR_CACHE,"Borrowed Expr data requires an owned guest wrapper"); require(!borrowedExprEquality(function.intrinsic),"Borrowed Expr equality requires an owned guest wrapper"); require(function.intrinsic!=LEVEL_EQUAL,"Borrowed Level equality requires an owned guest wrapper"); require(!borrowedExprLooseQuery(function.intrinsic),"Borrowed Expr loose search requires an owned guest wrapper"); require(!borrowedExprOrder(function.intrinsic),"Borrowed Expr quick ordering requires an owned guest wrapper"); require(!findPrimitive(function.intrinsic),"Borrowed Expr.find requires an owned guest wrapper"); require(function.intrinsic!=SHARECOMMON_QUICK,"Borrowed ShareCommon requires an owned guest wrapper"); require(function.intrinsic!=EXPR_REPLACE,"Borrowed Expr.replace requires an owned guest wrapper"); require(!abstractPrimitive(function.intrinsic),"Borrowed Expr abstraction requires an owned guest wrapper"); require(!pureExprTransform(function.intrinsic),"Borrowed Expr instantiation/lift requires an owned guest wrapper");
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
    private static void enqueuePositiveGraphValues(Object[] values,ImportNode[] nodes,Map<Long,Integer> positions,
                                                   boolean[] marked,ArrayDeque<Integer> pending) {
        for(Object value:values) if(value instanceof GraphRef) {
            int position=graphPosition((GraphRef)value,positions);
            if(nodes[position].sourceRC>0&&!marked[position]) { marked[position]=true; pending.addLast(position); }
        }
    }
    private static void requirePersistentGraphValues(Object[] values,ImportNode[] nodes,Map<Long,Integer> positions,String message) {
        for(Object value:values) if(value instanceof GraphRef)
            require(nodes[graphPosition((GraphRef)value,positions)].sourceRC==0,message);
    }
    /** Derive the exact target MT region without allocating or mutating runtime Nodes. */
    private static boolean[] preparedRefPayloadSharing(PreparedGraph graph,Map<Long,Integer> positions) {
        if(graph.profile!=GraphImportProfile.PERSISTENT_REF_PAYLOAD_MT) return null;
        boolean[] marked=new boolean[graph.nodes.length]; ArrayDeque<Integer> pending=new ArrayDeque<>();
        requirePersistentGraphValues(graph.globalValues,graph.nodes,positions,"MT payload profile forbids positive cache roots");
        requirePersistentGraphValues(graph.ownedRoots,graph.nodes,positions,"MT payload profile forbids positive output roots");
        for(ImportNode node:graph.nodes) {
            if(node.kind==ImportNode.REF) {
                require(node.sourceRC==0,"MT payload profile requires every Ref to be persistent");
                enqueuePositiveGraphValues(node.fields,graph.nodes,positions,marked,pending);
            } else if(node.sourceRC==0) {
                requirePersistentGraphValues(node.fields,graph.nodes,positions,
                        "Only persistent Ref slots may enter the positive MT payload graph");
            }
        }
        while(!pending.isEmpty())
            enqueuePositiveGraphValues(graph.nodes[pending.removeFirst()].fields,graph.nodes,positions,marked,pending);
        for(int i=0;i<graph.nodes.length;i++)
            require(marked[i]==(graph.nodes[i].sourceRC>0),"Source-positive object is outside persistent Ref payload closure");
        return marked;
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
        // One ordinary companion plus one complete module aggregate. Neither
        // admission can be repeated/split to evade its selected profile bound.
        boolean moduleData=graph.profile==GraphImportProfile.MODULE_DATA_RC0;
        require(moduleData?!moduleGraphInstalled:!graphInstalled,
                "Selected prepared graph slot has already been installed in this engine");
        Map<Long,Integer> positions=new HashMap<>();
        for(int i=0;i<graph.nodes.length;i++) {
            ImportNode node=graph.nodes[i];
            require(node.sourceRC>=0&&(graph.profile!=GraphImportProfile.DEFAULT_RC0||node.sourceRC==0),
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
                require(!target.borrowedUtf8,"Borrowed UTF8 conversion requires owned closure wrapper");
                require(target.intrinsic!=NAME_EQ,"Borrowed Name equality requires an owned guest wrapper");
                require(target.intrinsic!=EXPR_CACHE,"Borrowed Expr data requires an owned guest wrapper"); require(!borrowedExprEquality(target.intrinsic),"Borrowed Expr equality requires an owned guest wrapper"); require(target.intrinsic!=LEVEL_EQUAL,"Borrowed Level equality requires an owned guest wrapper"); require(!borrowedExprLooseQuery(target.intrinsic),"Borrowed Expr loose search requires an owned guest wrapper"); require(!borrowedExprOrder(target.intrinsic),"Borrowed Expr quick ordering requires an owned guest wrapper"); require(!findPrimitive(target.intrinsic),"Borrowed Expr.find requires an owned guest wrapper"); require(target.intrinsic!=SHARECOMMON_QUICK,"Borrowed ShareCommon requires an owned guest wrapper"); require(target.intrinsic!=EXPR_REPLACE,"Borrowed Expr.replace requires an owned guest wrapper"); require(!abstractPrimitive(target.intrinsic),"Borrowed Expr abstraction requires an owned guest wrapper"); require(!pureExprTransform(target.intrinsic),"Borrowed Expr instantiation/lift requires an owned guest wrapper");
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
        if(graph.profile!=GraphImportProfile.DEFAULT_RC0&&graph.profile!=GraphImportProfile.MODULE_DATA_RC0) {
            for(ImportNode node:graph.nodes) countGraphOwners(node.fields,graph.nodes,positions,owners);
            countGraphOwners(graph.globalValues,graph.nodes,positions,owners);
            countGraphOwners(graph.ownedRoots,graph.nodes,positions,owners);
            for(int i=0;i<owners.length;i++) if(graph.nodes[i].sourceRC>0)
                require(owners[i]>0,"Source-positive object has no selected owning occurrence");
        }
        boolean[] mtPayloads=preparedRefPayloadSharing(graph,positions);
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
        if(mtPayloads!=null) {
            // Only private, newly wired shells are touched; all owner counts,
            // cache state and counters remain unpublished if staging fails.
            for(int i=0;i<shells.length;i++) if(graph.nodes[i].kind==ImportNode.REF)
                markLogicalMT(shells[i].fields[0]);
            for(int i=0;i<shells.length;i++)
                require(logicalMT(shells[i])==mtPayloads[i],"Prepared Ref payload sharing derivation mismatch");
        }
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
        if(moduleData) { moduleGraphInstalled=true; preparedModuleSource=source; }
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
                require(!target.borrowedUtf8,"Borrowed UTF8 conversion requires owned closure wrapper");
        require(target.intrinsic!=NAME_EQ,"Borrowed Name equality requires an owned guest wrapper");
        require(target.intrinsic!=EXPR_CACHE,"Borrowed Expr data requires an owned guest wrapper"); require(!borrowedExprEquality(target.intrinsic),"Borrowed Expr equality requires an owned guest wrapper"); require(target.intrinsic!=LEVEL_EQUAL,"Borrowed Level equality requires an owned guest wrapper"); require(!borrowedExprLooseQuery(target.intrinsic),"Borrowed Expr loose search requires an owned guest wrapper"); require(!borrowedExprOrder(target.intrinsic),"Borrowed Expr quick ordering requires an owned guest wrapper"); require(!findPrimitive(target.intrinsic),"Borrowed Expr.find requires an owned guest wrapper"); require(target.intrinsic!=SHARECOMMON_QUICK,"Borrowed ShareCommon requires an owned guest wrapper"); require(target.intrinsic!=EXPR_REPLACE,"Borrowed Expr.replace requires an owned guest wrapper"); require(!abstractPrimitive(target.intrinsic),"Borrowed Expr abstraction requires an owned guest wrapper"); require(!pureExprTransform(target.intrinsic),"Borrowed Expr instantiation/lift requires an owned guest wrapper");
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
        codeRequest=new CodeRequest(runtimeIdentity,activation); pc=next; phase=CODE_CALL; actionHelperEntry(function,args); applicationEntry(kind); hostGuestEntry(function,args);
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
        pointerHashEntry(function,prepared,descendant);
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
        if(layoutPrimitive(function.intrinsic)) requireLayoutUnit(args[0]);
        if(function.intrinsic==BOOL_U64) requireBoolScalar(args[0]);
        if(function.intrinsic==STR_TO_UTF8) utf8Extent(args[0]);
        if(function.intrinsic==STR_FROM_UTF8) validateFromUtf8(args[0],args[1]);
        if(function.intrinsic==TASK_MAP&&taskRuntime==null) validateTaskMap(args);
        if(taskRuntime!=null&&function.intrinsic==TASK_PURE) {
            require(ERASED.equals(args[0]),"Task.pure erased placeholder required"); validateHostObject(args[1]);
        }
        if(taskRuntime!=null&&function.intrinsic==TASK_GET) {
            require(ERASED.equals(args[0]),"Task.get erased placeholder required"); readyTaskNode(args[1]);
        }
        if(function.intrinsic==MARK_PERSISTENT) validatePersistentArguments(args[0],args[1],args[2]);
        if(function.intrinsic>=SET_STDIN&&function.intrinsic<=SET_STDERR) {
            require(ERASED.equals(args[1]),"Stdio world placeholder required"); ownedStdioReplacement(args[0]);
        }
        if(function.intrinsic==ARRAY_CHECKED_SET) validateCheckedArraySet(args);
        else if(function.intrinsic==VOID_MK) validateVoidArguments(args[0],args[1]);
        else if(actionPrimitive(function)) validateNative(function,args);
        for(int i=0;i<args.length;i++) {
            if(function.paramTypes[i]!=OBJ) { if(saved) readSavedScalar(args[i],function.paramTypes[i]); else inputScalar(args[i],function.paramTypes[i]); }
            else if(args[i] instanceof Double||args[i] instanceof F64Bits||args[i] instanceof Float||args[i] instanceof F32Bits) throw error("Float scalar is not an OBJ value");
            else if(args[i] instanceof Node) {
                Node value=node(args[i]);
                if(value.closure!=null) acceptsClosure(value);
            }
        }
    }

    /** Bind an owned external invocation, without executing its body. */
    public void start(int function,Object[] args) {
        explicitOnly();
        require(pendingInitializerGlobal==null,"Complete the pending initializer before another start");
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
        bp=sp; sp=newSp; jbp=jsp; jsp=newJsp; active=f; activePrepared=prepared; pc=prepared.body; actionHelperEntry(f,args); applicationEntry(kind); hostGuestEntry(f,args);
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
            if(layoutPrimitive(f.intrinsic)) requireLayoutUnit(closure.fields.length==0?args[0]:closure.fields[0]);
            if(f.intrinsic==BOOL_U64) requireBoolScalar(closure.fields.length==0?args[0]:closure.fields[0]);
        }
        Object[] combined=new Object[closure.fields.length+args.length];
        System.arraycopy(closure.fields,0,combined,0,closure.fields.length);
        System.arraycopy(args,0,combined,closure.fields.length,args.length);
        if(combined.length>=f.params.length&&(taskRuntime!=null||called.intrinsic==VOID_MK||called.intrinsic==MARK_PERSISTENT||called.intrinsic==ARRAY_CHECKED_SET)) {
            Object[] actual=combined.length==f.params.length?combined:Arrays.copyOf(combined,f.params.length);
            if(called.intrinsic==MARK_PERSISTENT) validatePersistentArguments(actual[0],actual[1],actual[2]);
            else if(called.intrinsic==ARRAY_CHECKED_SET) validateCheckedArraySet(actual);
            else if(called.intrinsic==VOID_MK) validateVoidArguments(actual[0],actual[1]);
            else if(actionPrimitive(f)) validateNative(f,actual);
            else if(f.intrinsic==TASK_GET||f.intrinsic==TASK_PURE) validateEntryArguments(f,actual,true);
        }
        if(combined.length>=f.params.length&&called.intrinsic==STR_TO_UTF8) utf8Extent(combined[0]);
        if(combined.length>=f.params.length&&called.intrinsic==STR_FROM_UTF8) validateFromUtf8(combined[0],combined[1]);
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
                                if(f.intrinsic==POINTER_IDENTITY) pointerIdentity(f,e.args,activePrepared,e,active);
                                else intrinsicSlots(f,e.args);
                                if(b.type==OBJ) objects[dest]=result; else numbers[dest]=scalarResult;
                                b=b.next;
                            } else { enterExplicit(f,e.args,null,b.next,dest,e.args.length==0?CACHE:ASSIGN,null); b=pc; }
                        } else if(e.op==AP) {
                            Object value=obj(e.a); Object[] args=new Object[e.args.length];
                            for(int i=0;i<args.length;i++) args[i]=obj(e.args[i]);
                            applyExplicit(value,args,b.next,dest);
                            b=pc;
                        } else { expression(e,b.type,dest,activePrepared,active); b=b.next; }
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
        require(pendingInitializerGlobal==null,"Use completeInitializer for the pending initializer result");
        return detachCompletedResult();
    }
    private Object detachCompletedResult() {
        if(phase!=COMPLETE||!pendingOwnedResult) throw new IllegalStateException("No owned result available");
        Object value=releaseRoot?ERASED:entry==null||entry.resultType==OBJ?result:externalScalar(scalarResult,entry.resultType);
        pendingOwnedResult=false; result=null; entry=null; releaseRoot=false; phase=IDLE;
        return value;
    }
    /** Internal borrowed array primitives need an owning wrapper at host entry. */
    private static boolean borrowedTaskPrimitive(int op) {
        return op==PROMISE_RESOLVE||op==PROMISE_RESULT||op==TASK_STATE||op==TASK_CANCEL;
    }
    private static void rootEntry(Function f) {
        require(!f.borrowedUtf8,"Borrowed UTF8 conversion requires owned guest wrapper at external entry");
        require(f.intrinsic!=PROFILE_IT,"Borrowed profiling primitive requires an owned guest wrapper");
        require(!borrowedTaskPrimitive(f.intrinsic),"Borrowed task primitive requires owned guest wrapper");
        if(borrowedStringPositionPrimitive(f.intrinsic))
            throw new UnsupportedOperationException("Borrowed String position primitive requires owned guest wrapper at external entry");
        if(borrowedStringCompletionPrimitive(f.intrinsic))
            throw new UnsupportedOperationException("Borrowed String range primitive requires owned guest wrapper at external entry");
        if(borrowedIntPrimitive(f.intrinsic))
            throw new UnsupportedOperationException("Borrowed Int primitive requires owned guest wrapper at external entry");
        require(f.intrinsic!=NAME_EQ,"Borrowed Name equality requires an owned guest wrapper");
        require(f.intrinsic!=EXPR_CACHE,"Borrowed Expr data requires an owned guest wrapper"); require(!borrowedExprEquality(f.intrinsic),"Borrowed Expr equality requires an owned guest wrapper"); require(f.intrinsic!=LEVEL_EQUAL,"Borrowed Level equality requires an owned guest wrapper"); require(!borrowedExprLooseQuery(f.intrinsic),"Borrowed Expr loose search requires an owned guest wrapper"); require(!borrowedExprOrder(f.intrinsic),"Borrowed Expr quick ordering requires an owned guest wrapper"); require(!findPrimitive(f.intrinsic),"Borrowed Expr.find requires an owned guest wrapper"); require(f.intrinsic!=SHARECOMMON_QUICK,"Borrowed ShareCommon requires an owned guest wrapper"); require(f.intrinsic!=EXPR_REPLACE,"Borrowed Expr.replace requires an owned guest wrapper"); require(!abstractPrimitive(f.intrinsic),"Borrowed Expr abstraction requires an owned guest wrapper"); require(!pureExprTransform(f.intrinsic),"Borrowed Expr instantiation/lift requires an owned guest wrapper");
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
            if(!disposed||stdioRoots()||runtimeAction!=null||hostCompletion!=null||quietCurrent!=null||releasePending!=0)
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
        if(stdioContext!=null) {
            for(int i=0;i<3;i++) { Node old=stdioContext.current[i]; stdioContext.current[i]=null; if(old!=null) releaseQuiet(old,1); }
        }
        for(int i=0;i<3;i++) { Node old=stdioDefault(i); clearStdioDefault(i); if(old!=null) releaseQuiet(old,1); }
        utf8Key=null; utf8Bytes=null;
        for(int i=0;i<constants.length;i++) if(constantReady[i]&&program.functions[i].resultType==OBJ) releaseQuiet(constants[i],1);
        Arrays.fill(constants,null); Arrays.fill(objects,null); result=null; taskRecords.clear();
    }
}
