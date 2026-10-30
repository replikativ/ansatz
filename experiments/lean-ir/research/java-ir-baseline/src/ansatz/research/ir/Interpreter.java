/*
 * Experimental JVM port of Lean's lambda-RC interpreter, pinned to
 * 819816b2e0a3bf405af45ae5c7af2491d8f5bee6:src/library/ir_interpreter.cpp.
 * Upstream: Copyright (c) 2019 Microsoft Corporation. Apache-2.0.
 * Author of upstream interpreter: Sebastian Ullrich.
 *
 * Bounded object/uint8/uint32/usize profile (64-bit little-endian), not a public API.
 * Research eager graph forks and typed host requests, not a persistent branch
 * store, native ABI invocation, general host IO, or arbitrary World conversion.
 */
package ansatz.research.ir;

import java.math.BigInteger;
import java.lang.ref.WeakReference;
import java.nio.charset.StandardCharsets;
import java.util.*;

public final class Interpreter implements AutoCloseable {
    private static final int OBJ=0, U8=1, U32=2, USIZE=3;
    private static final int VDECL=0,JDECL=1,SET=2,SSET=3,INC=4,DEC=5,DEL=6,CASE=7,RET=8,JMP=9,UNREACHABLE=10,SETTAG=11,USET=12;
    private static final int CTOR=0,PROJ=1,SPROJ=2,FAP=3,PAP=4,AP=5,BOX=6,UNBOX=7,LIT=8,SHARED=9,UPROJ=10;
    private static final int ADD=1,SUB=2,MOD=3,EQ=4,LT=5,MUL=6,DIV=7,POW=8;
    private static final int USIZE_NAT=9,USIZE_REPR=10,U32_NAT=11,U32_EQ=12,U32_LE=13,PLATFORM_BITS=14;
    private static final int STR_PUSH=15,STR_LIST=16,STR_GET=17,STR_NEXT=18,STR_APPEND=19,STR_SIZE=20,
                             ARRAY_MK=21,ARRAY_SIZE=22,ARRAY_GET=23,GET_STDOUT=24,PANIC=25;
    private static final int STREAM_FLUSH=100,STREAM_READ=101,STREAM_WRITE=102,STREAM_LINE=103,STREAM_PUT=104,STREAM_TTY=105;
    private static final BigInteger SMALL_MAX=BigInteger.valueOf(Long.MAX_VALUE);
    private static final Object ERASED=Long.valueOf(0);

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
        public Object[] arguments() { return call.arguments.clone(); }
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

    public static final class Node {
        public int tag, rc=1;
        public final Object[] fields;
        public final byte[] scalars;
        private Function closure;
        private Generation image;
        private boolean dead;
        private boolean array;
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
        if(raw.equals("uint16")||raw.equals("uint64")||raw.equals("float")||raw.equals("float32")) return -1;
        return type(raw);
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
    /** Published only after parsing and validation; inherited slots share identity. */
    private static final class PreparedBody {
        final Body body;
        final int width, joinWidth;
        PreparedBody(Body body,int width,int joinWidth) {
            this.body=body; this.width=width; this.joinWidth=joinWidth;
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
    /** Identity-only lineage: no function/map/Program references. Binary lifting
     * bounds ancestry checks without retaining every old full image table. */
    private static final class Generation {
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
    public static final class Program {
        final Function[] functions;
        final PreparedBody[] preparedBodies;
        final Map<String,Function> labels;
        final Map<Object,Function> typedNames;
        final Map<String,List<HostExtern>> hostRegistry;
        final Generation generation;
        private Program(Function[] functions,PreparedBody[] preparedBodies,Map<String,Function> labels,Map<Object,Function> typedNames,
                        Map<String,List<HostExtern>> hostRegistry,Generation generation) {
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
        public int functionCount() { return functions.length; }
        /** Append-only link against this actual base, preserving every old
         * function identity/ID. Metadata-only input with no new ABI is a no-op. */
        public static Program extend(Program base,List<?> rows) { return extend(base,rows,new HostExtern[0]); }
        public static Program extend(Program base,List<?> rows,HostExtern[] additionalExterns) {
            require(base!=null,"Actual base Program required");
            return link(base,rows,additionalExterns);
        }
    }

    private static Map<String,List<HostExtern>> extendedHostRegistry(Program base,HostExtern[] additional) {
        require(additional!=null,"Explicit host extern registry required");
        Map<String,List<HostExtern>> registry=new HashMap<>();
        for(Map.Entry<String,List<HostExtern>> entry:base.hostRegistry.entrySet())
            registry.put(entry.getKey(),new ArrayList<>(entry.getValue()));
        for(HostExtern descriptor:additional.clone()) {
            require(descriptor!=null,"Null host extern descriptor");
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
                           new Generation(base.generation));
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
        return new Program(staged.functions,slots,staged.labels,staged.typedNames,staged.hostRegistry,new Generation(staged.generation));
    }

    private Program program;
    private Object[] objects=new Object[1024];
    private long[] numbers=new long[1024];
    private Body[] joins=new Body[256];
    private int bp,sp,jbp,jsp;
    private Object result;
    private long scalarResult;
    private Object[] constants;
    private boolean[] constantReady;
    private boolean closed;
    private boolean untrackedFailure;
    private final Object runtimeIdentity=new Object();
    private Node stdoutRoot;
    private final StringBuilder output=new StringBuilder();
    private WeakReference<String> utf8Key;
    private byte[] utf8Bytes;
    private Object[] releaseWork=new Object[32];
    private long callsLeft;
    private final boolean explicit;
    private static final int IDLE=0, RUNNING=1, COMPLETE=2, FAILED=3, HOST_CALL=4;
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
    private HostRequest hostRequest,failedHostRequest;
    private HostCall hostCompletion;
    private Throwable hostFailure;
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
    public Interpreter(Program program,boolean explicit) {
        this.program=program;
        this.explicit=explicit;
        if(explicit) continuations=new Continuation[32];
        constants=new Object[program.functions.length];
        constantReady=new boolean[constants.length];
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
        if(closed||advancing||phase==FAILED||untrackedFailure||(!explicit&&sp!=0))
            throw new IllegalStateException("Fork requires an open idle or paused instruction boundary");
        if(externalRoots==null) throw error("Explicit fork roots required");
        // phase RUNNING between advance calls is the explicit driver's paused
        // instruction boundary. No Java call frame is captured in that state.
        Interpreter child=new Interpreter(program,explicit);
        ForkCopy copy=new ForkCopy(child);
        copy.bind(constants,child.constants);
        child.objects=(Object[])copy.value(objects);
        child.numbers=numbers.clone(); child.joins=joins.clone();
        System.arraycopy(constantReady,0,child.constantReady,0,constantReady.length);
        child.bp=bp; child.sp=sp; child.jbp=jbp; child.jsp=jsp;
        child.result=copy.value(result); child.scalarResult=scalarResult;
        child.stdoutRoot=(Node)copy.value(stdoutRoot);
        child.output.append(output);
        String key=utf8Key==null?null:utf8Key.get();
        child.utf8Key=key==null?null:new WeakReference<>(key);
        child.utf8Bytes=utf8Bytes==null?null:utf8Bytes.clone();
        child.releaseWork=(Object[])copy.value(releaseWork);
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
        child.hostRequest=(HostRequest)copy.value(hostRequest);
        child.hostCompletion=(HostCall)copy.value(hostCompletion);
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
            if(source==null||source instanceof Long||source instanceof BigInteger||source instanceof String) return source;
            Object prior=copies.get(source); if(prior!=null) return prior;
            if(source instanceof Node) {
                Node old=(Node)source;
                Object[] fields=(Object[])copies.get(old.fields);
                boolean fresh=fields==null;
                if(fresh) fields=new Object[old.fields.length];
                Node out=new Node(old.tag,fields,old.scalars.length);
                copies.put(source,out); out.rc=old.rc; out.dead=old.dead; out.array=old.array; out.image=old.image;
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
            if(source instanceof HostRequest) {
                HostRequest old=(HostRequest)source;
                if(old.owner!=runtimeIdentity) throw error("Host request belongs to another interpreter");
                HostRequest out=new HostRequest(child.runtimeIdentity,(HostCall)value(old.call));
                copies.put(source,out); return out;
            }
            if(source instanceof HostCall) {
                HostCall old=(HostCall)source,out=new HostCall(); copies.put(source,out);
                out.function=(Function)value(old.function); out.arguments=(Object[])value(old.arguments);
                out.surplus=(Object[])value(old.surplus); out.next=old.next;
                out.dest=old.dest; out.kind=old.kind; out.borrowedCursor=old.borrowedCursor;
                out.facade=old.facade; out.replyClaimed=old.replyClaimed;
                out.adapterReleaseStarted=old.adapterReleaseStarted; out.resultOwned=old.resultOwned;
                out.resultTransferStarted=old.resultTransferStarted;
                out.completionResult=value(old.completionResult); out.completionScalar=old.completionScalar;
                return out;
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
                Object[] task=pending.removeFirst(),source=(Object[])task[0],target=(Object[])task[1];
                for(int i=0;i<source.length;i++) target[i]=value(source[i]);
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
                           Collections.unmodifiableMap(hostRegistry),new Generation(base==null?null:base.generation));
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
                    case SPROJ: require((b.type==U8||b.type==U32)&&lane(env,e.a)==OBJ,"Scalar projection lane mismatch"); break;
                    case UPROJ: require(b.type==USIZE&&lane(env,e.a)==OBJ,"USize projection lane mismatch"); break;
                    case FAP: requireExecutableAbi(e.target); checkArgs(env,e.args,e.target.paramTypes); require(b.type==e.target.resultType,"Call result lane mismatch"); break;
                    case PAP: requireExecutableAbi(e.target); require(b.type==OBJ&&e.args.length<e.target.params.length,"Invalid partial application"); require(e.target.intrinsic!=ARRAY_SIZE&&e.target.intrinsic!=ARRAY_GET,"Borrowed array primitive requires owned closure wrapper"); for(int i=0;i<e.target.paramTypes.length;i++) require(e.target.paramTypes[i]==OBJ,"Unboxed partial target unsupported; boxed wrapper required"); for(int a:e.args) require(lane(env,a)==OBJ,"Partial argument must be boxed"); break;
                    case AP: require(b.type==OBJ&&lane(env,e.a)==OBJ&&e.args.length>0,"Unsupported closure application"); for(int a:e.args) require(lane(env,a)==OBJ,"Closure argument must be boxed"); break;
                    case BOX: require(b.type==OBJ&&e.b!=OBJ&&lane(env,e.a)==e.b,"Box lane mismatch"); break;
                    case UNBOX: require(b.type!=OBJ&&lane(env,e.a)==OBJ,"Unbox lane mismatch"); break;
                    case SHARED: require(b.type==U8&&lane(env,e.a)==OBJ,"Sharing-test lane mismatch"); break;
                    case LIT: if(b.type!=OBJ) e.literal=Long.valueOf(inputScalar(e.literal,b.type)); break;
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
            case CASE: require(lane(env,b.a)==b.type,"Case lane mismatch"); for(Body alt:b.alternatives) validateBody(alt,f,env,joins,seen); break;
            case RET: require(lane(env,b.a)==f.resultType,"Return lane mismatch"); break;
            case SET: require(lane(env,b.a)==OBJ&&lane(env,b.args[0])==OBJ,"Field store lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
            case SSET: require(lane(env,b.a)==OBJ&&(b.type==U8||b.type==U32)&&lane(env,b.args[0])==b.type,"Scalar store lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
            case USET: require(lane(env,b.a)==OBJ&&lane(env,b.args[0])==USIZE,"USize store lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
            case INC: case DEC: case DEL: case SETTAG: require(lane(env,b.a)==OBJ,"Object instruction lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
            case UNREACHABLE: break;
            default: throw error("Invalid body opcode");
        }
    }
    private void ensure(int slots,int joinSlots) {
        if(slots>objects.length) { int n=Math.max(slots,objects.length*2); objects=Arrays.copyOf(objects,n); numbers=Arrays.copyOf(numbers,n); }
        if(joinSlots>joins.length) joins=Arrays.copyOf(joins,Math.max(joinSlots,joins.length*2));
    }
    private Object obj(int variable) { return variable==0?ERASED:objects[bp+variable]; }
    private Node node(Object o) {
        if(!(o instanceof Node)||((Node)o).dead) throw error("Expected live object"); return (Node)o;
    }
    public void inc(Object o,int n) {
        if(n<0) throw error("Negative reference increment");
        if(o instanceof Node) { Node v=node(o); if(v.rc!=0) { v.rc=Math.addExact(v.rc,n); retains+=n; } }
    }
    public void dec(Object o,int n) {
        if(n<0) throw error("Negative reference decrement");
        if(!(o instanceof Node)) return;
        Node v=node(o);
        if(v.rc==0) return;
        if(n>v.rc) throw error("Reference count underflow");
        v.rc-=n; releases+=n;
        if(v.rc==0) destroy(v);
    }
    private void destroy(Node current) {
        int pending=0;
        try {
            while(true) {
                current.dead=true;
                // Transfer child-edge owners to an explicit private work
                // stack. No native finalizers run in this profile.
                for(int i=current.fields.length-1;i>=0;i--) {
                    Object child=current.fields[i]; current.fields[i]=null;
                    if(child instanceof Node) {
                        if(pending==releaseWork.length) releaseWork=Arrays.copyOf(releaseWork,Math.multiplyExact(pending,2));
                        releaseWork[pending++]=child;
                    }
                }
                Node next=null;
                while(pending!=0) {
                    Node child=node(releaseWork[--pending]); releaseWork[pending]=null;
                    if(child.rc==0) continue;
                    child.rc--; releases++;
                    if(child.rc==0) { next=child; break; }
                }
                if(next==null) return;
                current=next;
            }
        } finally { Arrays.fill(releaseWork,0,pending,null); }
    }
    private void unique(Node n) { if(n.rc!=1) throw error("Expected exclusive object"); }
    private static BigInteger nat(Object x) {
        if(x instanceof Long&&((Long)x)>=0) return BigInteger.valueOf((Long)x);
        if(x instanceof BigInteger&&((BigInteger)x).signum()>=0) return (BigInteger)x;
        throw error("Invalid Nat");
    }
    private static Object normalize(BigInteger n) { if(n.signum()<0) throw error("Negative Nat"); return n.compareTo(SMALL_MAX)<=0?Long.valueOf(n.longValue()):n; }
    private static long inputScalar(Object value,int type) {
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
        if(type==USIZE&&value<0) return BigInteger.valueOf(value&Long.MAX_VALUE).setBit(63);
        return Long.valueOf(value);
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
        if(type==USIZE) {
            Node n=new Node(0,0,8); writeScalar(n,0,USIZE,value); allocations++; return n;
        }
        return Long.valueOf(type==U8?value&255:value&0xffffffffL);
    }
    private long unboxScalar(Object value,int type) {
        if(type==USIZE) {
            Node n=node(value);
            require(n.tag==0&&n.fields.length==0&&n.scalars.length==8&&n.closure==null,"Expected boxed USize");
            return readScalar(n,0,USIZE);
        }
        return inputScalar(value,type);
    }
    private long caseTag(Body b) {
        if(b.type==OBJ) {
            Object value=obj(b.a);
            if(value instanceof Node) return node(value).tag;
            if(value instanceof Long) return ((Long)value)&0xffffffffL;
            throw error("Object case outside baseline value profile");
        }
        long value=numbers[bp+b.a];
        // The pinned C++ driver truncates USize tags to unsigned32, unlike the
        // LLVM backend. Reject that ambiguous raw-IR domain in this profile.
        if(b.type==USIZE&&(value<0||value>0xffffffffL)) throw error("Wide USize case outside execution profile");
        return value;
    }
    private void intrinsicSlots(Function f,int[] slots) {
        if(f.intrinsic<=POW) { intrinsic(f,obj(slots[0]),obj(slots[1])); return; }
        Object a=f.paramTypes[0]==OBJ?obj(slots[0]):Long.valueOf(numbers[bp+slots[0]]);
        Object b=slots.length<2?ERASED:f.paramTypes[1]==OBJ?obj(slots[1]):Long.valueOf(numbers[bp+slots[1]]);
        if(f.intrinsic>=STR_PUSH) {
            Object c=slots.length<3?ERASED:f.paramTypes[2]==OBJ?obj(slots[2]):Long.valueOf(numbers[bp+slots[2]]);
            runtimeIntrinsic(f,a,b,c);
        } else scalarIntrinsic(f,a,b);
    }
    private void intrinsicExternal(Function f,Object[] args) {
        if(f.intrinsic<=POW) { intrinsic(f,args[0],args[1]); return; }
        Object a=f.paramTypes[0]==OBJ?args[0]:Long.valueOf(inputScalar(args[0],f.paramTypes[0]));
        Object b=args.length<2?ERASED:f.paramTypes[1]==OBJ?args[1]:Long.valueOf(inputScalar(args[1],f.paramTypes[1]));
        if(f.intrinsic>=STR_PUSH) {
            Object c=args.length<3?ERASED:f.paramTypes[2]==OBJ?args[2]:Long.valueOf(inputScalar(args[2],f.paramTypes[2]));
            runtimeIntrinsic(f,a,b,c);
        } else scalarIntrinsic(f,a,b);
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
            require(!n.array&&n.closure==null&&n.tag==1&&n.fields.length==2&&n.scalars.length==0,"Expected List cons");
            if(values.size()>=1_000_000) throw error("List traversal limit");
            values.add(n.fields[0]); cursor=n.fields[1];
        }
        return values.toArray();
    }
    private Node array(Object value) { Node n=node(value); require(n.array,"Expected Array"); return n; }
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
    private void runtimeIntrinsic(Function f,Object a,Object b,Object c) {
        switch(f.intrinsic) {
            case STR_PUSH: utf8(a); result=text(a)+new String(Character.toChars(codePoint(b))); break;
            case STR_APPEND: utf8(a); utf8(b); result=text(a)+text(b); break;
            case STR_SIZE: result=Long.valueOf(utf8(a).length); break;
            case STR_GET: case STR_NEXT: {
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
                String s=builder.toString(); dec(a,1); result=s; break;
            }
            case ARRAY_MK: {
                Object[] elements=listElements(b); Node n=new Node(246,elements.length,0); n.array=true;
                for(int i=0;i<elements.length;i++) { inc(elements[i],1); n.fields[i]=elements[i]; }
                allocations++; dec(b,1); result=n; break;
            }
            case ARRAY_SIZE: result=Long.valueOf(array(b).fields.length); break;
            case ARRAY_GET: {
                Node n=array(b); BigInteger index=nat(c);
                require(index.compareTo(BigInteger.valueOf(n.fields.length))<0,"Array index outside bounds");
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
    private void scalarIntrinsic(Function f,Object a,Object b) {
        switch(f.intrinsic) {
            case USIZE_NAT: scalarResult=nat(a).longValue(); break;
            case USIZE_REPR: result=Long.toUnsignedString((Long)a); break;
            case U32_NAT: result=a; break;
            case U32_EQ: scalarResult=((Long)a).longValue()==((Long)b).longValue()?1:0; break;
            case U32_LE: scalarResult=(Long)a<=(Long)b?1:0; break;
            case PLATFORM_BITS: require(a instanceof Long&&(Long)a==0,"Expected Unit for platform bits"); result=Long.valueOf(64); break;
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
                default: throw error("Invalid intrinsic");
            }
        }
    }
    private void load(Function f) {
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
    private void preflightCallable(Function function) {
        requireExecutableAbi(function);
        if(function.params.length==0&&constantReady[function.id]) return;
        Header header=function.header;
        if(header!=null&&header.initialized()) throw error("Initialized global is unavailable: "+function.label);
        if(function.hostExtern!=null||function.intrinsic!=0) return;
        if(header!=null&&header.kind.equals("extern")) throw error("Extern implementation unavailable: "+function.label);
        preparedBody(function);
    }
    private PreparedBody preparedBody(Function function) {
        require(function.id>=0&&function.id<program.functions.length
                &&program.functions[function.id]==function,"Function outside current Program");
        PreparedBody prepared=program.preparedBodies[function.id];
        if(prepared==null) throw error("Unprepared executable body: "+function.label);
        return prepared;
    }
    private void call(Function f,int[] args) {
        preflightCallable(f);
        if(f.hostExtern!=null) throw new UnsupportedOperationException("Host extern requires explicit driver: "+f.hostExtern.symbol);
        if(args.length!=f.params.length) throw error("Arity mismatch: "+f.label);
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
        preflightCallable(f);
        if(f.hostExtern!=null) throw new UnsupportedOperationException("Host extern requires explicit driver: "+f.hostExtern.symbol);
        if(args.length!=f.params.length) throw error("Arity mismatch: "+f.label);
        if(f.intrinsic!=0) { intrinsicExternal(f,args); return; }
        PreparedBody prepared=preparedBody(f);
        int oldBp=bp,oldSp=sp,oldJbp=jbp,oldJsp=jsp;
        ensure(sp+prepared.width,jsp+prepared.joinWidth);
        for(int i=0;i<args.length;i++) if(f.paramTypes[i]!=OBJ) inputScalar(args[i],f.paramTypes[i]);
        for(int i=0;i<args.length;i++) { int dest=sp+f.params[i]; if(f.paramTypes[i]==OBJ) objects[dest]=args[i]; else numbers[dest]=inputScalar(args[i],f.paramTypes[i]); }
        bp=oldSp;sp+=prepared.width;jbp=oldJsp;jsp+=prepared.joinWidth;
        try { eval(f,prepared); }
        finally { Arrays.fill(objects,oldSp,sp,null); Arrays.fill(joins,oldJsp,jsp,null); bp=oldBp;sp=oldSp;jbp=oldJbp;jsp=oldJsp; }
    }
    private Object apply(Object value,Object[] args) {
        Node closure=node(value); if(closure.closure==null) throw error("Expected closure");
        acceptsClosure(closure);
        Function f=closure.closure;
        requireExecutableAbi(f);
        if(closure.fields.length+args.length>=f.params.length) preflightCallable(f);
        Object[] combined=new Object[closure.fields.length+args.length];
        System.arraycopy(closure.fields,0,combined,0,closure.fields.length);
        // A shared closure keeps ownership of its captured arguments.
        if(closure.rc!=1) for(Object a:closure.fields) inc(a,1);
        System.arraycopy(args,0,combined,closure.fields.length,args.length);
        if(closure.rc==1) { closure.dead=true; Arrays.fill(closure.fields,null); shellDeletes++; }
        else dec(closure,1);
        if(combined.length<f.params.length) return closure(f,combined);
        Object[] actual=combined.length==f.params.length?combined:Arrays.copyOf(combined,f.params.length);
        enter(f,actual); Object answer=f.resultType==OBJ?result:boxScalar(scalarResult,f.resultType);
        return combined.length==f.params.length?answer:apply(answer,Arrays.copyOfRange(combined,f.params.length,combined.length));
    }
    private Node closure(Function f,Object[] captured) {
        Node n=new Node(245,captured.length,0); n.closure=f; n.image=program.generation; System.arraycopy(captured,0,n.fields,0,captured.length); allocations++; return n;
    }
    private void expression(Expr e,int type,int dest) {
        switch(e.op) {
            case CTOR: {
                if(e.size==0&&e.scalarBytes==0) objects[dest]=Long.valueOf(e.tag);
                else { Node n=new Node(e.tag,e.size,e.scalarBytes); for(int i=0;i<e.size;i++) n.fields[i]=obj(e.args[i]); objects[dest]=n; allocations++; } break;
            }
            case PROJ: objects[dest]=node(obj(e.a)).fields[e.b]; break;
            case SPROJ: { Node n=node(obj(e.a)); numbers[dest]=readScalar(n,rawOffset(n,e.size,e.b),type); break; }
            case UPROJ: { Node n=node(obj(e.a)); numbers[dest]=readScalar(n,rawOffset(n,e.b,0),USIZE); break; }
            case FAP:
                if(e.args.length==0) load(e.target); else call(e.target,e.args);
                if(type==OBJ) objects[dest]=result; else numbers[dest]=scalarResult; break;
            case PAP: { Object[] captured=new Object[e.args.length]; for(int i=0;i<captured.length;i++) captured[i]=obj(e.args[i]); objects[dest]=closure(e.target,captured); break; }
            case AP: { Object value=obj(e.a); Object[] args=new Object[e.args.length]; for(int i=0;i<args.length;i++) args[i]=obj(e.args[i]); objects[dest]=apply(value,args); break; }
            case BOX: objects[dest]=boxScalar(numbers[bp+e.a],e.b); break;
            case UNBOX: numbers[dest]=unboxScalar(obj(e.a),type); break;
            case LIT: if(type==OBJ) objects[dest]=e.literal; else numbers[dest]=(Long)e.literal; break;
            case SHARED: numbers[dest]=node(obj(e.a)).rc==1?0:1; break;
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
                    if(e.op==FAP&&e.target==f&&b.next.op==RET&&b.next.a==b.a) {
                        int scratch=sp; ensure(sp+e.args.length,jsp);
                        for(int i=0;i<e.args.length;i++) { objects[scratch+i]=obj(e.args[i]); numbers[scratch+i]=numbers[bp+e.args[i]]; }
                        for(int i=0;i<e.args.length;i++) { objects[bp+f.params[i]]=objects[scratch+i]; numbers[bp+f.params[i]]=numbers[scratch+i]; objects[scratch+i]=null; }
                        tick(); b=prepared.body; break;
                    }
                    expression(e,b.type,bp+b.a); b=b.next; break;
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
                case DEC: dec(obj(b.a),b.b); b=b.next; break;
                case DEL: { Node n=node(obj(b.a)); unique(n); n.dead=true; Arrays.fill(n.fields,null); shellDeletes++; b=b.next; break; }
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
        if(!program.generation.accepts(closure.image)) throw error("Closure belongs to another code image");
        if(function.privateOwner!=null) {
            if(function.privateOwner!=runtimeIdentity) throw error("Host closure belongs to another interpreter");
        } else require(function.id>=0&&function.id<program.functions.length&&program.functions[function.id]==function,
                       "Closure function identity differs from current code generation");
    }
    private void generationBoundary(String operation) {
        if(closed||advancing||untrackedFailure||(phase!=IDLE&&phase!=HOST_CALL)||(!explicit&&sp!=0))
            throw new IllegalStateException(operation+" requires an open idle or host-call boundary");
    }
    /** Install only an actual descendant. Preserve all initialized cache owners
     * and readiness; new slots start unready. Both arrays are allocated before
     * the thread-confined publication, with no guest calls or initializer replay. */
    public void installProgram(Program descendant) {
        generationBoundary("Program installation");
        require(descendant!=null,"Actual descendant Program required");
        if(descendant==program) return;
        require(descendant.generation.accepts(program.generation),"Program is not a descendant of the installed generation");
        require(descendant.functions.length>=program.functions.length,"Descendant function table shrank");
        for(int i=0;i<program.functions.length;i++) {
            require(descendant.functions[i]==program.functions[i],"Descendant replaced an inherited function");
            require(program.preparedBodies[i]==null||descendant.preparedBodies[i]==program.preparedBodies[i],
                    "Descendant replaced an inherited prepared body");
        }
        Object[] nextConstants=Arrays.copyOf(constants,descendant.functions.length);
        boolean[] nextReady=Arrays.copyOf(constantReady,descendant.functions.length);
        constants=nextConstants; constantReady=nextReady; program=descendant;
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
        require(target.intrinsic!=ARRAY_SIZE&&target.intrinsic!=ARRAY_GET,
                "Borrowed array primitive requires owned closure wrapper");
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
            else call.arguments[i]=externalScalar(inputScalar(call.arguments[i],f.paramTypes[i]),f.paramTypes[i]);
        }
        hostRequest=new HostRequest(runtimeIdentity,call); pc=next; phase=HOST_CALL;
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
        IdentityHashMap<Node,Integer> owners=new IdentityHashMap<>();
        if(call.facade) for(int i=call.borrowedCursor;i<call.arguments.length;i++)
            if(call.function.hostExtern.borrowed[i]&&call.arguments[i] instanceof Node) {
                Node value=node(call.arguments[i]); owners.put(value,owners.getOrDefault(value,0)+1);
            }
        if(call.function.resultType==OBJ&&reply instanceof Node) {
            Node value=node(reply); owners.put(value,owners.getOrDefault(value,0)+1);
        }
        for(Map.Entry<Node,Integer> credit:owners.entrySet())
            require(credit.getKey().rc==0||credit.getKey().rc>=credit.getValue(),
                    "Insufficient host reply or borrowed-facade owner credits");
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
        call.replyClaimed=true; call.completionResult=reply; call.completionScalar=scalar;
        call.resultOwned=call.function.resultType==OBJ;
        hostRequest=null; hostCompletion=call; advancing=true;
        try {
            if(call.facade) while(call.borrowedCursor<call.arguments.length) {
                int index=call.borrowedCursor;
                if(call.function.hostExtern.borrowed[index]) {
                    call.adapterReleaseStarted=true;
                    dec(call.arguments[index],1);
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
            hostCompletion=null;
        } catch(Throwable failure) { markHostFailure(request,failure); throw failure; }
        finally { advancing=false; }
    }
    /** Terminal external failure preserves all outstanding argument/facade
     * obligations and frames. No host effect, argument release, or replay occurs. */
    public void failHost(HostRequest request,Throwable cause) {
        requireHostRequest(request);
        if(cause==null) throw error("Host failure cause required");
        request.call.replyClaimed=true;
        markHostFailure(request,cause);
    }

    private void explicitOnly() {
        if(!explicit) throw new IllegalStateException("Explicit mode required");
        if(closed) throw new IllegalStateException("Interpreter closed");
    }
    public String phase() { return new String[]{"idle","running","complete","failed","host-call"}[phase]; }
    public int continuationDepth() { return continuationDepth; }
    public long instructionCount() { return instructions; }
    public String activeFunction() { return active==null?null:active.label; }

    /** Both drivers reject invalid input closures before publishing frames,
     * taking owned arguments, or running any guest operation. */
    private void validateEntryArguments(Function function,Object[] args) {
        if(args==null||args.length!=function.params.length) throw error("Arity mismatch: "+function.label);
        for(int i=0;i<args.length;i++) {
            if(function.paramTypes[i]!=OBJ) inputScalar(args[i],function.paramTypes[i]);
            else if(args[i] instanceof Node) {
                Node value=node(args[i]);
                if(value.closure!=null) acceptsClosure(value);
            }
        }
    }

    /** Bind an owned external invocation, without executing its body. */
    public void start(int function,Object[] args) {
        explicitOnly();
        if(advancing||phase!=IDLE) throw new IllegalStateException("Take the result or finish the current execution before start");
        Function f=program.functions[function];
        rootEntry(f);
        preflightCallable(f);
        validateEntryArguments(f,args);
        if(f.params.length==0&&constantReady[f.id]) {
            if(f.resultType==OBJ) { result=constants[f.id]; inc(result,1); }
            else scalarResult=(Long)constants[f.id];
            callsLeft=10_000_000; instructions=0;
            entry=f; phase=COMPLETE; pendingOwnedResult=true; return;
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
        preflightCallable(f);
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
                if(f.paramTypes[i]==OBJ) objects[target]=args[i]; else numbers[target]=inputScalar(args[i],f.paramTypes[i]);
            }
        }
        k.caller=active; k.callerPrepared=activePrepared; k.next=next; k.bp=bp; k.sp=sp; k.jbp=jbp; k.jsp=jsp;
        k.dest=dest; k.kind=kind; k.surplus=surplus;
        continuationDepth++;
        bp=sp; sp=newSp; jbp=jsp; jsp=newJsp; active=f; activePrepared=prepared; pc=prepared.body;
        tick();
    }

    /** Prepare and consume one AP exactly once; no guest execution here. */
    private boolean prepareExplicitApply(Object value,Object[] args) {
        Node closure=node(value); if(closure.closure==null) throw error("Expected closure");
        acceptsClosure(closure);
        Function f=closure.closure;
        requireExecutableAbi(f);
        if(closure.fields.length+args.length>=f.params.length) preflightCallable(f);
        Object[] combined=new Object[closure.fields.length+args.length];
        System.arraycopy(closure.fields,0,combined,0,closure.fields.length);
        if(closure.rc!=1) for(Object a:closure.fields) inc(a,1);
        System.arraycopy(args,0,combined,closure.fields.length,args.length);
        if(closure.rc==1) { closure.dead=true; Arrays.fill(closure.fields,null); shellDeletes++; }
        else dec(closure,1);
        if(combined.length<f.params.length) { result=closure(f,combined); return false; }
        applicationTarget=f;
        applicationArgs=combined.length==f.params.length?combined:Arrays.copyOf(combined,f.params.length);
        applicationSurplus=combined.length==f.params.length?null:Arrays.copyOfRange(combined,f.params.length,combined.length);
        return true;
    }
    private void applyExplicit(Object value,Object[] args,Body next,int dest) {
        while(true) {
            if(!prepareExplicitApply(value,args)) { objects[dest]=result; pc=next; return; }
            Function f=applicationTarget; Object[] actual=applicationArgs,rest=applicationSurplus;
            applicationTarget=null; applicationArgs=null; applicationSurplus=null;
            if(f.hostExtern!=null) { suspendHost(f,actual,next,dest,APPLY,rest,true); return; }
            if(f.intrinsic==0) { enterExplicit(f,null,actual,next,dest,APPLY,rest); return; }
            intrinsicExternal(f,actual);
            value=f.resultType==OBJ?result:boxScalar(scalarResult,f.resultType);
            if(rest==null) { objects[dest]=value; pc=next; return; }
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
     * Self-tail elimination consumes its VDECL and has no deferred RET frame. */
    public boolean advance(long budget) {
        explicitOnly();
        if(budget<0) throw error("Negative instruction budget");
        if(advancing) throw new IllegalStateException("Reentrant advance");
        if(phase==COMPLETE) return true;
        if(phase==HOST_CALL) return false;
        if(phase!=RUNNING) throw new IllegalStateException("No resumable execution: "+phase());
        advancing=true;
        try { runExplicitLoop(budget); return phase==COMPLETE; }
        catch(Throwable failure) { phase=FAILED; throw failure; }
        finally { advancing=false; }
    }
    private void runExplicitLoop(long budget) {
        Body b=pc;
            while(phase==RUNNING&&budget-->0) {
                // Keep the dispatch cursor local. Publish the attempted body
                // for failures and let control-transfer helpers publish callees.
                pc=b; instructions++;
                switch(b.op) {
                    case VDECL: {
                        Expr e=b.expr; int dest=bp+b.a;
                        if(e.op==FAP) {
                            Function f=e.target;
                            if(f!=active) preflightCallable(f);
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
                                for(int i=0;i<args.length;i++) args[i]=f.paramTypes[i]==OBJ?obj(e.args[i]):externalScalar(numbers[bp+e.args[i]],f.paramTypes[i]);
                                suspendHost(f,args,b.next,dest,ASSIGN,null,false); b=pc;
                            } else if(f.intrinsic!=0) {
                                intrinsicSlots(f,e.args);
                                if(b.type==OBJ) objects[dest]=result; else numbers[dest]=scalarResult;
                                b=b.next;
                            } else { enterExplicit(f,e.args,null,b.next,dest,e.args.length==0?CACHE:ASSIGN,null); b=pc; }
                        } else if(e.op==AP) {
                            Object value=obj(e.a); Object[] args=new Object[e.args.length];
                            for(int i=0;i<args.length;i++) args[i]=obj(e.args[i]);
                            applyExplicit(value,args,b.next,dest);
                            b=pc;
                        } else { expression(e,b.type,dest); b=b.next; }
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
                    case DEC: dec(obj(b.a),b.b); b=b.next; break;
                    case DEL: { Node n=node(obj(b.a)); unique(n); n.dead=true; Arrays.fill(n.fields,null); shellDeletes++; b=b.next; break; }
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
        Object value=entry.resultType==OBJ?result:externalScalar(scalarResult,entry.resultType);
        pendingOwnedResult=false; result=null; entry=null; phase=IDLE;
        return value;
    }
    /** Internal borrowed array primitives need an owning wrapper at host entry. */
    private static void rootEntry(Function f) {
        if(f.intrinsic==ARRAY_SIZE||f.intrinsic==ARRAY_GET)
            throw new UnsupportedOperationException("Borrowed array primitive requires owned guest wrapper at external entry");
    }
    /** Internal owned-argument typed entry, not Lean's generic call_boxed ABI. */
    public Object invoke(int function,Object[] args) {
        if(closed) throw error("Interpreter closed");
        if(explicit) {
            start(function,args); advance(Long.MAX_VALUE);
            if(phase==HOST_CALL) throw new IllegalStateException("Invocation suspended for host extern: "+hostRequest.symbol());
            return takeResult();
        }
        if(sp!=0) throw error("Reentrant external invocation unsupported");
        Function f=program.functions[function];
        rootEntry(f);
        if(f.hostExtern!=null) throw new UnsupportedOperationException("Host extern requires explicit driver: "+f.hostExtern.symbol);
        preflightCallable(f);
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
        if(closed) return; closed=true;
        if(explicit&&(phase==RUNNING||phase==FAILED||phase==HOST_CALL)) {
            closed=false;
            throw new IllegalStateException("Active or failed explicit execution requires ownership cleanup before close");
        }
        if(pendingOwnedResult&&entry.resultType==OBJ) dec(result,1);
        pendingOwnedResult=false;
        if(stdoutRoot!=null) { dec(stdoutRoot,1); stdoutRoot=null; }
        utf8Key=null; utf8Bytes=null;
        for(int i=0;i<constants.length;i++) if(constantReady[i]&&program.functions[i].resultType==OBJ) dec(constants[i],1);
        Arrays.fill(constants,null); Arrays.fill(objects,null); result=null;
    }
}
