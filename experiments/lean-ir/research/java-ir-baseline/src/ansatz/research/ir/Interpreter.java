/*
 * Experimental JVM port of Lean's lambda-RC interpreter, pinned to
 * 819816b2e0a3bf405af45ae5c7af2491d8f5bee6:src/library/ir_interpreter.cpp.
 * Upstream: Copyright (c) 2019 Microsoft Corporation. Apache-2.0.
 * Author of upstream interpreter: Sebastian Ullrich.
 *
 * Bounded object/uint8 profile, not a complete Lean runtime or public API.
 * No persistence, native ABI, host effects, or arbitrary World conversion.
 */
package ansatz.research.ir;

import java.math.BigInteger;
import java.util.*;

public final class Interpreter implements AutoCloseable {
    private static final int OBJ=0, U8=1;
    private static final int VDECL=0,JDECL=1,SET=2,SSET=3,INC=4,DEC=5,DEL=6,CASE=7,RET=8,JMP=9,UNREACHABLE=10,SETTAG=11;
    private static final int CTOR=0,PROJ=1,SPROJ=2,FAP=3,PAP=4,AP=5,BOX=6,UNBOX=7,LIT=8,SHARED=9;
    private static final int ADD=1,SUB=2,MOD=3,EQ=4,LT=5;
    private static final BigInteger SMALL_MAX=BigInteger.valueOf(Long.MAX_VALUE);
    private static final Object ERASED=Long.valueOf(0);

    public static final class Node {
        public int tag, rc=1;
        public final Object[] fields;
        public final byte[] scalars;
        private Function closure;
        private Program image;
        private boolean dead;
        Node(int tag, int size, int scalarBytes) {
            this.tag=tag; fields=new Object[size]; scalars=new byte[scalarBytes];
        }
    }
    static final class Function {
        final String label;
        int id, width=1, joinWidth=1, resultType, intrinsic;
        int[] params;
        int[] paramTypes;
        Body body;
        Function(String label) { this.label=label; }
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
    public static final class Program {
        final Function[] functions;
        final Map<String,Function> labels;
        Program(Function[] functions,Map<String,Function> labels) { this.functions=functions; this.labels=labels; }
        public int functionId(String label) {
            Function f=labels.get(label);
            if(f==null) throw error("Unknown function: "+label);
            return f.id;
        }
        public int functionCount() { return functions.length; }
    }

    private final Program program;
    private Object[] objects=new Object[1024];
    private long[] numbers=new long[1024];
    private Body[] joins=new Body[256];
    private int bp,sp,jbp,jsp;
    private Object result;
    private long scalarResult;
    private final Object[] constants;
    private final boolean[] constantReady;
    private boolean closed;
    private long callsLeft;
    private final boolean explicit;
    private static final int IDLE=0, RUNNING=1, COMPLETE=2, FAILED=3;
    private static final int ASSIGN=0, CACHE=1, APPLY=2, ROOT=4;
    private int phase=IDLE, continuationDepth;
    private long instructions;
    private boolean advancing, pendingOwnedResult;
    private Function active, entry;
    private Body pc;
    private Continuation[] continuations;
    private Function applicationTarget;
    private Object[] applicationArgs,applicationSurplus;
    private static final class Continuation {
        Function caller;
        Body next;
        int bp,sp,jbp,jsp,dest,kind;
        Object[] surplus;
        void clear() { caller=null; next=null; surplus=null; }
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

    /** Prepare original exported IR once. All functions must be in the profile. */
    public static Program prepare(List<?> rows) {
        Map<Object,Function> byName=new HashMap<>();
        Map<String,Function> labels=new LinkedHashMap<>();
        List<Map<String,Object>> declarations=new ArrayList<>();
        for(Object row:rows) {
            Map<String,Object> r=map(row);
            if(!"decl".equals(r.get("kind"))) continue;
            Object key=r.get("name"); String label=name(key);
            if(byName.containsKey(key)||labels.containsKey(label)) throw error("Duplicate/ambiguous function name: "+label);
            Function f=new Function(label); f.id=declarations.size();
            byName.put(key,f); labels.put(label,f); declarations.add(r);
        }
        for(Map<String,Object> row:declarations) {
            Function f=byName.get(row.get("name"));
            Map<String,Object> ir=map(row.get("ir")); boolean external=ir.containsKey("extern");
            Map<String,Object> d=map(ir.get(external?"extern":"fdecl"));
            f.params=params(d.get("xs")); f.paramTypes=new int[f.params.length];
            for(int i=0;i<f.params.length;i++) { f.paramTypes[i]=type(map(list(d.get("xs")).get(i)).get("ty")); f.width=Math.max(f.width,f.params[i]+1); }
            f.resultType=type(d.get("type"));
            if(external) {
                List<Object> entries=list(map(d.get("ext")).get("entries"));
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
                String symbol=(String)entry.get("fn");
                switch(symbol) {
                    case "lean_nat_add": f.intrinsic=ADD; break;
                    case "lean_nat_sub": f.intrinsic=SUB; break;
                    case "lean_nat_mod": f.intrinsic=MOD; break;
                    case "lean_nat_dec_eq": f.intrinsic=EQ; break;
                    case "lean_nat_dec_lt": f.intrinsic=LT; break;
                    default: throw error("Unsupported baseline extern: "+symbol);
                }
                if(f.params.length!=2||f.paramTypes[0]!=OBJ||f.paramTypes[1]!=OBJ) throw error("Unsupported intrinsic signature");
                for(Object p:list(d.get("xs"))) if(!Boolean.TRUE.equals(map(p).get("borrow"))) throw error("Nat intrinsic requires borrowed parameters");
                if(f.resultType!=((f.intrinsic==EQ||f.intrinsic==LT)?U8:OBJ)) throw error("Wrong intrinsic result");
            } else f.body=body(d.get("body"),f,byName);
        }
        Function[] prepared=labels.values().toArray(new Function[0]);
        for(Function f:prepared) validate(f);
        return new Program(prepared,Collections.unmodifiableMap(labels));
    }
    private static Function target(Map<Object,Function> functions,Object name) {
        Function f=functions.get(name); if(f==null) throw error("Unresolved function: "+name); return f;
    }
    private static Expr expr(Object input, Function f, Map<Object,Function> functions) {
        Map<String,Object> e=map(input); if(e.size()!=1) throw error("Invalid expression");
        String op=e.keySet().iterator().next(); Map<String,Object> d=map(e.get(op)); Expr out=new Expr();
        switch(op) {
            case "ctor": {
                out.op=CTOR; Map<String,Object> info=map(d.get("i")); out.tag=number(info.get("cidx"));
                out.size=number(info.get("size")); int usize=number(info.get("usize"));
                if(usize!=0) throw error("USize fields outside baseline profile");
                out.scalarBytes=number(info.get("ssize")); out.args=args(d.get("ys"));
                if(out.args.length!=out.size) throw error("Constructor arity mismatch"); break;
            }
            case "proj": out.op=PROJ; out.a=variable(d.get("x")); out.b=number(d.get("i")); break;
            case "sproj": out.op=SPROJ; out.a=variable(d.get("x")); out.b=number(d.get("offset")); out.size=number(d.get("n")); break;
            case "fap": case "pap": out.op=op.equals("fap")?FAP:PAP; out.target=target(functions,d.get("c")); out.args=args(d.get("ys")); break;
            case "ap": out.op=AP; out.a=variable(d.get("x")); out.args=args(d.get("ys")); break;
            case "box": out.op=BOX; out.b=type(d.get("ty")); out.a=variable(d.get("x")); break;
            case "unbox": out.op=UNBOX; out.a=variable(d.get("x")); break;
            case "lit": {
                out.op=LIT; Map<String,Object> lit=map(d.get("v"));
                if(lit.containsKey("num")) { Object n=map(lit.get("num")).get("v"); BigInteger big=new BigInteger(n.toString()); out.literal=normalize(big); }
                else if(lit.containsKey("str")) out.literal=map(lit.get("str")).get("v");
                else throw error("Unsupported literal"); break;
            }
            case "isShared": out.op=SHARED; out.a=variable(d.get("x")); break;
            default: throw error("Unsupported baseline expression: "+op);
        }
        f.width=Math.max(f.width,out.a+1);
        if(out.args!=null) for(int a:out.args) f.width=Math.max(f.width,a+1);
        return out;
    }
    private static Body body(Object input,Function f,Map<Object,Function> functions) {
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
    private static void validate(Function f) {
        Map<Integer,Integer> env=new HashMap<>(); Set<Integer> seen=new HashSet<>();
        for(int i=0;i<f.params.length;i++) { mark(seen,f.params[i]); env.put(f.params[i],f.paramTypes[i]); }
        if(f.intrinsic==0) validateBody(f.body,f,env,new HashMap<>(),seen);
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
                    case SPROJ: require(b.type==U8&&lane(env,e.a)==OBJ,"Scalar projection lane mismatch"); break;
                    case FAP: checkArgs(env,e.args,e.target.paramTypes); require(b.type==e.target.resultType,"Call result lane mismatch"); break;
                    case PAP: require(b.type==OBJ&&e.args.length<e.target.params.length,"Invalid partial application"); for(int i=0;i<e.target.paramTypes.length;i++) require(e.target.paramTypes[i]==OBJ,"Unboxed partial target unsupported; boxed wrapper required"); for(int a:e.args) require(lane(env,a)==OBJ,"Partial argument must be boxed"); break;
                    case AP: require(b.type==OBJ&&lane(env,e.a)==OBJ&&e.args.length>0,"Unsupported closure application"); for(int a:e.args) require(lane(env,a)==OBJ,"Closure argument must be boxed"); break;
                    case BOX: require(b.type==OBJ&&lane(env,e.a)==U8&&e.b==U8,"Box lane mismatch"); break;
                    case UNBOX: require(b.type==U8&&lane(env,e.a)==OBJ,"Unbox lane mismatch"); break;
                    case SHARED: require(b.type==U8&&lane(env,e.a)==OBJ,"Sharing-test lane mismatch"); break;
                    case LIT: if(b.type==U8) require(e.literal instanceof Long&&(Long)e.literal<=255,"Byte literal outside range"); break;
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
            case SSET: require(lane(env,b.a)==OBJ&&lane(env,b.args[0])==U8&&b.type==U8,"Scalar store lane mismatch"); validateBody(b.next,f,env,joins,seen); break;
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
        if(o instanceof Node) { Node v=node(o); if(v.rc!=0) { v.rc=Math.addExact(v.rc,n); retains+=n; } }
    }
    public void dec(Object o,int n) {
        if(o instanceof Node) {
            Node v=node(o); if(v.rc==0) return;
            if(n>v.rc) throw error("Reference count underflow");
            v.rc-=n; releases+=n;
            if(v.rc==0) { v.dead=true; for(int i=0;i<v.fields.length;i++) { Object child=v.fields[i]; v.fields[i]=null; dec(child,1); } }
        }
    }
    private void unique(Node n) { if(n.rc!=1) throw error("Expected exclusive object"); }
    private static BigInteger nat(Object x) {
        if(x instanceof Long&&((Long)x)>=0) return BigInteger.valueOf((Long)x);
        if(x instanceof BigInteger&&((BigInteger)x).signum()>=0) return (BigInteger)x;
        throw error("Invalid Nat");
    }
    private static Object normalize(BigInteger n) { if(n.signum()<0) throw error("Negative Nat"); return n.compareTo(SMALL_MAX)<=0?Long.valueOf(n.longValue()):n; }
    private void intrinsic(Function f,Object a,Object b) {
        if(a instanceof Long && b instanceof Long && (Long)a>=0 && (Long)b>=0) {
            long x=(Long)a,y=(Long)b;
            switch(f.intrinsic) {
                case ADD: result=x<=Long.MAX_VALUE-y?Long.valueOf(x+y):BigInteger.valueOf(x).add(BigInteger.valueOf(y)); break;
                case SUB: result=Long.valueOf(x<y?0:x-y); break;
                case MOD: result=Long.valueOf(y==0?x:x%y); break;
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
    private void call(Function f,int[] args) {
        if(args.length!=f.params.length) throw error("Arity mismatch: "+f.label);
        if(f.intrinsic!=0) { intrinsic(f,obj(args[0]),obj(args[1])); return; }
        int oldBp=bp,oldSp=sp,oldJbp=jbp,oldJsp=jsp;
        ensure(sp+f.width,jsp+f.joinWidth);
        for(int i=0;i<args.length;i++) {
            int source=oldBp+args[i],dest=oldSp+f.params[i];
            if(f.paramTypes[i]==OBJ) objects[dest]=obj(args[i]); else numbers[dest]=numbers[source];
        }
        bp=oldSp; sp+=f.width; jbp=oldJsp; jsp+=f.joinWidth;
        try { eval(f); }
        finally { Arrays.fill(objects,oldSp,sp,null); Arrays.fill(joins,oldJsp,jsp,null); bp=oldBp;sp=oldSp;jbp=oldJbp;jsp=oldJsp; }
    }
    private void enter(Function f,Object[] args) {
        if(args.length!=f.params.length) throw error("Arity mismatch: "+f.label);
        if(f.intrinsic!=0) { intrinsic(f,args[0],args[1]); return; }
        int oldBp=bp,oldSp=sp,oldJbp=jbp,oldJsp=jsp;
        ensure(sp+f.width,jsp+f.joinWidth);
        for(int i=0;i<args.length;i++) if(f.paramTypes[i]==U8) require(number(args[i])<=255,"Byte argument outside range");
        for(int i=0;i<args.length;i++) { int dest=sp+f.params[i]; if(f.paramTypes[i]==OBJ) objects[dest]=args[i]; else numbers[dest]=number(args[i]); }
        bp=oldSp;sp+=f.width;jbp=oldJsp;jsp+=f.joinWidth;
        try { eval(f); }
        finally { Arrays.fill(objects,oldSp,sp,null); Arrays.fill(joins,oldJsp,jsp,null); bp=oldBp;sp=oldSp;jbp=oldJbp;jsp=oldJsp; }
    }
    private Object apply(Object value,Object[] args) {
        Node closure=node(value); if(closure.closure==null) throw error("Expected closure");
        if(closure.image!=program) throw error("Closure belongs to another code image");
        Function f=closure.closure; Object[] combined=new Object[closure.fields.length+args.length];
        System.arraycopy(closure.fields,0,combined,0,closure.fields.length);
        // A shared closure keeps ownership of its captured arguments.
        if(closure.rc!=1) for(Object a:closure.fields) inc(a,1);
        System.arraycopy(args,0,combined,closure.fields.length,args.length);
        if(closure.rc==1) { closure.dead=true; Arrays.fill(closure.fields,null); shellDeletes++; }
        else dec(closure,1);
        if(combined.length<f.params.length) return closure(f,combined);
        Object[] actual=combined.length==f.params.length?combined:Arrays.copyOf(combined,f.params.length);
        enter(f,actual); Object answer=f.resultType==OBJ?result:Long.valueOf(scalarResult);
        return combined.length==f.params.length?answer:apply(answer,Arrays.copyOfRange(combined,f.params.length,combined.length));
    }
    private Node closure(Function f,Object[] captured) {
        Node n=new Node(245,captured.length,0); n.closure=f; n.image=program; System.arraycopy(captured,0,n.fields,0,captured.length); allocations++; return n;
    }
    private void expression(Expr e,int type,int dest) {
        switch(e.op) {
            case CTOR: {
                if(e.size==0&&e.scalarBytes==0) objects[dest]=Long.valueOf(e.tag);
                else { Node n=new Node(e.tag,e.size,e.scalarBytes); for(int i=0;i<e.size;i++) n.fields[i]=obj(e.args[i]); objects[dest]=n; allocations++; } break;
            }
            case PROJ: objects[dest]=node(obj(e.a)).fields[e.b]; break;
            case SPROJ: { if(type!=U8) throw error("Non-byte projection"); Node n=node(obj(e.a)); int offset=Math.addExact(Math.multiplyExact(e.size-n.fields.length,8),e.b); numbers[dest]=Byte.toUnsignedInt(n.scalars[offset]); break; }
            case FAP:
                if(e.args.length==0) load(e.target); else call(e.target,e.args);
                if(type==OBJ) objects[dest]=result; else numbers[dest]=scalarResult; break;
            case PAP: { Object[] captured=new Object[e.args.length]; for(int i=0;i<captured.length;i++) captured[i]=obj(e.args[i]); objects[dest]=closure(e.target,captured); break; }
            case AP: { Object value=obj(e.a); Object[] args=new Object[e.args.length]; for(int i=0;i<args.length;i++) args[i]=obj(e.args[i]); objects[dest]=apply(value,args); break; }
            case BOX: if(e.b!=U8) throw error("Unsupported box"); objects[dest]=Long.valueOf(numbers[bp+e.a]&255); break;
            case UNBOX: if(type!=U8) throw error("Unsupported unbox"); numbers[dest]=((Number)obj(e.a)).longValue()&255; break;
            case LIT: if(type==OBJ) objects[dest]=e.literal; else numbers[dest]=((Number)e.literal).longValue()&255; break;
            case SHARED: numbers[dest]=node(obj(e.a)).rc==1?0:1; break;
            default: throw error("Invalid expression opcode");
        }
    }
    private void tick() { if(--callsLeft<0) throw error("Call/loop budget exhausted"); if((callsLeft&1023)==0&&Thread.currentThread().isInterrupted()) throw error("Interrupted"); }
    private void eval(Function f) {
        tick(); Body b=f.body;
        while(true) {
            switch(b.op) {
                case VDECL: {
                    Expr e=b.expr;
                    if(e.op==FAP&&e.target==f&&b.next.op==RET&&b.next.a==b.a) {
                        int scratch=sp; ensure(sp+e.args.length,jsp);
                        for(int i=0;i<e.args.length;i++) { objects[scratch+i]=obj(e.args[i]); numbers[scratch+i]=numbers[bp+e.args[i]]; }
                        for(int i=0;i<e.args.length;i++) { objects[bp+f.params[i]]=objects[scratch+i]; numbers[bp+f.params[i]]=numbers[scratch+i]; objects[scratch+i]=null; }
                        tick(); b=f.body; break;
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
                case SSET: { Node n=node(obj(b.a)); unique(n); if(b.type!=U8) throw error("Non-byte store"); int offset=Math.addExact(Math.multiplyExact(b.tags[0]-n.fields.length,8),b.b); n.scalars[offset]=(byte)numbers[bp+b.args[0]]; stores++; b=b.next; break; }
                case SETTAG: { Node n=node(obj(b.a)); unique(n); n.tag=b.b; b=b.next; break; }
                case INC: inc(obj(b.a),b.b); b=b.next; break;
                case DEC: dec(obj(b.a),b.b); b=b.next; break;
                case DEL: { Node n=node(obj(b.a)); unique(n); n.dead=true; Arrays.fill(n.fields,null); shellDeletes++; b=b.next; break; }
                case CASE: {
                    Object value=b.type==OBJ?obj(b.a):null;
                    if(b.type==OBJ&&!(value instanceof Node)&&!(value instanceof Long)) throw error("Object case outside baseline value profile");
                    int tag=b.type==U8?(int)numbers[bp+b.a]:value instanceof Node?node(value).tag:((Long)value).intValue();
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

    private void explicitOnly() {
        if(!explicit) throw new IllegalStateException("Explicit mode required");
        if(closed) throw new IllegalStateException("Interpreter closed");
    }
    public String phase() { return new String[]{"idle","running","complete","failed"}[phase]; }
    public int continuationDepth() { return continuationDepth; }
    public long instructionCount() { return instructions; }
    public String activeFunction() { return active==null?null:active.label; }

    /** Bind an owned external invocation, without executing its body. */
    public void start(int function,Object[] args) {
        explicitOnly();
        if(advancing||phase!=IDLE) throw new IllegalStateException("Take the result or finish the current execution before start");
        Function f=program.functions[function];
        if(args.length!=f.params.length) throw error("Arity mismatch: "+f.label);
        // Validate host inputs before publishing state or writing stack slots.
        for(int i=0;i<args.length;i++) {
            if(f.paramTypes[i]==U8) require(number(args[i])<=255,"Byte argument outside range");
            else if(args[i] instanceof Node) {
                Node n=node(args[i]);
                if(n.closure!=null&&n.image!=program) throw error("Closure belongs to another code image");
            }
        }
        if(f.intrinsic!=0) {
            intrinsic(f,args[0],args[1]); callsLeft=10_000_000; instructions=0;
            entry=f; phase=COMPLETE; pendingOwnedResult=true; return;
        }
        if(f.params.length==0&&constantReady[f.id]) {
            if(f.resultType==OBJ) { result=constants[f.id]; inc(result,1); }
            else scalarResult=(Long)constants[f.id];
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
        int newSp=Math.addExact(sp,f.width),newJsp=Math.addExact(jsp,f.joinWidth);
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
                if(f.paramTypes[i]==OBJ) objects[target]=args[i]; else numbers[target]=number(args[i]);
            }
        }
        k.caller=active; k.next=next; k.bp=bp; k.sp=sp; k.jbp=jbp; k.jsp=jsp;
        k.dest=dest; k.kind=kind; k.surplus=surplus;
        continuationDepth++;
        bp=sp; sp=newSp; jbp=jsp; jsp=newJsp; active=f; pc=f.body;
        tick();
    }

    /** Prepare and consume one AP exactly once; no guest execution here. */
    private boolean prepareExplicitApply(Object value,Object[] args) {
        Node closure=node(value); if(closure.closure==null) throw error("Expected closure");
        if(closure.image!=program) throw error("Closure belongs to another code image");
        Function f=closure.closure;
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
            if(f.intrinsic==0) { enterExplicit(f,null,actual,next,dest,APPLY,rest); return; }
            intrinsic(f,actual[0],actual[1]);
            value=f.resultType==OBJ?result:Long.valueOf(scalarResult);
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
        bp=k.bp; sp=k.sp; jbp=k.jbp; jsp=k.jsp; active=k.caller; pc=next;
        k.clear();
        if((kind&ROOT)!=0) {
            if(entry.params.length==0&&entry.resultType==OBJ) inc(result,1);
            pendingOwnedResult=true; phase=COMPLETE; return;
        }
        if((kind&APPLY)!=0) {
            Object answer=completed.resultType==OBJ?result:Long.valueOf(scalarResult);
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
                            if(f==active&&b.next.op==RET&&b.next.a==b.a) {
                                int scratch=sp; ensure(sp+e.args.length,jsp);
                                for(int i=0;i<e.args.length;i++) { objects[scratch+i]=obj(e.args[i]); numbers[scratch+i]=numbers[bp+e.args[i]]; }
                                for(int i=0;i<e.args.length;i++) { objects[bp+f.params[i]]=objects[scratch+i]; numbers[bp+f.params[i]]=numbers[scratch+i]; objects[scratch+i]=null; }
                                tick(); b=f.body;
                            } else if(e.args.length==0&&constantReady[f.id]) {
                                if(f.resultType==OBJ) objects[dest]=constants[f.id]; else numbers[dest]=(Long)constants[f.id];
                                b=b.next;
                            } else if(f.intrinsic!=0) {
                                intrinsic(f,obj(e.args[0]),obj(e.args[1]));
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
                    case SSET: { Node n=node(obj(b.a)); unique(n); if(b.type!=U8) throw error("Non-byte store"); int offset=Math.addExact(Math.multiplyExact(b.tags[0]-n.fields.length,8),b.b); n.scalars[offset]=(byte)numbers[bp+b.args[0]]; stores++; b=b.next; break; }
                    case SETTAG: { Node n=node(obj(b.a)); unique(n); n.tag=b.b; b=b.next; break; }
                    case INC: inc(obj(b.a),b.b); b=b.next; break;
                    case DEC: dec(obj(b.a),b.b); b=b.next; break;
                    case DEL: { Node n=node(obj(b.a)); unique(n); n.dead=true; Arrays.fill(n.fields,null); shellDeletes++; b=b.next; break; }
                    case CASE: {
                        Object value=b.type==OBJ?obj(b.a):null;
                        if(b.type==OBJ&&!(value instanceof Node)&&!(value instanceof Long)) throw error("Object case outside baseline value profile");
                        int tag=b.type==U8?(int)numbers[bp+b.a]:value instanceof Node?node(value).tag:((Long)value).intValue();
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
        Object value=entry.resultType==OBJ?result:Long.valueOf(scalarResult);
        pendingOwnedResult=false; result=null; entry=null; phase=IDLE;
        return value;
    }
    /** Internal owned-argument typed entry, not Lean's generic call_boxed ABI. */
    public Object invoke(int function,Object[] args) {
        if(closed) throw error("Interpreter closed");
        if(explicit) { start(function,args); advance(Long.MAX_VALUE); return takeResult(); }
        if(sp!=0) throw error("Reentrant external invocation unsupported");
        callsLeft=10_000_000;
        Function f=program.functions[function];
        if(args.length!=f.params.length) throw error("Arity mismatch: "+f.label);
        if(f.params.length==0) { load(f); if(f.resultType==OBJ) inc(result,1); }
        else enter(f,args);
        return f.resultType==OBJ?result:Long.valueOf(scalarResult);
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
        if(explicit&&(phase==RUNNING||phase==FAILED)) {
            closed=false;
            throw new IllegalStateException("Active or failed explicit execution requires ownership cleanup before close");
        }
        if(pendingOwnedResult&&entry.resultType==OBJ) dec(result,1);
        pendingOwnedResult=false;
        for(int i=0;i<constants.length;i++) if(constantReady[i]&&program.functions[i].resultType==OBJ) dec(constants[i],1);
        Arrays.fill(constants,null); Arrays.fill(objects,null); result=null;
    }
}
