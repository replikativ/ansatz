package ansatz.lean.jvm.internal.exec;

import java.math.BigInteger;
import java.util.*;
import ansatz.lean.jvm.internal.exec.Interpreter.Node;

/** Private detached pure-data storage. Plans are not source/native admission. */
final class FrozenValues {
    private static final java.util.concurrent.atomic.AtomicLong DETACHED_ALLOCATIONS=new java.util.concurrent.atomic.AtomicLong();
    private static Node allocated(Node node) { DETACHED_ALLOCATIONS.incrementAndGet();return node; }
    private static final int MAX_DATA_OCCURRENCES=100_000,MAX_DATA_INTEGER_BITS=4_194_304,
            MAX_DATA_STRING_UNITS=1_048_576,MAX_DATA_BUFFER_BYTES=1_048_576,MAX_ARRAY_CAPACITY=1_000_000;
    private static void dataRequire(boolean condition,String message) {
        if(!condition) throw new IllegalArgumentException(message);
    }
    /* PRIVATE storage foundation. Plans below are fixed internal test plans,
     * not native layout evidence and not an entry/public datatype admission API.
     * The capability is intentionally unreachable through the public SDK.
     * RECORD proves physical pure storage and sequential raw-byte lane coverage,
     * not logical scalar field correspondence or Bool/Char/range constraints.
     * Actual v3 evidence-derived plans must add those before public admission. */
    static final class FrozenPlan {
        static final int NAT=0,STRING=1,ENUM=2,RECORD=3,ARRAY=4,BYTES=5,ERASED=6,INT=7,SCALAR=8,FAMILY=9,UNIT=10;
        final int kind,tag,scalarBytes;
        final FrozenPlan[] children;
        final int[] scalarWidths;
        final Schema schema;final Row row;final String role;final Object key;
        FrozenPlan(int kind,int tag,int scalarBytes,FrozenPlan[] children,int[] scalarWidths) {
            dataRequire(kind>=NAT&&kind<=ERASED&&children!=null&&scalarWidths!=null,"Invalid private frozen plan");
            dataRequire(children.length<=64&&scalarWidths.length<=1024&&scalarBytes>=0&&scalarBytes<=1024,"Private plan extent");
            for(FrozenPlan child:children) dataRequire(child!=null,"Absent private child plan");
            int bytes=0;
            for(int width:scalarWidths) {
                dataRequire(width==1||width==2||width==4||width==8,"Private scalar width");
                dataRequire(bytes<=scalarBytes-width,"Private scalar layout extent");bytes+=width;
            }
            dataRequire(bytes==scalarBytes,"Private scalar layout must cover all bytes");
            dataRequire(kind!=RECORD||(tag>=0&&tag<=243),"Private allocated tag domain");
            dataRequire(kind!=ENUM||(tag>0&&tag<=65536),"Private enum domain");
            dataRequire((kind==RECORD)||(scalarBytes==0),"Private scalar layout requires record");
            dataRequire(kind==RECORD||children.length==((kind==ARRAY||kind==ERASED)?1:0),"Private plan child arity");
            this.schema=null;this.row=null;this.role="object";this.key=this;
            this.kind=kind;this.tag=tag;this.scalarBytes=scalarBytes;
            this.children=children.clone();this.scalarWidths=scalarWidths.clone();
        }
        FrozenPlan(Schema schema,Row row,String role) {
            this.schema=schema;this.row=row;this.role=role;this.kind=row.kind;
            tag=0;scalarBytes=row.kind==SCALAR&&!row.boxed.equals("small-immediate")?laneWidth(row.lane):0;
            children=new FrozenPlan[0];scalarWidths=new int[0];
            key=new PlanKey(schema.logicalKeys.get(row.id),schema.representationKeys.get(row.id),role,Node.class,FrozenValues.class);
        }
        FrozenPlan child(int id) { return schema.plan(id); }
        FrozenPlan raw(String lane) { return new FrozenPlan(schema,row,lane); }
    }
    /** Metadata proof DAG only. In particular a child proof never points at its
     * payload, its parent proof/root, a Program, interpreter, or callback. */
    static final class FrozenFootprint {
        final int slots,bytes,integerBits,stringUnits;
        FrozenFootprint(int slots,int bytes,int integerBits,int stringUnits) {
            this.slots=slots;this.bytes=bytes;this.integerBits=integerBits;this.stringUnits=stringUnits;
        }
    }
    static final class FrozenCert {
        final FrozenPlan plan;
        final FrozenFootprint footprint;
        final FrozenCert[] children;
        // payloadCost bounds scalar/buffer bytes; stringUnits counts logical
        // UTF-16 occurrences, including repeated shared leaves. Neither is a
        // measurement of retained heap. Cached frontiers need no payload walk.
        final long occurrences,capacityCost,payloadCost,integerCost,stringUnits;
        final int depth,live,capacity,constructorIndex,logicalLength;
        FrozenCert(FrozenPlan plan,FrozenCert[] children,int live,int capacity,FrozenFootprint footprint,int constructorIndex) {
            this.constructorIndex=constructorIndex;
            this.footprint=footprint;this.plan=plan;this.children=children;this.live=live;this.capacity=capacity;
            long count=1,slots=footprint==null?0:footprint.slots,bytes=footprint==null?0:footprint.bytes,bits=plan.schema!=null&&plan.kind==FrozenPlan.SCALAR?(Set.of("machine-int","word","char").contains(plan.row.type.get("kind"))?64:0):footprint==null?0:footprint.integerBits,strings=footprint==null?0:footprint.stringUnits;int height=1;
            for(FrozenCert child:children) {
                count=Math.min(MAX_DATA_OCCURRENCES+1L,count+child.occurrences);
                slots=Math.min(MAX_DATA_OCCURRENCES+1L,slots+child.capacityCost);
                bytes=Math.min(MAX_DATA_BUFFER_BYTES+1L,bytes+child.payloadCost);
                bits=Math.min(MAX_DATA_INTEGER_BITS+1L,bits+child.integerCost);
                strings=Math.min(MAX_DATA_STRING_UNITS+1L,strings+child.stringUnits);
                height=Math.max(height,1+child.depth);
            }
            dataRequire(count<=MAX_DATA_OCCURRENCES&&height<=1024,"Frozen logical occurrence/depth bound");
            dataRequire(strings<=MAX_DATA_STRING_UNITS,"Frozen logical String aggregate budget exceeded");
            dataRequire(plan.schema==null||bits<=MAX_DATA_INTEGER_BITS,"Frozen logical integer aggregate budget exceeded");
            String logical=plan.schema==null?"":text(plan.row.type.get("kind"));
            logicalLength=logical.equals("list")?(constructorIndex==0?0:1+children[1].logicalLength):plan.kind==FrozenPlan.ARRAY||plan.kind==FrozenPlan.BYTES?live:children.length;
            occurrences=count;depth=height;capacityCost=slots;payloadCost=bytes;integerCost=bits;stringUnits=strings;
        }
        FrozenCert(FrozenCert root,long capacityCost,long payloadCost,long integerCost) {
            plan=root.plan;footprint=root.footprint;children=root.children;occurrences=root.occurrences;
            depth=root.depth;live=root.live;capacity=root.capacity;stringUnits=root.stringUnits;constructorIndex=root.constructorIndex;logicalLength=root.logicalLength;
            this.capacityCost=capacityCost;this.payloadCost=payloadCost;this.integerCost=integerCost;
        }
    }
    /** A monotone physical immutability marker plus the initial typed proofs.
     * A marker alone never authenticates a different interpretation/plan. */
    static final class FrozenStamp {
        final FrozenFootprint footprint;
        private final Map<Object,FrozenCert> proofs;
        FrozenStamp(Map<Object,FrozenCert> proofs,FrozenFootprint footprint) {
            this.footprint=footprint;this.proofs=Map.copyOf(proofs);
        }
        FrozenCert find(FrozenPlan plan) { return proofs.get(plan.key); }
    }

    static final class FrozenInput {
        final Object value;
        final FrozenCert cert;
        // Written AFTER every physical commit; acquiring this is required even
        // though final fields were assigned before Node writes became visible.
        private volatile boolean published;
        FrozenInput(Object value,FrozenCert cert) { this.value=value;this.cert=cert; }
        Object acquire() {
            dataRequire(published,"Unpublished frozen capability"); return value;
        }
    }
    static final class FreezeFrame {
        final Object value;
        final FrozenPlan plan;
        FrozenCert[] children;
        int next,live,capacity,numeric;
        Alternative alternative;FrozenFootprint footprint;
        boolean entered,owning;
        FreezeFrame(Object value,FrozenPlan plan) { this.value=value;this.plan=plan; }
    }
    private static void freezePoll() {
        if (Thread.currentThread().isInterrupted()) throw new java.util.concurrent.CancellationException("Frozen preflight interrupted");
    }
    private static final class RawBits {
        final String lane;final long bits;
        RawBits(String lane,long bits) { this.lane=lane;this.bits=bits; }
    }
    private static long scalarBits(Object value,FrozenPlan plan) {
        String lane=plan.schema.rawLanes.get(plan.row.id);dataRequire(lane!=null,"Logical type has no scalar representation");
        int aliases=0;
        while(plan.role.equals("object")&&plan.row.kind==FrozenPlan.FAMILY&&plan.row.alternatives[0].kind.equals("alias")) {
            dataRequire(++aliases<=1024,"Scalar alias depth");Alternative a=plan.row.alternatives[0];plan=plan.child(a.fields[a.alias].plan);
        }
        long bits;
        if(!plan.role.equals("object")) { dataRequire(value!=null&&value.getClass()==RawBits.class&&((RawBits)value).lane.equals(lane),"Raw scalar role mismatch");bits=((RawBits)value).bits; }
        else if(plan.row.kind==FrozenPlan.FAMILY) {
            Alternative a=plan.row.alternatives[0];
            dataRequire(value!=null&&value.getClass()==Long.class,"Enum immediate required");bits=(Long)value;
        } else if(plan.row.boxed.equals("small-immediate")) { dataRequire(value!=null&&value.getClass()==Long.class,"Small scalar immediate required");bits=(Long)value; }
        else {
            dataRequire(value!=null&&value.getClass()==Node.class,"Scalar box required");Node node=(Node)value;int width=laneWidth(lane);
            dataRequire(node.storageKind()==0&&node.storageTag()==0&&node.fieldCount()==0&&node.scalarCount()==width,"Scalar box layout");bits=node.storageBits(0,width);
        }
        int width=laneWidth(lane);dataRequire(width==8||(bits>=0&&bits<(1L<<(width*8))),"Raw scalar width");
        return bits;
    }
    private static void scalarDomain(FrozenPlan plan,long bits) {
        String logical=text(plan.row.type.get("kind"));
        if(logical.equals("bool")) dataRequire(bits==0||bits==1,"Bool requires zero or one");
        if(logical.equals("char")) dataRequire(bits>=0&&bits<=0x10ffff&&(bits<0xd800||bits>0xdfff),"Char requires Unicode scalar");
    }
    private static Alternative select(FrozenPlan plan,Object value) {
        Row row=plan.row;if(row.alternatives.length==1&&row.alternatives[0].kind.equals("alias")) return row.alternatives[0];
        long tag;
        if(!plan.role.equals("object")) tag=scalarBits(value,plan);
        else if(value!=null&&value.getClass()==Node.class) tag=((Node)value).storageTag();
        else { dataRequire(value!=null&&value.getClass()==Long.class,"Constructor carrier");tag=(Long)value; }
        dataRequire(tag>=0&&tag<row.alternatives.length,"Constructor membership");Alternative alternative=row.alternatives[(int)tag];
        dataRequire((alternative.kind.equals("node"))==(value instanceof Node),"Immediate/allocated constructor mismatch");return alternative;
    }
    private static FrozenInput published(Object value,FrozenCert cert) { FrozenInput out=new FrozenInput(value,cert);out.published=true;return out; }
    private static void checkNode(FreezeFrame frame,IdentityHashMap<Node,Boolean> active,int kind,int tag,int fields,int scalars) {
        dataRequire(frame.value!=null&&frame.value.getClass()==Node.class,"Exact frozen Node required");Node node=(Node)frame.value;
        dataRequire(!active.containsKey(node),"Frozen runtime owning cycle");active.put(node,Boolean.TRUE);frame.owning=true;
        dataRequire(node.storageKind()==kind&&node.storageTag()==tag&&node.fieldCount()==fields&&node.scalarCount()==scalars,"Frozen storage kind/layout");
    }
    static FrozenInput freeze(Object value,FrozenPlan plan) {
        dataRequire(plan!=null,"Absent frozen plan");freezePoll();
        if(value instanceof Node) { FrozenStamp stamp=((Node)value).frozenState();FrozenCert cert=stamp==null?null:stamp.find(plan);if(cert!=null) return published(value,cert); }
        IdentityHashMap<Object,FrozenFootprint> footprints=new IdentityHashMap<>();
        IdentityHashMap<FrozenFootprint,Boolean> accounted=new IdentityHashMap<>();IdentityHashMap<FrozenCert,Boolean> proofSeen=new IdentityHashMap<>();
        IdentityHashMap<Object,Map<Object,FrozenCert>> memo=new IdentityHashMap<>();IdentityHashMap<Node,Boolean> physical=new IdentityHashMap<>(),active=new IdentityHashMap<>();
        ArrayList<Node> commit=new ArrayList<>();ArrayDeque<FreezeFrame> stack=new ArrayDeque<>();stack.push(new FreezeFrame(value,plan));
        FrozenCert answer=null;long work=0,payload=0,integerBits=0,stringValidation=0;int pairs=0;
        while(!stack.isEmpty()) {
            freezePoll();FreezeFrame frame=stack.peek();Object current=frame.value;FrozenPlan p=frame.plan;dataRequire(current!=null,"Absent frozen field");
            if(!frame.entered) {
                Map<Object,FrozenCert> byPlan=memo.get(current);FrozenCert known=byPlan==null?null:byPlan.get(p.key);boolean cached=false;
                if(known==null&&current instanceof Node) { FrozenStamp stamp=((Node)current).frozenState();if(stamp!=null) { known=stamp.find(p);cached=known!=null; } }
                if(known!=null) {
                    if(cached&&proofSeen.put(known,Boolean.TRUE)==null) {
                        work+=known.capacityCost;payload+=known.payloadCost;integerBits+=known.integerCost;
                        dataRequire(work<=MAX_DATA_OCCURRENCES&&payload<=MAX_DATA_BUFFER_BYTES&&integerBits<=MAX_DATA_INTEGER_BITS,"Frozen cached frontier budget");
                    }
                    stack.pop();if(stack.isEmpty()) answer=known;else { FreezeFrame parent=stack.peek();parent.children[parent.next-1]=known; }continue;
                }
                dataRequire(++pairs<=MAX_DATA_OCCURRENCES&&stack.size()<=1024,"Frozen typed-pair/depth bound");frame.entered=true;
                if(p.kind==FrozenPlan.ERASED) frame.children=new FrozenCert[1];
                else if(p.kind==FrozenPlan.NAT||p.kind==FrozenPlan.INT) {
                    dataRequire(current.getClass()==Long.class||current.getClass()==BigInteger.class,"Exact integer leaf required");
                    if(current.getClass()==Long.class) dataRequire(p.kind==FrozenPlan.INT||(Long)current>=0,"Negative Nat");
                    else { BigInteger n=(BigInteger)current;dataRequire((p.kind==FrozenPlan.INT||n.signum()>=0)&&n.bitLength()<=4096&&n.abs().bitLength()<=4096,"Integer leaf bound"); }
                    FrozenFootprint footprint=footprints.get(current);
                    if(footprint==null) { footprint=new FrozenFootprint(0,0,current.getClass()==Long.class?64:((BigInteger)current).abs().bitLength(),0);footprints.put(current,footprint); }
                    frame.footprint=footprint;frame.children=new FrozenCert[0];
                } else if(p.kind==FrozenPlan.STRING) {
                    dataRequire(current.getClass()==String.class,"Exact String leaf required");String text=(String)current;dataRequire(text.length()<=65536,"String leaf bound");
                    FrozenFootprint footprint=footprints.get(current);
                    if(footprint==null) {
                        stringValidation+=text.length();dataRequire(stringValidation<=MAX_DATA_STRING_UNITS,"String validation bound");unicode(text,65536);
                        footprint=new FrozenFootprint(0,0,0,text.length());footprints.put(current,footprint);
                    }frame.footprint=footprint;frame.children=new FrozenCert[0];
                } else if(p.kind==FrozenPlan.UNIT) {
                    dataRequire(current.getClass()==Long.class&&(Long)current==0,"Canonical Unit required");frame.children=new FrozenCert[0];
                } else if(p.kind==FrozenPlan.ENUM) {
                    dataRequire(current.getClass()==Long.class&&(Long)current>=0&&(Long)current<p.tag,"Enum domain");frame.children=new FrozenCert[0];
                } else if(p.kind==FrozenPlan.SCALAR) {
                    long bits=scalarBits(current,p);scalarDomain(p,bits);
                    String logical=text(p.row.type.get("kind"));int numeric=Set.of("machine-int","word","char").contains(logical)?64:0;
                    if(current instanceof Node) { checkNode(frame,active,0,0,0,laneWidth(p.row.lane));frame.numeric=numeric; }
                    else frame.footprint=new FrozenFootprint(0,0,numeric,0);
                    frame.children=new FrozenCert[0];
                } else if(p.kind==FrozenPlan.FAMILY) {
                    frame.alternative=select(p,current);Alternative a=frame.alternative;frame.children=new FrozenCert[a.fields.length];
                    if(a.kind.equals("node")) { checkNode(frame,active,0,a.tag,a.objects,a.scalarBytes());frame.live=a.objects;frame.capacity=a.objects; }
                } else {
                    dataRequire(current.getClass()==Node.class,"Exact frozen Node required");Node node=(Node)current;int live;
                    if(p.kind==FrozenPlan.ARRAY) {
                        dataRequire(node.storageKind()==1,"Array runtime kind");live=node.storageLive();dataRequire(live>=0&&live<=node.fieldCount()&&node.fieldCount()<=MAX_ARRAY_CAPACITY,"Array extent");
                        checkNode(frame,active,1,246,node.fieldCount(),0);frame.live=live;frame.capacity=node.fieldCount();frame.children=new FrozenCert[live];
                    } else if(p.kind==FrozenPlan.BYTES) {
                        dataRequire(node.storageKind()==2,"ByteArray runtime kind");live=node.storageLive();dataRequire(live>=0&&live<=node.scalarCount()&&node.scalarCount()<=MAX_DATA_BUFFER_BYTES,"ByteArray extent");
                        checkNode(frame,active,2,248,0,node.scalarCount());frame.live=live;frame.capacity=node.scalarCount();frame.children=new FrozenCert[0];
                    } else {
                        checkNode(frame,active,0,p.tag,p.children.length,p.scalarBytes);frame.live=node.fieldCount();frame.capacity=frame.live;frame.children=new FrozenCert[frame.live];
                    }
                }
                if(frame.owning) {
                    Node node=(Node)current;
                    if(!physical.containsKey(node)) {
                        physical.put(node,Boolean.TRUE);dataRequire(physical.size()<=MAX_DATA_OCCURRENCES,"Physical node bound");
                        FrozenFootprint footprint=node.frozenState()==null?new FrozenFootprint(node.fieldCount(),node.scalarCount(),frame.numeric,0):node.frozenState().footprint;
                        footprints.put(node,footprint);frame.footprint=footprint;
                        for(int i=0;i<node.fieldCount();i++) { if((i&1023)==0) freezePoll();if(i<frame.live) dataRequire(node.storageField(i)!=null,"Absent owning field");else dataRequire(node.storageField(i)==null,"Array spare must be null"); }
                        if(node.frozenState()==null) commit.add(node);
                    } else frame.footprint=footprints.get(node);
                }
                if(frame.footprint!=null&&accounted.put(frame.footprint,Boolean.TRUE)==null) {
                    work+=frame.footprint.slots;payload+=frame.footprint.bytes;integerBits+=frame.footprint.integerBits;
                    dataRequire(work<=MAX_DATA_OCCURRENCES&&payload<=MAX_DATA_BUFFER_BYTES&&integerBits<=MAX_DATA_INTEGER_BITS,"Frozen physical payload budget");
                }
            }
            if(frame.next<frame.children.length) {
                int index=frame.next++;Object child;FrozenPlan cp;
                if(p.kind==FrozenPlan.ERASED) { child=current;cp=p.children[0]; }
                else if(p.kind==FrozenPlan.FAMILY) {
                    Binding b=frame.alternative.fields[index];cp=p.child(b.plan);
                    switch(b.kind) {
                        case "object":child=((Node)current).storageField(b.index);break;
                        case "scalar":case "usize":child=new RawBits(b.lane,((Node)current).storageBits(b.offset,laneWidth(b.lane)));cp=cp.raw(b.lane);break;
                        case "self":child=current;if(!p.role.equals("object")) cp=cp.raw(p.role);break;
                        case "unit":child=0L;break;
                        default:throw new AssertionError("Validated binding");
                    }
                } else { child=((Node)current).storageField(index);cp=p.schema==null?(p.kind==FrozenPlan.ARRAY?p.children[0]:p.children[index]):p.child(p.row.element); }
                stack.push(new FreezeFrame(child,cp));continue;
            }
            FrozenCert cert=new FrozenCert(p,frame.children,frame.live,frame.capacity,frame.footprint,frame.alternative==null?-1:frame.alternative.index);
            Map<Object,FrozenCert> byPlan=memo.get(current);if(byPlan==null) { byPlan=new HashMap<>();memo.put(current,byPlan); }byPlan.put(p.key,cert);
            if(frame.owning) active.remove((Node)current);stack.pop();if(stack.isEmpty()) answer=cert;else { FreezeFrame parent=stack.peek();parent.children[parent.next-1]=cert; }
        }
        answer=new FrozenCert(answer,work,payload,plan.schema==null?integerBits:answer.integerCost);
        Map<Object,FrozenCert> rootProofs=memo.get(value);if(rootProofs!=null) rootProofs.put(plan.key,answer);
        FrozenStamp[] stamps=new FrozenStamp[commit.size()];for(int i=0;i<stamps.length;i++) { freezePoll();stamps[i]=new FrozenStamp(memo.get(commit.get(i)),footprints.get(commit.get(i))); }
        FrozenInput output=new FrozenInput(value,answer);freezePoll();
        for(int i=0;i<stamps.length;i++) commit.get(i).commitFrozen(stamps[i]);
        output.published=true;return output;
    }

    /* Strict private normalized programs. Syntax and internal correspondence
     * are checked here; native origin/declaration authority is a future layer. */
    private static final Set<String> LANES=Set.of("uint8","uint16","uint32","uint64","usize","float","float32");
    private static final Set<String> OBJECT_LANES=Set.of("object","tobject","tagged");
    private static Map<String,Object> object(Object value) {
        dataRequire(value instanceof Map,"Expected copied data object");
        @SuppressWarnings("unchecked") Map<String,Object> result=(Map<String,Object>)value;return result;
    }
    private static List<?> vector(Object value,int maximum) {
        dataRequire(value instanceof List&&((List<?>)value).size()<=maximum,"Bounded data vector required");return (List<?>)value;
    }
    private static int number(Object value,int maximum) {
        dataRequire(value!=null&&(value.getClass()==Long.class||value.getClass()==Integer.class),"Exact bounded integer required");
        long n=((Number)value).longValue();dataRequire(n>=0&&n<=maximum,"Data integer bound");return (int)n;
    }
    private static String text(Object value) { dataRequire(value!=null&&value.getClass()==String.class,"Exact data String required");return (String)value; }
    private static void keys(Map<String,Object> map,String... names) {
        dataRequire(map.size()==names.length&&map.keySet().equals(Set.of(names)),"Unexpected data object keys");
    }
    private static Map<String,Object> obj(Object... pairs) {
        TreeMap<String,Object> out=new TreeMap<>();for(int i=0;i<pairs.length;i+=2) out.put((String)pairs[i],pairs[i+1]);return Map.copyOf(out);
    }
    private static void unicode(String text,int maximum) {
        dataRequire(text.length()<=maximum,"String leaf extent");
        for(int i=0;i<text.length();i++) {
            if((i&1023)==0) freezePoll();char c=text.charAt(i);
            if(Character.isHighSurrogate(c)) dataRequire(++i<text.length()&&Character.isLowSurrogate(text.charAt(i)),"Invalid UTF-16");
            else dataRequire(!Character.isLowSurrogate(c),"Invalid UTF-16");
        }
    }
    private static boolean trustedMap(Object value) {
        Class<?> c=value.getClass();return c==HashMap.class||c==LinkedHashMap.class||c==TreeMap.class
                ||c==Map.of().getClass()||c==Map.of("x",1).getClass();
    }
    private static boolean trustedList(Object value) {
        Class<?> c=value.getClass();return c==ArrayList.class||c==Arrays.asList(1).getClass()
                ||c==List.of().getClass()||c==List.of(1).getClass()
                ||c==Collections.emptyList().getClass()||c==Collections.singletonList(1).getClass();
    }
    private static Object snapshot(Object input,int depth,int[] work,boolean tape) {
        freezePoll();dataRequire(depth<128&&++work[0]<=100_000&&input!=null,"Data document depth/work/null bound");
        Class<?> c=input.getClass();
        if(c==String.class) {
            work[2]=Math.addExact(work[2],((String)input).length());
            dataRequire(work[2]<=(tape?2_097_152:1_048_576),"Snapshot cumulative String validation budget");
            unicode((String)input,1_048_576);return input;
        }
        if(c==Long.class||c==Integer.class) return Long.valueOf(((Number)input).longValue());
        if(c==Boolean.class) return input;
        if(tape&&c==FrozenInput.class) { ((FrozenInput)input).acquire();return input; }
        if(tape&&c==BigInteger.class) { dataRequire(((BigInteger)input).abs().bitLength()<=4096,"Tape integer bound");return input; }
        if(tape&&c==byte[].class) {
            work[1]=Math.addExact(work[1],((byte[])input).length);dataRequire(work[1]<=MAX_DATA_BUFFER_BYTES,"Tape byte snapshot bound");return ((byte[])input).clone();
        }
        if(trustedMap(input)) {
            Map<?,?> source=(Map<?,?>)input;dataRequire(source.size()<=8192,"Data map extent");TreeMap<String,Object> out=new TreeMap<>();
            for(Map.Entry<?,?> entry:source.entrySet()) out.put((String)snapshot(text(entry.getKey()),depth+1,work,tape),snapshot(entry.getValue(),depth+1,work,tape));
            return Map.copyOf(out);
        }
        if(trustedList(input)) {
            List<?> source=(List<?>)input;dataRequire(source.size()<=100_000,"Data vector extent");ArrayList<Object> out=new ArrayList<>(source.size());
            for(Object child:source) out.add(snapshot(child,depth+1,work,tape));return List.copyOf(out);
        }
        throw new IllegalArgumentException("Only exact trusted data carriers are accepted");
    }
    private static void json(Object value,StringBuilder out) {
        if(value instanceof Map) {
            out.append('{');boolean first=true;for(Map.Entry<String,Object> entry:new TreeMap<>(object(value)).entrySet()) {
                if(!first) out.append(',');first=false;json(entry.getKey(),out);out.append(':');json(entry.getValue(),out);
            }out.append('}');
        } else if(value instanceof List) {
            out.append('[');boolean first=true;for(Object child:(List<?>)value) { if(!first) out.append(',');first=false;json(child,out); }out.append(']');
        } else if(value instanceof String) {
            out.append('"');String s=(String)value;for(int i=0;i<s.length();i++) {
                char c=s.charAt(i);switch(c) {
                    case '"':out.append("\\\"");break;case '\\':out.append("\\\\");break;
                    case '\n':out.append("\\n");break;case '\r':out.append("\\r");break;case '\t':out.append("\\t");break;
                    case '\b':out.append("\\b");break;case '\f':out.append("\\f");break;
                    default:if(c<32||c==0x2028||c==0x2029) out.append(String.format(Locale.ROOT,"\\u%04x",(int)c));else out.append(c);
                }
            }out.append('"');
        } else { dataRequire(value instanceof Long||value instanceof Integer||value instanceof Boolean,"JSON scalar");out.append(value); }
        dataRequire(out.length()<=1_048_576,"Encoded data extent");
    }
    private static String digest(Object value) { return digest(value,null); }
    private static String digest(Object value,long[] work) {
        StringBuilder text=new StringBuilder();json(value,text);byte[] bytes=text.toString().getBytes(java.nio.charset.StandardCharsets.UTF_8);
        dataRequire(bytes.length<=1_048_576,"Encoded data byte extent");
        if(work!=null) { work[0]+=bytes.length;dataRequire(work[0]<=67_108_864,"Schema aggregate hashing work bound"); }
        try { return HexFormat.of().formatHex(java.security.MessageDigest.getInstance("SHA-256").digest(bytes)); }
        catch(java.security.NoSuchAlgorithmException impossible) { throw new AssertionError(impossible); }
    }
    private static void hex(Object value) { dataRequire(text(value).matches("[0-9a-f]{64}"),"Canonical SHA256 required"); }
    private static void name(Object value,boolean nonanonymous,int[] units) {
        List<?> n=vector(value,3);dataRequire(!nonanonymous||!n.equals(List.of("anonymous")),"Nonanonymous Name required");int depth=0;
        while(!n.equals(List.of("anonymous"))) {
            dataRequire(++depth<64&&n.size()==3,"Name shape/depth");String kind=text(n.get(0)),part=text(n.get(2));unicode(part,1024);
            units[0]+=part.length();dataRequire(units[0]<=65536,"Aggregate Name extent");
            if(kind.equals("num")) {
                dataRequire(part.matches("0|[1-9][0-9]*")&&part.length()<=20,"Canonical numeric Name");
                dataRequire(new BigInteger(part).bitLength()<=64,"Numeric Name overflow");
            } else dataRequire(kind.equals("str"),"Name component kind");n=vector(n.get(1),3);
        }
    }
    private static List<Map<String,Object>> typeChildren(Map<String,Object> t) {
        String kind=text(t.get("kind"));return switch(kind) {
            case "option","list","array"->List.of(object(t.get("element")));
            case "product"->List.of(object(t.get("first")),object(t.get("second")));
            case "sum"->List.of(object(t.get("left")),object(t.get("right")));
            case "except"->List.of(object(t.get("error")),object(t.get("value")));
            default->List.of();
        };
    }
    private static void type(Map<String,Object> t,Map<Integer,Map<String,Object>> defs,int depth,int[] work) {
        dataRequire(depth<32&&++work[0]<=8192,"Logical type depth/visits");String kind=text(t.get("kind"));
        switch(kind) {
            case "nat","int","bool","string","unit","char","bytes":keys(t,"kind");break;
            case "nominal":keys(t,"kind","id");dataRequire(defs.containsKey(number(t.get("id"),255)),"Missing nominal reference");break;
            case "machine-int":keys(t,"kind","bits","signed");dataRequire(Set.of(8,16,32,64).contains(number(t.get("bits"),64))&&t.get("signed") instanceof Boolean,"Machine type");break;
            case "word":keys(t,"kind","signed");dataRequire(t.get("signed") instanceof Boolean,"Word signedness");break;
            case "float":keys(t,"kind","bits");dataRequire(Set.of(32,64).contains(number(t.get("bits"),64)),"Float type");break;
            case "option","list","array":keys(t,"kind","element");break;
            case "product":keys(t,"kind","first","second");break;
            case "sum":keys(t,"kind","left","right");break;
            case "except":keys(t,"kind","error","value");break;
            default:throw new IllegalArgumentException("Unsupported logical kind");
        }
        if(kind.equals("nominal")) dataRequire(++work[1]<=4096,"Logical edge bound");
        for(Map<String,Object> child:typeChildren(t)) { dataRequire(++work[1]<=4096,"Logical edge bound");type(child,defs,depth+1,work); }
    }
    private static List<Map<String,Object>> definitionTypes(Map<String,Object> d) {
        List<Map<String,Object>> out=new ArrayList<>();for(Object t:vector(d.get("arguments"),64)) out.add(object(t));
        for(Object c:vector(d.get("constructors"),1024)) for(Object f:vector(object(c).get("fields"),64)) out.add(object(object(f).get("type")));return out;
    }
    private static Set<Integer> nominalRefs(Collection<Map<String,Object>> types) {
        Set<Integer> seen=new HashSet<>();ArrayDeque<Map<String,Object>> todo=new ArrayDeque<>(types);
        while(!todo.isEmpty()) { Map<String,Object> t=todo.pop();if("nominal".equals(t.get("kind"))) seen.add(number(t.get("id"),255));else todo.addAll(typeChildren(t)); }return seen;
    }
    private static Set<Integer> closure(Map<Integer,Set<Integer>> edges,Collection<Integer> seed) {
        Set<Integer> out=new HashSet<>();ArrayDeque<Integer> todo=new ArrayDeque<>(seed);
        while(!todo.isEmpty()) { int id=todo.pop();if(out.add(id)) todo.addAll(edges.get(id)); }return out;
    }
    private static Object rewrite(Object value,Map<Integer,Integer> ids) {
        if(value instanceof Map) {
            Map<String,Object> in=object(value);TreeMap<String,Object> out=new TreeMap<>();
            for(Map.Entry<String,Object> e:in.entrySet()) out.put(e.getKey(),rewrite(e.getValue(),ids));
            if("nominal".equals(in.get("kind"))) out.put("id",Long.valueOf(ids.get(number(in.get("id"),255))));
            return Map.copyOf(out);
        }
        if(value instanceof List) { List<Object> out=new ArrayList<>();for(Object child:(List<?>)value) out.add(rewrite(child,ids));return List.copyOf(out); }return value;
    }
    private static LinkedHashMap<Integer,Integer> canonicalIds(Map<Integer,Map<String,Object>> defs,List<?> roots) {
        LinkedHashMap<Integer,Integer> ids=new LinkedHashMap<>();ArrayDeque<Map<String,Object>> todo=new ArrayDeque<>();
        for(int i=roots.size()-1;i>=0;i--) todo.push(object(roots.get(i)));
        while(!todo.isEmpty()) {
            Map<String,Object> t=todo.pop();List<Map<String,Object>> children;
            if("nominal".equals(t.get("kind"))) {
                int id=number(t.get("id"),255);if(ids.containsKey(id)) continue;ids.put(id,ids.size());children=definitionTypes(defs.get(id));
            } else children=typeChildren(t);
            for(int i=children.size()-1;i>=0;i--) todo.push(children.get(i));
        }
        return ids;
    }
    private static Map<String,Object> canonicalLogical(Map<Integer,Map<String,Object>> defs,List<?> roots) {
        LinkedHashMap<Integer,Integer> ids=canonicalIds(defs,roots);
        List<Object> normalized=new ArrayList<>();for(int id:ids.keySet()) { TreeMap<String,Object> d=new TreeMap<>(object(rewrite(defs.get(id),ids)));d.put("id",Long.valueOf(ids.get(id)));normalized.add(Map.copyOf(d)); }
        return obj("schema","lean-jvm-type-graph/3","roots",rewrite(roots,ids),"definitions",List.copyOf(normalized));
    }
    private static Object applicationRefs(Object value,Map<Integer,String> digests) {
        if(value instanceof Map) {
            Map<String,Object> m=object(value);
            if("nominal".equals(m.get("kind"))) { String hash=digests.get(number(m.get("id"),255));dataRequire(hash!=null,"Application argument dependency order");return obj("kind","closed-application","digest",hash); }
            TreeMap<String,Object> out=new TreeMap<>();for(Map.Entry<String,Object> e:m.entrySet()) out.put(e.getKey(),applicationRefs(e.getValue(),digests));return Map.copyOf(out);
        }
        if(value instanceof List) { List<Object> out=new ArrayList<>();for(Object child:(List<?>)value) out.add(applicationRefs(child,digests));return List.copyOf(out); }return value;
    }
    private static Map<Integer,Map<String,Object>> logical(Map<String,Object> g) {
        keys(g,"schema","roots","definitions");dataRequire("lean-jvm-type-graph/3".equals(g.get("schema")),"Logical schema version");
        List<?> roots=vector(g.get("roots"),1024);dataRequire(!roots.isEmpty()&&new HashSet<>(roots).size()==roots.size(),"Logical roots");
        Map<Integer,Map<String,Object>> defs=new HashMap<>();int constructors=0;int[] units={0},work={0,0};
        for(Object raw:vector(g.get("definitions"),256)) {
            Map<String,Object> d=object(raw);keys(d,"id","origin","name","universes","arguments","constructors");int id=number(d.get("id"),255);dataRequire(defs.put(id,d)==null,"Duplicate definition");
        }
        for(Map<String,Object> d:defs.values()) {
            Map<String,Object> origin=object(d.get("origin"));keys(origin,"module","productSha256");name(origin.get("module"),true,units);hex(origin.get("productSha256"));name(d.get("name"),true,units);
            for(Object u:vector(d.get("universes"),32)) number(u,255);
            for(Object t:vector(d.get("arguments"),64)) type(object(t),defs,0,work);
            List<?> cs=vector(d.get("constructors"),1024);dataRequire(!cs.isEmpty(),"Empty nominal family");Set<Object> names=new HashSet<>();
            for(Object raw:cs) {
                dataRequire(++constructors<=1024,"Constructor bound");Map<String,Object> c=object(raw);keys(c,"name","fields");name(c.get("name"),true,units);dataRequire(names.add(c.get("name")),"Duplicate constructor Name");
                for(Object f:vector(c.get("fields"),64)) { Map<String,Object> field=object(f);keys(field,"name","type");name(field.get("name"),false,units);type(object(field.get("type")),defs,0,work); }
            }
        }
        for(Object t:roots) type(object(t),defs,0,work);
        Map<Integer,Set<Integer>> edges=new HashMap<>(),args=new HashMap<>();
        for(int id:defs.keySet()) {
            Map<String,Object> d=defs.get(id);edges.put(id,nominalRefs(definitionTypes(d)));List<Map<String,Object>> a=new ArrayList<>();for(Object t:vector(d.get("arguments"),64)) a.add(object(t));args.put(id,nominalRefs(a));dataRequire(!args.get(id).contains(id),"Recursive nominal argument");
        }
        Set<Integer> done=new HashSet<>();List<Integer> order=new ArrayList<>();
        while(done.size()<defs.size()) {
            boolean progress=false;for(int id:new TreeSet<>(defs.keySet())) if(!done.contains(id)) {
                Set<Integer> needs=new HashSet<>(edges.get(id));needs.remove(id);if(done.containsAll(needs)) { done.add(id);order.add(id);progress=true; }
            }dataRequire(progress,"Mutual/nonregular schema recursion");
        }
        for(int id:defs.keySet()) for(int other:closure(edges,edges.get(id))) if(other!=id) {
            Map<String,Object> a=defs.get(id),b=defs.get(other);
            if(a.get("origin").equals(b.get("origin"))&&a.get("name").equals(b.get("name"))) dataRequire(closure(edges,args.get(id)).contains(other),"Changed recursive application");
        }
        Map<Integer,String> applications=new HashMap<>();Set<String> identities=new HashSet<>();
        for(int id:order) { Map<String,Object> d=defs.get(id);String key=digest(List.of(d.get("origin"),d.get("name"),d.get("universes"),applicationRefs(d.get("arguments"),applications)));dataRequire(identities.add(key),"Duplicate closed nominal application");applications.put(id,key); }
        dataRequire(vector(canonicalLogical(defs,roots).get("definitions"),256).size()==defs.size(),"Unreachable nominal definition");return defs;
    }
    private record PlanKey(String logical,String representation,String role,Class<?> nodeClass,Class<?> helperClass) { }
    private static final class Binding {
        final int plan,index,offset;final String kind,lane;
        Binding(int plan,int index,int offset,String kind,String lane) { this.plan=plan;this.index=index;this.offset=offset;this.kind=kind;this.lane=lane; }
    }
    private static final class Alternative {
        final int index,tag,objects,usize,ssize,alias;final String kind;final Binding[] fields;
        Alternative(int index,int tag,int objects,int usize,int ssize,int alias,String kind,Binding[] fields) {
            this.index=index;this.tag=tag;this.objects=objects;this.usize=usize;this.ssize=ssize;this.alias=alias;this.kind=kind;this.fields=fields;
        }
        int scalarBytes() { return usize*8+ssize; }
    }
    private static final class Row {
        final int id,kind,element;final int[] arguments;final String closedIR,lane,boxed;final Map<String,Object> type,encoding;final Alternative[] alternatives;
        Row(int id,int kind,int element,int[] arguments,String closedIR,String lane,String boxed,Map<String,Object> type,Map<String,Object> encoding,Alternative[] alternatives) {
            this.id=id;this.kind=kind;this.element=element;this.arguments=arguments;this.closedIR=closedIR;this.lane=lane;this.boxed=boxed;this.type=type;this.encoding=encoding;this.alternatives=alternatives;
        }
    }
    static final class Schema {
        final Map<String,Object> logical,normalized,metadata;
        final Map<Integer,Row> rows;final Map<Integer,String> logicalKeys,representationKeys,rawLanes;
        Schema(Map<String,Object> logical,Map<String,Object> normalized,Map<Integer,Row> rows,Map<Integer,String> logicalKeys,Map<Integer,String> representationKeys) {
            Map<Integer,String> lanes=new HashMap<>();for(Row row:rows.values()) { String lane=rowRawLane(row,rows);if(lane!=null) lanes.put(row.id,lane); }rawLanes=Map.copyOf(lanes);
            this.logical=logical;this.normalized=normalized;this.rows=Map.copyOf(rows);this.logicalKeys=Map.copyOf(logicalKeys);this.representationKeys=Map.copyOf(representationKeys);
            metadata=obj("logical",logical,"normalized",normalized,"typeDigests",Map.copyOf(new TreeMap<>(logicalKeys)));
        }
        FrozenPlan plan(int id) { Row row=rows.get(id);dataRequire(row!=null,"Unknown plan row");return new FrozenPlan(this,row,"object"); }
    }
    private static int laneWidth(String lane) { return switch(lane) { case "uint8"->1;case "uint16"->2;case "uint32","float32"->4;case "uint64","usize","float"->8;default->throw new IllegalArgumentException("Unknown lane"); }; }
    private static String scalarLane(Map<String,Object> type) {
        return switch(text(type.get("kind"))) {
            case "bool"->"uint8";case "char"->"uint32";case "machine-int"->"uint"+number(type.get("bits"),64);
            case "word"->"usize";case "float"->number(type.get("bits"),64)==32?"float32":"float";default->null;
        };
    }
    private static Object builtinName(String family,String ctor) { return List.of("str",List.of("str",List.of("anonymous"),family),ctor); }
    private static List<Map<String,Object>> logicalConstructors(Map<String,Object> type,Map<Integer,Map<String,Object>> defs) {
        String kind=text(type.get("kind"));List<Map<String,Object>> out=new ArrayList<>();
        if(kind.equals("nominal")) { for(Object c:vector(defs.get(number(type.get("id"),255)).get("constructors"),1024)) out.add(object(c));return out; }
        List<Map<String,Object>> children=typeChildren(type);Object anonymous=List.of("anonymous");
        switch(kind) {
            case "list":out.add(obj("name",builtinName("List","nil"),"fields",List.of()));out.add(obj("name",builtinName("List","cons"),"fields",List.of(obj("name",anonymous,"type",children.get(0)),obj("name",anonymous,"type",type))));break;
            case "option":out.add(obj("name",builtinName("Option","none"),"fields",List.of()));out.add(obj("name",builtinName("Option","some"),"fields",List.of(obj("name",anonymous,"type",children.get(0)))));break;
            case "product":out.add(obj("name",builtinName("Prod","mk"),"fields",List.of(obj("name",anonymous,"type",children.get(0)),obj("name",anonymous,"type",children.get(1)))));break;
            case "sum":case "except":String family=kind.equals("sum")?"Sum":"Except";String[] names=kind.equals("sum")?new String[]{"inl","inr"}:new String[]{"error","ok"};for(int i=0;i<2;i++) out.add(obj("name",builtinName(family,names[i]),"fields",List.of(obj("name",anonymous,"type",children.get(i)))));break;
            default:throw new IllegalArgumentException("Family encoding requires a logical family");
        }return out;
    }
    private static String rowRawLane(Row row,Map<Integer,Row> rows) {
        Set<Integer> seen=new HashSet<>();
        while(true) {
            dataRequire(seen.add(row.id),"No-progress alias schema cycle");
            if(row.kind==FrozenPlan.SCALAR) return row.lane;
            if(row.kind!=FrozenPlan.FAMILY) return null;
            boolean enums=true;for(Alternative a:row.alternatives) enums&=a.kind.equals("immediate");
            if(enums) return LANES.contains(row.closedIR)?row.closedIR:null;
            if(row.alternatives.length!=1||!row.alternatives[0].kind.equals("alias")) return null;
            Alternative a=row.alternatives[0];row=rows.get(a.fields[a.alias].plan);
        }
    }
    private static List<Integer> refs(Row row) {
        List<Integer> out=new ArrayList<>();for(int argument:row.arguments) out.add(argument);if(row.kind==FrozenPlan.ARRAY) out.add(row.element);
        for(Alternative a:row.alternatives) for(Binding f:a.fields) out.add(f.plan);return out;
    }
    private static Map<String,Object> reprRoot(int root,Map<Integer,Row> rows,Map<Integer,String> logicalKeys) {
        LinkedHashMap<Integer,Integer> ids=new LinkedHashMap<>();ArrayDeque<Integer> todo=new ArrayDeque<>();todo.push(root);
        while(!todo.isEmpty()) { int id=todo.pop();if(ids.containsKey(id)) continue;ids.put(id,ids.size());List<Integer> children=refs(rows.get(id));for(int i=children.size()-1;i>=0;i--) todo.push(children.get(i)); }
        List<Object> out=new ArrayList<>();
        for(int id:ids.keySet()) {
            Row row=rows.get(id);TreeMap<String,Object> encoding=new TreeMap<>(row.encoding);
            if(row.kind==FrozenPlan.ARRAY) encoding.put("element",Long.valueOf(ids.get(row.element)));
            if(row.kind==FrozenPlan.FAMILY) {
                List<Object> cs=new ArrayList<>();for(Object raw:vector(row.encoding.get("constructors"),1024)) {
                    TreeMap<String,Object> c=new TreeMap<>(object(raw));List<Object> fs=new ArrayList<>();
                    for(Object field:vector(c.get("fields"),64)) { TreeMap<String,Object> f=new TreeMap<>(object(field));f.put("plan",Long.valueOf(ids.get(number(f.get("plan"),8191))));fs.add(Map.copyOf(f)); }
                    c.put("fields",List.copyOf(fs));cs.add(Map.copyOf(c));
                }encoding.put("constructors",List.copyOf(cs));
            }
            List<Object> arguments=new ArrayList<>();for(int argument:row.arguments) arguments.add(Long.valueOf(ids.get(argument)));
            out.add(obj("logical",logicalKeys.get(id),"arguments",arguments,"closedIR",row.closedIR,"encoding",Map.copyOf(encoding)));
        }return obj("schema","lean-jvm-rooted-storage/1","target",obj("wordBits",64L,"byteOrder","little","storageAbi","node-pure-data/1"),"plans",out);
    }
    static Map<String,Object> describe(Object value) { return schema(value).metadata; }
    static Schema compile(Map<String,Object> logicalInput,Map<String,Object> normalizedInput) {
        long[] hashWork={0};
        Map<String,Object> g=object(snapshot(logicalInput,0,new int[3],false)),n=object(snapshot(normalizedInput,0,new int[3],false));
        Map<Integer,Map<String,Object>> defs=logical(g);Map<String,Object> canonical=canonicalLogical(defs,vector(g.get("roots"),1024));
        keys(n,"schema","logicalDigest","target","roots","plans");dataRequire("lean-jvm-typed-storage/1".equals(n.get("schema")),"Storage protocol version");
        hex(n.get("logicalDigest"));dataRequire(n.get("logicalDigest").equals(digest(canonical,hashWork)),"Logical digest mismatch");
        Map<String,Object> target=object(n.get("target"));keys(target,"wordBits","byteOrder","storageAbi");dataRequire(number(target.get("wordBits"),64)==64&&"little".equals(target.get("byteOrder"))&&"node-pure-data/1".equals(target.get("storageAbi")),"Unsupported storage cohort/target");
        Map<Integer,Map<String,Object>> rawRows=new HashMap<>();Map<Integer,Row> rows=new HashMap<>();Map<Integer,String> logicalKeys=new HashMap<>();Set<String> uniqueTypes=new HashSet<>();int edgeCount=0;
        for(Object raw:vector(n.get("plans"),8192)) {
            Map<String,Object> r=object(raw);keys(r,"id","type","closedIR","encoding");int id=number(r.get("id"),8191);dataRequire(rawRows.put(id,r)==null,"Duplicate plan row");
            Map<String,Object> t=object(r.get("type"));type(t,defs,0,new int[2]);String semantic=digest(canonicalLogical(defs,List.of(t)),hashWork);dataRequire(uniqueTypes.add(semantic),"Duplicate closed type plan");logicalKeys.put(id,semantic);
        }
        dataRequire(!rawRows.isEmpty(),"Missing normalized plans");
        for(int id:rawRows.keySet()) {
            Map<String,Object> r=rawRows.get(id),t=object(r.get("type")),enc=object(r.get("encoding"));String k=text(enc.get("kind")),closed=text(r.get("closedIR"));dataRequire(OBJECT_LANES.contains(closed)||LANES.contains(closed),"Closed IR lane");
            int kind=-1,element=-1;String lane=null,boxed=null;Alternative[] alternatives=new Alternative[0];String logicalKind=text(t.get("kind"));
            switch(k) {
                case "nat":kind=FrozenPlan.NAT;break;case "int":kind=FrozenPlan.INT;break;case "string":kind=FrozenPlan.STRING;break;case "unit":kind=FrozenPlan.UNIT;break;case "bytes":kind=FrozenPlan.BYTES;break;
                case "array":keys(enc,"kind","element");kind=FrozenPlan.ARRAY;element=number(enc.get("element"),8191);dataRequire(rawRows.containsKey(element)&&object(rawRows.get(element).get("type")).equals(t.get("element")),"Array element correspondence");edgeCount++;break;
                case "scalar":keys(enc,"kind","lane","boxed");kind=FrozenPlan.SCALAR;lane=text(enc.get("lane"));boxed=text(enc.get("boxed"));dataRequire(lane.equals(scalarLane(t)),"Logical scalar/lane mismatch");dataRequire(boxed.equals(lane.equals("float32")?"box32":Set.of("float","uint64","usize").contains(lane)?"box64":"small-immediate"),"Scalar boxing mismatch");dataRequire(closed.equals(lane),"Closed scalar lowering");break;
                case "family": {
                    keys(enc,"kind","constructors");kind=FrozenPlan.FAMILY;List<Map<String,Object>> expected=logicalConstructors(t,defs);List<?> supplied=vector(enc.get("constructors"),1024);dataRequire(supplied.size()==expected.size(),"Incomplete constructor alternatives");alternatives=new Alternative[supplied.size()];
                    for(int ci=0;ci<alternatives.length;ci++) {
                        Map<String,Object> c=object(supplied.get(ci)),rep=object(c.get("representation"));keys(c,"index","name","representation","fields");dataRequire(number(c.get("index"),1023)==ci&&c.get("name").equals(expected.get(ci).get("name")),"Constructor identity mismatch");
                        String rk=text(rep.get("kind"));int tag=-1,objects=0,usize=0,ssize=0,alias=-1;
                        if(rk.equals("node")) { keys(rep,"kind","tag","objects","usize","ssize");tag=number(rep.get("tag"),243);objects=number(rep.get("objects"),64);usize=number(rep.get("usize"),64);ssize=number(rep.get("ssize"),1024);dataRequire(tag==ci&&objects+usize*8L+ssize>0,"Allocated constructor tag/extent"); }
                        else if(rk.equals("immediate")) { keys(rep,"kind","tag");tag=number(rep.get("tag"),1023);dataRequire(tag==ci,"Immediate constructor tag"); }
                        else if(rk.equals("alias")) { keys(rep,"kind","field");alias=number(rep.get("field"),63);dataRequire(alternatives.length==1,"Alias family must have one constructor"); }
                        else throw new IllegalArgumentException("Unknown constructor representation");
                        List<?> fs=vector(c.get("fields"),64),efs=vector(expected.get(ci).get("fields"),64);dataRequire(fs.size()==efs.size(),"Logical field arity mismatch");Binding[] bindings=new Binding[fs.size()];boolean[] os=new boolean[objects],us=new boolean[usize],bs=new boolean[ssize];
                        for(int fi=0;fi<bindings.length;fi++) {
                            Map<String,Object> f=object(fs.get(fi)),loc=object(f.get("location"));keys(f,"index","plan","location");int child=number(f.get("plan"),8191);dataRequire(number(f.get("index"),63)==fi&&rawRows.containsKey(child)&&rawRows.get(child).get("type").equals(object(efs.get(fi)).get("type")),"Logical field/type correspondence");
                            String fk=text(loc.get("kind")),fl=null;int index=-1,offset=-1;
                            if(fk.equals("object")) { keys(loc,"kind","slot");index=number(loc.get("slot"),63);dataRequire(rk.equals("node")&&index<objects&&!os[index],"Object slot overlap/extent");os[index]=true; }
                            else if(fk.equals("usize")) { keys(loc,"kind","nativeIndex");index=number(loc.get("nativeIndex"),127);dataRequire(rk.equals("node")&&index>=objects&&index<objects+usize&&!us[index-objects],"USize slot overlap/extent");us[index-objects]=true;offset=(index-objects)*8;fl="usize"; }
                            else if(fk.equals("scalar")) { keys(loc,"kind","offset","lane");fl=text(loc.get("lane"));int width=laneWidth(fl);int nativeOffset=number(loc.get("offset"),1024);dataRequire(rk.equals("node")&&nativeOffset<=ssize-width,"Scalar slot extent");for(int bi=nativeOffset;bi<nativeOffset+width;bi++) { dataRequire(!bs[bi],"Scalar overlap");bs[bi]=true; }offset=usize*8+nativeOffset; }
                            else if(fk.equals("self")) { keys(loc,"kind");dataRequire(rk.equals("alias")&&fi==alias,"Alias selected field mismatch"); }
                            else if(fk.equals("unit")) { keys(loc,"kind");dataRequire("unit".equals(object(rawRows.get(child).get("type")).get("kind")),"Only logical Unit may be erased"); }
                            else throw new IllegalArgumentException("Unknown logical field location");
                            dataRequire(!rk.equals("immediate")||fk.equals("unit"),"Immediate constructor contains stored field");
                            dataRequire(!rk.equals("alias")||fi==alias||fk.equals("unit"),"Alias contains another stored field");
                            bindings[fi]=new Binding(child,index,offset,fk,fl);edgeCount++;
                        }
                        for(boolean covered:os) dataRequire(covered,"Uncovered object slot");for(boolean covered:us) dataRequire(covered,"Uncovered USize slot");for(boolean covered:bs) dataRequire(covered,"Unclassified scalar byte");
                        if(rk.equals("alias")) dataRequire(alias<bindings.length&&bindings[alias].kind.equals("self"),"Missing selected alias field");
                        alternatives[ci]=new Alternative(ci,tag,objects,usize,ssize,alias,rk,bindings);
                    }break;
                }
                default:throw new IllegalArgumentException("Unknown storage encoding");
            }
            if(Set.of("nat","int","string","unit","bytes").contains(k)) { keys(enc,"kind");dataRequire(logicalKind.equals(k),"Leaf kind correspondence"); }
            if(k.equals("array")) dataRequire(logicalKind.equals("array")&&closed.equals("object"),"Array lowering correspondence");
            if(k.equals("nat")||k.equals("int")) dataRequire(closed.equals("tobject"),"Integer lowering correspondence");
            if(k.equals("string")||k.equals("bytes")) dataRequire(closed.equals("object"),"Object leaf lowering correspondence");
            if(k.equals("unit")) dataRequire(closed.equals("tagged"),"Unit lowering correspondence");
            List<?> args="nominal".equals(t.get("kind"))?vector(defs.get(number(t.get("id"),255)).get("arguments"),64):typeChildren(t);
            int[] argumentPlans=new int[args.size()];
            for(int ai=0;ai<argumentPlans.length;ai++) {
                int found=-1;for(Map.Entry<Integer,Map<String,Object>> candidate:rawRows.entrySet())
                    if(candidate.getValue().get("type").equals(args.get(ai))) { found=candidate.getKey();break; }
                dataRequire(found>=0,"Missing closed argument plan");argumentPlans[ai]=found;
            }
            rows.put(id,new Row(id,kind,element,argumentPlans,closed,lane,boxed,t,enc,alternatives));
        }
        dataRequire(edgeCount<=4096,"Normalized plan edge bound");
        for(Row row:rows.values()) {
            String raw=rowRawLane(row,rows);for(Alternative a:row.alternatives) for(Binding b:a.fields) if(b.lane!=null) dataRequire(b.lane.equals(rowRawLane(rows.get(b.plan),rows)),"Logical field scalar lowering mismatch");
            if(row.kind==FrozenPlan.FAMILY) {
                boolean enums=true,alias=false,immediate=false;for(Alternative a:row.alternatives) { enums&=a.kind.equals("immediate");alias|=a.kind.equals("alias");immediate|=a.kind.equals("immediate"); }
                String expected=alias?rows.get(row.alternatives[0].fields[row.alternatives[0].alias].plan).closedIR:enums?(row.alternatives.length==1?"tagged":row.alternatives.length<256?"uint8":"uint16"):immediate?"tobject":"object";
                dataRequire(row.closedIR.equals(expected),"Family closed application lowering mismatch");
            }
        }
        List<?> roots=vector(n.get("roots"),1024),logicalRoots=vector(g.get("roots"),1024);dataRequire(roots.size()==logicalRoots.size(),"Root catalog correspondence");Set<Integer> reachable=new HashSet<>();ArrayDeque<Integer> todo=new ArrayDeque<>();
        for(int i=0;i<roots.size();i++) { int id=number(roots.get(i),8191);dataRequire(rows.containsKey(id)&&rows.get(id).type.equals(logicalRoots.get(i)),"Root type mismatch");todo.push(id); }
        while(!todo.isEmpty()) { int id=todo.pop();if(reachable.add(id)) todo.addAll(refs(rows.get(id))); }dataRequire(reachable.size()==rows.size(),"Unreachable normalized row");
        Map<Integer,String> representationKeys=new HashMap<>();for(int id:rows.keySet()) representationKeys.put(id,digest(reprRoot(id,rows,logicalKeys),hashWork));
        // Force the independent normalized encoded extent check before publication.
        digest(n,hashWork);
        Map<Integer,Integer> canonicalIds=canonicalIds(defs,vector(g.get("roots"),1024));List<Object> metadataRows=new ArrayList<>();
        for(Object raw:vector(n.get("plans"),8192)) {
            TreeMap<String,Object> row=new TreeMap<>(object(raw));row.put("type",rewrite(row.get("type"),canonicalIds));metadataRows.add(Map.copyOf(row));
        }
        TreeMap<String,Object> metadataNormalized=new TreeMap<>(n);metadataNormalized.put("plans",List.copyOf(metadataRows));
        return new Schema(canonical,Map.copyOf(metadataNormalized),rows,logicalKeys,representationKeys);
    }
    private static FrozenInput capability(Object value) {
        dataRequire(value!=null&&value.getClass()==FrozenInput.class,"Issued typed capability required");FrozenInput input=(FrozenInput)value;input.acquire();dataRequire(input.cert.plan.schema!=null,"Physical test proof is not logical authority");return input;
    }
    private static Schema schema(Object value) { dataRequire(value!=null&&value.getClass()==Schema.class,"Compiled schema required");return (Schema)value; }
    private static boolean compatible(FrozenPlan expected,FrozenPlan actual) {
        if(!(actual.key instanceof PlanKey)) return false;PlanKey a=(PlanKey)expected.key,b=(PlanKey)actual.key;
        return a.logical.equals(b.logical)&&a.representation.equals(b.representation)&&a.nodeClass==b.nodeClass&&a.helperClass==b.helperClass;
    }
    static FrozenInput freezeTyped(Object schema,int root,Object value,String lane) {
        FrozenPlan plan=schema(schema).plan(root);
        if(OBJECT_LANES.contains(lane)) return freeze(value,plan);
        dataRequire(lane.equals(plan.row.closedIR)&&lane.equals(plan.schema.rawLanes.get(plan.row.id)),"Raw result ABI/type mismatch");
        long bits;
        if(lane.equals("float")) { dataRequire(value!=null&&value.getClass()==Double.class,"Exact Float result carrier");bits=Double.doubleToRawLongBits((Double)value); }
        else if(lane.equals("float32")) { dataRequire(value!=null&&value.getClass()==Float.class,"Exact Float32 result carrier");bits=Integer.toUnsignedLong(Float.floatToRawIntBits((Float)value)); }
        else { dataRequire(value!=null&&value.getClass()==Long.class,"Exact raw scalar result carrier");bits=(Long)value; }
        return freeze(new RawBits(lane,bits),plan.raw(lane));
    }
    static FrozenInput readChild(Object value,int index) {
        FrozenInput input=capability(value);FrozenCert cert=input.cert;FrozenPlan p=cert.plan;Object storage=input.value;
        dataRequire(index>=0&&index<cert.children.length,"Logical child index");Object child;
        if(p.kind==FrozenPlan.ARRAY) child=((Node)storage).storageField(index);
        else {
            dataRequire(p.kind==FrozenPlan.FAMILY,"Value has no logical fields");Binding b=p.row.alternatives[cert.constructorIndex].fields[index];
            child=switch(b.kind) {
                case "object"->((Node)storage).storageField(b.index);
                case "scalar","usize"->new RawBits(b.lane,((Node)storage).storageBits(b.offset,laneWidth(b.lane)));
                case "self"->storage;case "unit"->0L;default->throw new AssertionError("Checked field binding");
            };
        }
        return published(child,cert.children[index]);
    }
    static int constructorIndex(Object value) { FrozenInput input=capability(value);dataRequire(input.cert.plan.kind==FrozenPlan.FAMILY,"Constructor requires family");return input.cert.constructorIndex; }
    static int size(Object value) {
        FrozenInput input=capability(value);String kind=text(input.cert.plan.row.type.get("kind"));dataRequire(Set.of("array","list","bytes").contains(kind),"Value has no sequence size");return input.cert.logicalLength;
    }
    static Object scalar(Object value) {
        FrozenInput input=capability(value);FrozenPlan p=input.cert.plan;String kind=text(p.row.type.get("kind"));Object storage=input.value;
        if(kind.equals("nat")||kind.equals("int")) return storage.getClass()==Long.class?BigInteger.valueOf((Long)storage):storage;
        if(kind.equals("string")) return storage;
        dataRequire(p.kind==FrozenPlan.SCALAR,"Logical scalar required");long bits=scalarBits(storage,p);
        if(kind.equals("bool")) return bits==1;
        if(kind.equals("char")) return Integer.valueOf((int)bits);
        if(kind.equals("float")) return p.row.lane.equals("float32")?Float.valueOf(Float.intBitsToFloat((int)bits)):(Object)Double.valueOf(Double.longBitsToDouble(bits));
        BigInteger unsigned=BigInteger.valueOf(bits&Long.MAX_VALUE);if(bits<0) unsigned=unsigned.setBit(63);
        int width=laneWidth(p.row.lane)*8;if(Boolean.TRUE.equals(p.row.type.get("signed"))&&unsigned.testBit(width-1)) unsigned=unsigned.subtract(BigInteger.ONE.shiftLeft(width));return unsigned;
    }
    static int byteAt(Object value,int index) {
        FrozenInput input=capability(value);dataRequire(input.cert.plan.kind==FrozenPlan.BYTES&&index>=0&&index<input.cert.live,"Byte index/type");return ((Node)input.value).storageByte(index);
    }
    static byte[] copyByteArray(Object value) {
        FrozenInput input=capability(value);dataRequire(input.cert.plan.kind==FrozenPlan.BYTES,"ByteArray capability required");byte[] out=new byte[input.cert.live];
        for(int i=0;i<out.length;i++) { if((i&1023)==0) freezePoll();out[i]=(byte)((Node)input.value).storageByte(i); }return out;
    }
    private static final class CanonicalBytes {
        static final Schema SCHEMA=compile(obj("schema","lean-jvm-type-graph/3","roots",List.of(obj("kind","bytes")),"definitions",List.of()),
            obj("schema","lean-jvm-typed-storage/1","logicalDigest",digest(obj("schema","lean-jvm-type-graph/3","roots",List.of(obj("kind","bytes")),"definitions",List.of())),
                "target",obj("wordBits",64L,"byteOrder","little","storageAbi","node-pure-data/1"),"roots",List.of(0L),
                "plans",List.of(obj("id",0L,"type",obj("kind","bytes"),"closedIR","object","encoding",obj("kind","bytes")))));
    }
    static FrozenInput copyBytes(byte[] source) {
        dataRequire(source!=null&&source.length<=MAX_DATA_BUFFER_BYTES,"ByteArray input bound");freezePoll();return freeze(allocated(Node.storageBytesOwned(source.clone())),CanonicalBytes.SCHEMA.plan(0));
    }
    static final class FrozenArgument {
        final FrozenInput input;final String lane;
        FrozenArgument(FrozenInput input,String lane) { this.input=input;this.lane=lane; }
    }
    /** Separate from construction arguments: raw reply lanes must never become
     * object roots through constructDataArguments. Only this class issues it. */
    static final class FrozenReply {
        final Object value;final String lane;
        private FrozenReply(Object value,String lane) { this.value=value;this.lane=lane; }
    }
    static FrozenReply prepareReply(Object schema,int root,Object value,String lane) {
        FrozenPlan expected=schema(schema).plan(root);FrozenInput input=capability(value);
        dataRequire(compatible(expected,input.cert.plan),"Reply type/layout/cohort mismatch");
        if(OBJECT_LANES.contains(lane)) {
            FrozenArgument argument=prepareArgument(schema,root,value,lane);
            return new FrozenReply(argument.input.acquire(),lane);
        }
        dataRequire(lane.equals(expected.row.closedIR)&&lane.equals(expected.schema.rawLanes.get(expected.row.id)),
                    "Raw reply ABI/type mismatch");
        long bits=scalarBits(input.value,input.cert.plan);
        Object raw=lane.equals("float")?Double.valueOf(Double.longBitsToDouble(bits))
            :lane.equals("float32")?(Object)Float.valueOf(Float.intBitsToFloat((int)bits)):Long.valueOf(bits);
        // Apply the same raw scalar validation as guest exports before issuing
        // the reply token; never authorize arbitrary host scalar carriers.
        freezeTyped(schema,root,raw,lane);
        if((lane.equals("uint64")||lane.equals("usize"))&&bits<0)
            raw=BigInteger.valueOf(bits&Long.MAX_VALUE).setBit(63);
        return new FrozenReply(raw,lane);
    }
    private static Object canonicalScalar(FrozenPlan plan,Object storage) {
        String lane=plan.schema.rawLanes.get(plan.row.id);dataRequire(lane!=null,"Raw-to-object adaptation requires scalar type");
        long bits=scalarBits(storage,plan.raw(lane));FrozenPlan terminal=plan;
        while(terminal.kind==FrozenPlan.FAMILY&&terminal.row.alternatives[0].kind.equals("alias")) {
            Alternative a=terminal.row.alternatives[0];terminal=terminal.child(a.fields[a.alias].plan);
        }
        if(terminal.kind==FrozenPlan.FAMILY||terminal.row.boxed.equals("small-immediate")) return Long.valueOf(bits);
        Node box=allocated(Node.storageNew(0,0,0,laneWidth(lane),0));box.storageInitializeBits(0,laneWidth(lane),bits);return box;
    }
    static FrozenArgument prepareArgument(Object schema,int root,Object value,String lane) {
        dataRequire(OBJECT_LANES.contains(lane),"Only owned boxed arguments are supported");FrozenPlan expected=schema(schema).plan(root);FrozenInput input=capability(value);
        dataRequire(compatible(expected,input.cert.plan),"Argument type/layout/cohort mismatch");
        FrozenCert proof=input.cert;
        dataRequire(proof.occurrences<=MAX_DATA_OCCURRENCES&&proof.depth<=1024&&proof.stringUnits<=MAX_DATA_STRING_UNITS
                &&proof.integerCost<=MAX_DATA_INTEGER_BITS&&proof.capacityCost<=MAX_DATA_OCCURRENCES&&proof.payloadCost<=MAX_DATA_BUFFER_BYTES,
                "Argument cached proof quota exceeded");
        if(!input.cert.plan.role.equals("object")) input=freeze(canonicalScalar(expected,input.value),expected);
        dataRequire(input.cert.plan.key.equals(expected.key),"Canonical object argument role required");return new FrozenArgument(input,lane);
    }
    private static final class Build {
        final FrozenPlan plan;final Alternative alternative;final Object[] children;final Object leaf;final RawBits raw;final byte[] bytes;
        final long occurrences,strings,bits;final int depth;boolean needed;Object storage;
        Build(FrozenPlan plan,Alternative alternative,Object[] children,Object leaf,RawBits raw,byte[] bytes) {
            this.plan=plan;this.alternative=alternative;this.children=children;this.leaf=leaf;this.raw=raw;this.bytes=bytes;
            long count=1,units=leaf instanceof String?((String)leaf).length():0,numeric=0;int height=1;
            if(leaf instanceof Long) numeric=64;else if(leaf instanceof BigInteger) numeric=((BigInteger)leaf).abs().bitLength();
            if(raw!=null&&plan.kind==FrozenPlan.SCALAR&&Set.of("machine-int","word","char").contains(plan.row.type.get("kind"))) numeric=64;
            for(Object child:children) {
                if(child instanceof Build) { Build b=(Build)child;count=Math.min(MAX_DATA_OCCURRENCES+1L,count+b.occurrences);units=Math.min(MAX_DATA_STRING_UNITS+1L,units+b.strings);numeric=Math.min(MAX_DATA_INTEGER_BITS+1L,numeric+b.bits);height=Math.max(height,1+b.depth); }
                else { FrozenCert c=((FrozenInput)child).cert;count=Math.min(MAX_DATA_OCCURRENCES+1L,count+c.occurrences);units=Math.min(MAX_DATA_STRING_UNITS+1L,units+c.stringUnits);numeric=Math.min(MAX_DATA_INTEGER_BITS+1L,numeric+c.integerCost);height=Math.max(height,1+c.depth); }
            }
            dataRequire(count<=MAX_DATA_OCCURRENCES&&units<=MAX_DATA_STRING_UNITS&&numeric<=MAX_DATA_INTEGER_BITS&&height<=1024,"Build logical aggregate budget");occurrences=count;strings=units;bits=numeric;depth=height;
        }
    }
    private static Object token(Object raw,List<Build> prior,FrozenPlan expected) {
        Map<String,Object> t=object(raw);Object value;
        if(t.containsKey("ref")) { keys(t,"ref");int index=number(t.get("ref"),100_000);dataRequire(index<prior.size(),"Build references must point earlier");value=prior.get(index); }
        else { keys(t,"cap");value=capability(t.get("cap")); }
        FrozenPlan actual=value instanceof Build?((Build)value).plan:((FrozenInput)value).cert.plan;
        dataRequire(compatible(expected,actual),"Build child type/layout/cohort mismatch");return value;
    }
    private static FrozenPlan valuePlan(Object value) { return value instanceof Build?((Build)value).plan:((FrozenInput)value).cert.plan; }
    private static RawBits rawValue(Object value) {
        if(value instanceof Build) { RawBits raw=((Build)value).raw;dataRequire(raw!=null,"Child lacks raw scalar representation");return raw; }
        FrozenInput input=(FrozenInput)value;String lane=input.cert.plan.schema.rawLanes.get(input.cert.plan.row.id);dataRequire(lane!=null,"Child lacks scalar representation");return new RawBits(lane,scalarBits(input.value,input.cert.plan));
    }
    private static Object storageValue(Object value,IdentityHashMap<FrozenInput,Object> adapted) {
        if(value instanceof Build) { Object storage=((Build)value).storage;dataRequire(storage!=null,"Unprepared object child");return storage; }
        FrozenInput input=(FrozenInput)value;if(input.cert.plan.role.equals("object")) return input.value;
        Object prior=adapted.get(input);if(prior!=null) return prior;
        Object out=canonicalScalar(input.cert.plan,input.value);adapted.put(input,out);return out;
    }
    static FrozenInput construct(Object schemaValue,int root,Object tapeValue) {
        Schema schema=schema(schemaValue);FrozenPlan expected=schema.plan(root);Map<String,Object> tape=object(snapshot(tapeValue,0,new int[3],true));keys(tape,"schema","records","root");dataRequire("lean-jvm-value-build/1".equals(tape.get("schema")),"Build protocol version");
        List<Build> builds=new ArrayList<>();
        for(Object record:vector(tape.get("records"),MAX_DATA_OCCURRENCES)) {
            Map<String,Object> r=object(record);FrozenPlan p=schema.plan(number(r.get("plan"),8191));String kind=text(r.get("kind"));Alternative a=null;Object[] children=new Object[0];Object leaf=null;RawBits raw=null;byte[] bytes=null;
            if(kind.equals("leaf")) {
                keys(r,"kind","plan","value");leaf=r.get("value");
                if(p.kind==FrozenPlan.STRING) { dataRequire(leaf.getClass()==String.class,"Build String carrier");unicode((String)leaf,65536); }
                else { dataRequire((p.kind==FrozenPlan.NAT||p.kind==FrozenPlan.INT)&&(leaf.getClass()==Long.class||leaf.getClass()==BigInteger.class),"Build integer carrier");BigInteger n=leaf instanceof Long?BigInteger.valueOf((Long)leaf):(BigInteger)leaf;dataRequire(n.bitLength()<=4096&&n.abs().bitLength()<=4096&&(p.kind==FrozenPlan.INT||n.signum()>=0),"Build integer range");if(n.bitLength()<=63) leaf=Long.valueOf(n.longValue()); }
            } else if(kind.equals("unit")) { keys(r,"kind","plan");dataRequire(p.kind==FrozenPlan.UNIT,"Build Unit kind");leaf=0L; }
            else if(kind.equals("scalar")) {
                keys(r,"kind","plan","lane","bits");String lane=text(r.get("lane"));dataRequire(p.kind==FrozenPlan.SCALAR&&lane.equals(p.row.lane)&&r.get("bits").getClass()==Long.class,"Build scalar kind/lane");raw=new RawBits(lane,(Long)r.get("bits"));scalarBits(raw,p.raw(lane));scalarDomain(p,raw.bits);
            } else if(kind.equals("bytes")) { keys(r,"kind","plan","bytes");dataRequire(p.kind==FrozenPlan.BYTES&&r.get("bytes").getClass()==byte[].class,"Build bytes kind");bytes=(byte[])r.get("bytes"); }
            else if(kind.equals("array")) {
                keys(r,"kind","plan","elements");dataRequire(p.kind==FrozenPlan.ARRAY,"Build Array kind");List<?> elements=vector(r.get("elements"),MAX_DATA_OCCURRENCES);children=new Object[elements.size()];for(int i=0;i<children.length;i++) children[i]=token(elements.get(i),builds,p.child(p.row.element));
            } else if(kind.equals("constructor")) {
                keys(r,"kind","plan","constructor","fields");dataRequire(p.kind==FrozenPlan.FAMILY,"Build family kind");int ci=number(r.get("constructor"),1023);dataRequire(ci<p.row.alternatives.length,"Build constructor membership");a=p.row.alternatives[ci];List<?> fields=vector(r.get("fields"),64);dataRequire(fields.size()==a.fields.length,"Build field arity");children=new Object[fields.size()];
                for(int i=0;i<children.length;i++) {
                    Binding b=a.fields[i];children[i]=token(fields.get(i),builds,p.child(b.plan));
                    if(b.lane!=null) { RawBits bits=rawValue(children[i]);dataRequire(bits.lane.equals(b.lane),"Build field scalar lowering"); }
                }
                String lane=schema.rawLanes.get(p.row.id);
                if(lane!=null) raw=a.kind.equals("alias")?rawValue(children[a.alias]):new RawBits(lane,ci);
            } else throw new IllegalArgumentException("Unknown build record kind");
            builds.add(new Build(p,a,children,leaf,raw,bytes));
        }
        Object rootValue=token(tape.get("root"),builds,expected);
        // Determine reachability/object uses backwards before any Node allocation.
        IdentityHashMap<Object,Boolean> reachable=new IdentityHashMap<>();ArrayDeque<Object> todo=new ArrayDeque<>();todo.push(rootValue);
        while(!todo.isEmpty()) { Object value=todo.pop();if(reachable.put(value,Boolean.TRUE)!=null) continue;if(value instanceof Build) for(Object child:((Build)value).children) todo.push(child); }
        for(Build b:builds) dataRequire(reachable.containsKey(b),"Unreachable build record");
        if(rootValue instanceof Build) ((Build)rootValue).needed=true;
        IdentityHashMap<FrozenInput,Boolean> adaptedUses=new IdentityHashMap<>();
        if(rootValue instanceof FrozenInput&&!((FrozenInput)rootValue).cert.plan.role.equals("object")) adaptedUses.put((FrozenInput)rootValue,Boolean.TRUE);
        for(int i=builds.size()-1;i>=0;i--) {
            Build b=builds.get(i);
            for(int ci=0;ci<b.children.length;ci++) {
                boolean objectUse=b.plan.kind==FrozenPlan.ARRAY||b.alternative!=null&&(b.alternative.fields[ci].kind.equals("object")||b.alternative.kind.equals("alias")&&ci==b.alternative.alias&&b.needed);
                if(objectUse) { Object child=b.children[ci];if(child instanceof Build) ((Build)child).needed=true;else if(!((FrozenInput)child).cert.plan.role.equals("object")) adaptedUses.put((FrozenInput)child,Boolean.TRUE); }
            }
        }
        long slots=0,payload=0;IdentityHashMap<FrozenCert,Boolean> cached=new IdentityHashMap<>();
        for(Object value:reachable.keySet()) {
            if(value instanceof FrozenInput) { FrozenCert c=((FrozenInput)value).cert;if(cached.put(c,Boolean.TRUE)==null) { slots+=c.capacityCost;payload+=c.payloadCost; } }
            else {
                Build b=(Build)value;if(b.bytes!=null) payload+=b.bytes.length;
                if(b.plan.kind==FrozenPlan.ARRAY) slots+=b.children.length;
                if(b.alternative!=null&&b.alternative.kind.equals("node")) { slots+=b.alternative.objects;payload+=b.alternative.scalarBytes(); }
                if(b.plan.kind==FrozenPlan.SCALAR&&b.needed&&!b.plan.row.boxed.equals("small-immediate")) payload+=laneWidth(b.plan.row.lane);
            }
        }
        for(FrozenInput value:adaptedUses.keySet()) payload+=8; // conservative shallow-box bound
        dataRequire(slots<=MAX_DATA_OCCURRENCES&&payload<=MAX_DATA_BUFFER_BYTES,"Build physical capacity/payload budget");
        // Root-only cap tape still checks all logical quotas without a traversal.
        if(rootValue instanceof FrozenInput) {
            FrozenCert c=((FrozenInput)rootValue).cert;dataRequire(c.occurrences<=MAX_DATA_OCCURRENCES&&c.depth<=1024&&c.stringUnits<=MAX_DATA_STRING_UNITS&&c.integerCost<=MAX_DATA_INTEGER_BITS,"Build root capability budget");
        }
        freezePoll();IdentityHashMap<FrozenInput,Object> adapted=new IdentityHashMap<>();
        for(Build b:builds) {
            freezePoll();FrozenPlan p=b.plan;
            if(b.leaf!=null) b.storage=b.leaf;
            else if(b.bytes!=null) b.storage=allocated(Node.storageBytesOwned(b.bytes));
            else if(p.kind==FrozenPlan.SCALAR) { if(b.needed) b.storage=canonicalScalar(p,b.raw); }
            else if(p.kind==FrozenPlan.ARRAY) {
                Node node=allocated(Node.storageNew(1,246,b.children.length,0,b.children.length));for(int i=0;i<b.children.length;i++) node.storageInitializeField(i,storageValue(b.children[i],adapted));b.storage=node;
            } else {
                Alternative a=b.alternative;
                if(a.kind.equals("immediate")) b.storage=Long.valueOf(a.tag);
                else if(a.kind.equals("alias")) { if(b.needed) b.storage=storageValue(b.children[a.alias],adapted); }
                else {
                    Node node=allocated(Node.storageNew(0,a.tag,a.objects,a.scalarBytes(),0));
                    for(int i=0;i<a.fields.length;i++) { Binding f=a.fields[i];if(f.kind.equals("object")) node.storageInitializeField(f.index,storageValue(b.children[i],adapted));else if(f.lane!=null) node.storageInitializeBits(f.offset,laneWidth(f.lane),rawValue(b.children[i]).bits); }
                    b.storage=node;
                }
            }
        }
        if(rootValue instanceof FrozenInput&&((FrozenInput)rootValue).cert.plan.key.equals(expected.key)) return (FrozenInput)rootValue;
        return freeze(storageValue(rootValue,adapted),expected);
    }
}
