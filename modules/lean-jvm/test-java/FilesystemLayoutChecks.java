package ansatz.lean.jvm.internal.exec;

import ansatz.lean.jvm.internal.exec.Interpreter.Node;
import java.util.ArrayList;
import java.util.List;

/** Fixed native-fixture facts; not a producer or replacement projection receipt. */
public final class FilesystemLayoutChecks {
    private static int checks;
    private static void check(boolean condition) {
        checks++; if (!condition) throw new AssertionError("Filesystem layout check " + checks);
    }
    private static final class Allocations implements FilesystemLayouts.Allocator {
        final List<Node> nodes = new ArrayList<>();
        public Node allocate(int tag, int fields, int bytes) {
            Node value = new Node(tag, fields, bytes); nodes.add(value); return value;
        }
    }
    private static long raw(Node value, int offset, int bytes) {
        long n = 0; for (int i = 0; i < bytes; i++) n |= (value.scalars[offset+i] & 255L) << (8*i); return n;
    }
    private static void shape(Node n, int tag, int fields, int bytes) {
        check(n.tag == tag && n.rc == 1 && n.fields.length == fields && n.scalars.length == bytes);
    }
    private static void refused(Runnable task) {
        try { task.run(); throw new AssertionError("Invalid layout input accepted"); }
        catch (IllegalArgumentException expected) { checks++; }
    }
    private static final String[] KINDS = {"alreadyExists","otherError","resourceBusy","resourceVanished",
        "unsupportedOperation","hardwareFault","unsatisfiedConstraints","illegalOperation","protocolError",
        "timeExpired","interrupted","noFileOrDirectory","invalidArgument","permissionDenied","resourceExhausted",
        "inappropriateType","noSuchThing","unexpectedEof","userError"};
    private static boolean filename(int tag) { return tag == 0 || tag >= 10 && tag <= 16; }
    private static boolean optional(int tag) { return tag == 0 || tag >= 12 && tag <= 16; }
    public static void main(String[] arguments) throws Exception {
        check(arguments.length == 0);
        byte[] capture;
        try (var input = FilesystemLayoutChecks.class.getResourceAsStream(
                "/META-INF/ansatz-lean-jvm/filesystem-layouts.jsonl")) {
            if (input == null) throw new AssertionError("Packaged layout witness missing");
            capture = input.readNBytes(131073);
        }
        FilesystemLayouts codec = FilesystemLayouts.authenticate(capture);
        capture[0] ^= 1;
        refused(() -> FilesystemLayouts.authenticate(capture));
        refused(() -> FilesystemLayouts.authenticate(new byte[0]));
        refused(() -> FilesystemLayouts.authenticate(null));
        // Mutation of caller bytes cannot revoke or change an issued immutable codec.
        Allocations metadata = new Allocations();
        for (int kind = 0; kind < 4; kind++) {
            Node value = codec.metadata(metadata, Long.MIN_VALUE, 0, Long.MAX_VALUE, 999999999,
                                       Long.MIN_VALUE, -1L, kind);
            shape(value,0,2,17); shape((Node)value.fields[0],0,1,4); shape((Node)value.fields[1],0,1,4);
            check(value.fields[0] != value.fields[1]);
            check(((Node)value.fields[0]).fields[0].equals(Long.MIN_VALUE));
            check(((Node)value.fields[1]).fields[0].equals(Long.MAX_VALUE));
            check(raw((Node)value.fields[0],0,4) == 0);
            check(raw((Node)value.fields[1],0,4) == 999999999);
            check(raw(value,0,8) == Long.MIN_VALUE && raw(value,8,8) == -1L);
            check(raw(value,16,1) == kind);
        }
        check(metadata.nodes.size() == 12);
        for (int tag = 0; tag < KINDS.length; tag++) {
            for (long code : tag >= 17 ? new long[]{0} : new long[]{0,1,0x80000000L,0xffffffffL}) {
                for (String path : optional(tag) ? new String[]{null,"","λ\u0000😀"}
                        : filename(tag) ? new String[]{"","file"} : new String[]{null}) {
                    Allocations allocations = new Allocations();
                    String message = tag == 17 ? null : "details λ\u0000😀";
                    Object payload = codec.errorPayload(allocations,KINDS[tag],path,code,message);
                    if (tag == 17) { check(payload.equals(17L)); check(allocations.nodes.isEmpty()); }
                    else {
                        Node value = (Node)payload;
                        shape(value,tag,filename(tag)?2:1,tag==18?0:4);
                        check(value.fields[filename(tag)?1:0].equals(message));
                        if (tag != 18) check(raw(value,0,4) == code);
                        if (filename(tag)) {
                            Object name=value.fields[0];
                            if (optional(tag)) {
                                if(path==null) check(name.equals(0L));
                                else { shape((Node)name,1,1,0); check(((Node)name).fields[0].equals(path)); }
                            } else check(name.equals(path));
                        }
                        check(allocations.nodes.size() == (optional(tag)&&path!=null?2:1));
                    }
                    Allocations envelope = new Allocations();
                    Node failure = codec.ioFailure(envelope,KINDS[tag],path,code,message);
                    shape(failure,1,1,0); check(failure.fields[0] != null);
                    check(envelope.nodes.size() == allocations.nodes.size()+1);
                }
            }
        }
        Allocations envelopes = new Allocations();
        Node owned = new Node(0,0,0);
        Node ok = codec.ioSuccess(envelopes,owned); shape(ok,0,1,0); check(ok.fields[0] == owned && owned.rc==1);
        check(codec.ioSuccess(envelopes,0L).fields[0].equals(0L));
        check(codec.ioSuccess(envelopes,"λ😀\u0000").fields[0].equals("λ😀\u0000"));
        String longLine = "x".repeat(65537);
        check(codec.ioSuccess(envelopes,longLine).fields[0] == longLine);
        // The independently declared diagnostic/path bound remains unchanged.
        Allocations rejected = new Allocations();
        refused(() -> codec.metadata(rejected,0,-1,0,0,0,0,0));
        refused(() -> codec.metadata(rejected,0,0,0,1000000000,0,0,0));
        refused(() -> codec.metadata(rejected,0,0,0,0,0,0,-1));
        refused(() -> codec.metadata(rejected,0,0,0,0,0,0,4));
        refused(() -> codec.errorPayload(rejected,"unknown",null,0,"x"));
        refused(() -> codec.errorPayload(rejected,null,null,0,"x"));
        refused(() -> codec.ioFailure(rejected,"otherError",null,-1,"x"));
        refused(() -> codec.ioFailure(rejected,"otherError",null,0x100000000L,"x"));
        refused(() -> codec.ioFailure(rejected,"noFileOrDirectory",null,2,"x"));
        refused(() -> codec.ioFailure(rejected,"otherError","path",2,"x"));
        refused(() -> codec.ioFailure(rejected,"unexpectedEof",null,0,"x"));
        refused(() -> codec.ioFailure(rejected,"userError",null,1,"x"));
        refused(() -> codec.ioFailure(rejected,"userError",null,0,null));
        refused(() -> codec.ioFailure(rejected,"permissionDenied","\ud800",13,"x"));
        refused(() -> codec.ioFailure(rejected,"permissionDenied","path",13,"\udc00"));
        refused(() -> codec.ioFailure(rejected,"userError",null,0,"x".repeat(65537)));
        refused(() -> codec.ioSuccess(rejected,"\ud800"));
        refused(() -> codec.ioSuccess(rejected,"\udc00"));
        String oversizedInternal = "x".repeat(16 * 1024 * 1024 + 1);
        refused(() -> codec.ioSuccess(rejected,oversizedInternal));
        refused(() -> codec.ioSuccess(rejected,new Object()));
        refused(() -> codec.ioSuccess(rejected,null));
        check(rejected.nodes.isEmpty());
        check(FilesystemLayouts.class.getDeclaredConstructors().length == 1
            && java.lang.reflect.Modifier.isPrivate(FilesystemLayouts.class.getDeclaredConstructors()[0].getModifiers()));
        check(java.lang.reflect.Modifier.isFinal(FilesystemLayouts.class.getModifiers()));
        System.out.println("FILESYSTEM_LAYOUT_CHECKS " + checks);
    }
}
