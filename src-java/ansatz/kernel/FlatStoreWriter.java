// Ansatz kernel — Writer for FlatStore mmap'd format.

package ansatz.kernel;

import java.io.*;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

/**
 * Converts expression/declaration data into the FlatStore mmap'd format.
 *
 * <p>Usage:
 * <pre>
 *   FlatStoreWriter.convert(outDir, exprStore, names, levels, declProvider, declOrder);
 * </pre>
 *
 * <p>Reads from an ExprStore (variable-length binary records) and writes:
 * <ul>
 *   <li>{@code exprs.arena} — fixed 32-byte records
 *   <li>{@code exprs.side} — overflow data (CONST levels, big LIT_NAT, LIT_STR)
 *   <li>{@code decls.idx} — open-addressing hash table
 *   <li>{@code decls.data} — variable-length declaration records
 *   <li>{@code names.data} — serialized Name array
 *   <li>{@code levels.data} — serialized Level array
 *   <li>{@code order.data} — declaration order
 * </ul>
 */
public final class FlatStoreWriter {

    private FlatStoreWriter() {}

    /**
     * Interface for looking up declarations by name.
     * Implemented by the Clojure layer to bridge PSS/LMDB storage.
     */
    public interface DeclProvider {
        ConstantInfo lookup(Name name);
    }

    /**
     * Convert an ExprStore + declarations into FlatStore format.
     *
     * @param outDir      output directory (created if missing)
     * @param exprStore   expression store with all expressions
     * @param names       name table (indexed by ID)
     * @param levels      level table (indexed by ID)
     * @param declProvider provides ConstantInfo by Name
     * @param declOrder   ordered declaration names (as strings)
     * @param nameIndex   maps Name → integer ID (for writing name references)
     */
    public static void convert(Path outDir,
                                ExprStore exprStore,
                                ArrayList<?> names,
                                ArrayList<?> levels,
                                DeclProvider declProvider,
                                String[] declOrder,
                                Map<Object, Integer> nameIndex) throws IOException {
        Files.createDirectories(outDir);

        System.out.println("[FlatStoreWriter] Starting conversion to " + outDir);
        long t0 = System.currentTimeMillis();

        writeNames(outDir.resolve("names.data"), names);
        System.out.println("[FlatStoreWriter] names.data written (" + names.size() + " names) in " +
            (System.currentTimeMillis() - t0) + "ms");

        long t1 = System.currentTimeMillis();
        writeLevels(outDir.resolve("levels.data"), levels, nameIndex);
        System.out.println("[FlatStoreWriter] levels.data written (" + levels.size() + " levels) in " +
            (System.currentTimeMillis() - t1) + "ms");

        long t2 = System.currentTimeMillis();
        writeExprs(outDir, exprStore);
        System.out.println("[FlatStoreWriter] exprs.arena+side written (" + exprStore.maxId() + " exprs) in " +
            (System.currentTimeMillis() - t2) + "ms");

        long t3 = System.currentTimeMillis();
        writeDecls(outDir, declProvider, declOrder, names, nameIndex);
        System.out.println("[FlatStoreWriter] decls.idx+data written (" + declOrder.length + " decls) in " +
            (System.currentTimeMillis() - t3) + "ms");

        long t4 = System.currentTimeMillis();
        writeDeclOrder(outDir.resolve("order.data"), declOrder);
        System.out.println("[FlatStoreWriter] order.data written in " +
            (System.currentTimeMillis() - t4) + "ms");

        System.out.println("[FlatStoreWriter] Total conversion: " +
            (System.currentTimeMillis() - t0) + "ms");
    }

    // ================================================================
    // Names
    // ================================================================

    private static void writeNames(Path path, ArrayList<?> names) throws IOException {
        // Estimate size: 4 (count) + ~20 bytes avg per name
        ByteBuffer bb = ByteBuffer.allocate(4 + names.size() * 30);
        bb.putInt(names.size());

        // Build prefix ID lookup: we need to map Name → index
        // Names are stored in order, so prefix must have a lower index
        IdentityHashMap<Object, Integer> nameToId = new IdentityHashMap<>(names.size());
        for (int i = 0; i < names.size(); i++) {
            nameToId.put(names.get(i), i);
        }

        for (int i = 0; i < names.size(); i++) {
            Name n = (Name) names.get(i);
            // Ensure capacity
            if (bb.remaining() < 100) {
                bb = grow(bb);
            }

            if (n == null) {
                // Sparse entry — write ANONYMOUS as placeholder
                bb.put(Name.ANONYMOUS);
                continue;
            }

            bb.put(n.tag);
            switch (n.tag) {
                case Name.ANONYMOUS:
                    break;
                case Name.STR: {
                    Integer prefixId = nameToId.get(n.prefix);
                    bb.putInt(prefixId != null ? prefixId : -1);
                    byte[] strBytes = n.str.getBytes(StandardCharsets.UTF_8);
                    bb.putShort((short) strBytes.length);
                    if (bb.remaining() < strBytes.length) {
                        bb = grow(bb, strBytes.length);
                    }
                    bb.put(strBytes);
                    break;
                }
                case Name.NUM: {
                    Integer prefixId = nameToId.get(n.prefix);
                    bb.putInt(prefixId != null ? prefixId : -1);
                    bb.putLong(n.num);
                    break;
                }
            }
        }

        bb.flip();
        Files.write(path, Arrays.copyOf(bb.array(), bb.limit()));
    }

    // ================================================================
    // Levels
    // ================================================================

    private static void writeLevels(Path path, ArrayList<?> levels,
                                     Map<Object, Integer> nameIndex) throws IOException {
        // Write levels in original order. The reader handles forward references.
        // Build level → id mapping (must use equals, not identity — Level isn't interned)
        HashMap<Object, Integer> levelToId = new HashMap<>(levels.size());
        for (int i = 0; i < levels.size(); i++) {
            Object l = levels.get(i);
            if (l != null) levelToId.put(l, i);
        }

        int n = levels.size();
        ByteBuffer bb = ByteBuffer.allocate(4 + n * 12);
        bb.putInt(n);

        for (int i = 0; i < n; i++) {
            Level l = (Level) levels.get(i);
            if (bb.remaining() < 20) {
                bb = grow(bb);
            }

            if (l == null) {
                bb.put(Level.ZERO);
                continue;
            }

            bb.put(l.tag);
            switch (l.tag) {
                case Level.ZERO:
                    break;
                case Level.SUCC: {
                    Integer childId = levelToId.get(l.o0);
                    bb.putInt(childId != null ? childId : 0);
                    break;
                }
                case Level.MAX:
                case Level.IMAX: {
                    Integer lhsId = levelToId.get(l.o0);
                    Integer rhsId = levelToId.get(l.o1);
                    bb.putInt(lhsId != null ? lhsId : 0);
                    bb.putInt(rhsId != null ? rhsId : 0);
                    break;
                }
                case Level.PARAM: {
                    Integer nameId = nameIndex != null ? nameIndex.get(l.o0) : null;
                    bb.putInt(nameId != null ? nameId : -1);
                    break;
                }
            }
        }

        bb.flip();
        Files.write(path, Arrays.copyOf(bb.array(), bb.limit()));
    }

    // ================================================================
    // Expressions
    // ================================================================

    private static void writeExprs(Path outDir, ExprStore exprStore) throws IOException {
        int count = exprStore.maxId();

        // Use streaming I/O for arena (can be multi-GB for Mathlib)
        try (BufferedOutputStream arenaOut = new BufferedOutputStream(
                new FileOutputStream(outDir.resolve("exprs.arena").toFile()), 1 << 20);
             BufferedOutputStream sideOut = new BufferedOutputStream(
                new FileOutputStream(outDir.resolve("exprs.side").toFile()), 1 << 20)) {

            // Header: magic(4) + reserved(4) + count(4) + reserved(4) = 16 bytes
            byte[] header = new byte[FlatStore.ARENA_HEADER];
            header[0] = 'C'; header[1] = 'I'; header[2] = 'C'; header[3] = '1';
            putInt(header, 8, count);
            arenaOut.write(header);

            byte[] rec = new byte[FlatStore.RECORD_SIZE];
            long sidePos = 0;

            for (int id = 0; id < count; id++) {
                byte[] raw;
                try {
                    raw = exprStore.readRaw(id);
                } catch (IllegalArgumentException e) {
                    // Sparse ID — write an empty record
                    Arrays.fill(rec, (byte) 0xFF);
                    arenaOut.write(rec);
                    continue;
                }

                Arrays.fill(rec, (byte) 0);
                byte tag = raw[0];
                rec[FlatStore.OFF_TAG] = tag;

                switch (tag) {
                    case Expr.BVAR: {
                        long idx = readLong(raw, 1);
                        putLong(rec, FlatStore.OFF_LONG, idx);
                        break;
                    }

                    case Expr.SORT: {
                        int levelId = readInt(raw, 1);
                        putInt(rec, FlatStore.OFF_F0, levelId);
                        break;
                    }

                    case Expr.CONST: {
                        int nameId = readInt(raw, 1);
                        int numLevels = readUShort(raw, 5);
                        putInt(rec, FlatStore.OFF_F0, nameId);
                        putInt(rec, FlatStore.OFF_F1, numLevels);

                        if (numLevels > 0) {
                            // Write level IDs to side data
                            putLong(rec, FlatStore.OFF_LONG, sidePos);
                            byte[] levelBytes = new byte[numLevels * 4];
                            for (int i = 0; i < numLevels; i++) {
                                int levelId = readInt(raw, 7 + i * 4);
                                putInt(levelBytes, i * 4, levelId);
                            }
                            sideOut.write(levelBytes);
                            sidePos += levelBytes.length;
                        }
                        break;
                    }

                    case Expr.APP: {
                        putInt(rec, FlatStore.OFF_F0, readInt(raw, 1));
                        putInt(rec, FlatStore.OFF_F1, readInt(raw, 5));
                        break;
                    }

                    case Expr.LAM:
                    case Expr.FORALL: {
                        rec[FlatStore.OFF_AUX] = raw[1]; // binderInfo
                        putInt(rec, FlatStore.OFF_F0, readInt(raw, 2));  // nameId
                        putInt(rec, FlatStore.OFF_F1, readInt(raw, 6));  // typeId
                        putInt(rec, FlatStore.OFF_F2, readInt(raw, 10)); // bodyId
                        break;
                    }

                    case Expr.LET: {
                        putInt(rec, FlatStore.OFF_F0, readInt(raw, 1));  // nameId
                        putInt(rec, FlatStore.OFF_F1, readInt(raw, 5));  // typeId
                        putInt(rec, FlatStore.OFF_F2, readInt(raw, 9));  // valueId
                        putInt(rec, FlatStore.OFF_F3, readInt(raw, 13)); // bodyId
                        break;
                    }

                    case Expr.LIT_NAT: {
                        int len = readUShort(raw, 1);
                        byte[] bigBytes = Arrays.copyOfRange(raw, 3, 3 + len);
                        BigInteger val = new BigInteger(bigBytes);

                        if (val.signum() >= 0 && val.bitLength() < 63) {
                            putLong(rec, FlatStore.OFF_LONG, val.longValueExact());
                        } else {
                            // Big value: store in side data
                            byte[] sideBuf = new byte[2 + bigBytes.length];
                            putShort(sideBuf, 0, (short) bigBytes.length);
                            System.arraycopy(bigBytes, 0, sideBuf, 2, bigBytes.length);
                            putLong(rec, FlatStore.OFF_LONG, sidePos | (1L << 63));
                            sideOut.write(sideBuf);
                            sidePos += sideBuf.length;
                        }
                        break;
                    }

                    case Expr.LIT_STR: {
                        int len = readInt(raw, 1);
                        byte[] strBytes = Arrays.copyOfRange(raw, 5, 5 + len);

                        putInt(rec, FlatStore.OFF_F0, len);
                        putLong(rec, FlatStore.OFF_LONG, sidePos);
                        sideOut.write(strBytes);
                        sidePos += len;
                        break;
                    }

                    case Expr.MDATA: {
                        putInt(rec, FlatStore.OFF_F0, readInt(raw, 1));
                        break;
                    }

                    case Expr.PROJ: {
                        putInt(rec, FlatStore.OFF_F0, readInt(raw, 1));  // nameId
                        putInt(rec, FlatStore.OFF_F1, readInt(raw, 5));  // projIdx
                        putInt(rec, FlatStore.OFF_F2, readInt(raw, 9));  // structId
                        break;
                    }

                    case Expr.FVAR: {
                        putLong(rec, FlatStore.OFF_LONG, readLong(raw, 1));
                        break;
                    }

                    default:
                        Arrays.fill(rec, (byte) 0xFF);
                        break;
                }

                arenaOut.write(rec);

                if (id > 0 && id % 5000000 == 0) {
                    System.out.println("[FlatStoreWriter]   exprs: " + id + "/" + count);
                }
            }
        }
    }

    // ================================================================
    // Declarations
    // ================================================================

    private static void writeDecls(Path outDir,
                                    DeclProvider declProvider,
                                    String[] declOrder,
                                    ArrayList<?> names,
                                    Map<Object, Integer> nameIndex) throws IOException {
        // Hash table: 4M slots × 16 bytes = 64MB
        byte[] idx = new byte[FlatStore.DECL_IDX_SIZE];
        ByteBuffer idxBuf = ByteBuffer.wrap(idx);
        idxBuf.order(ByteOrder.nativeOrder());

        // Data: variable-length records, estimate ~100 bytes avg
        // Must use native byte order to match MemorySegment reads
        ByteBuffer data = ByteBuffer.allocate(declOrder.length * 120);
        data.order(ByteOrder.nativeOrder());

        for (int i = 0; i < declOrder.length; i++) {
            String nameStr = declOrder[i];
            Name name = Name.fromString(nameStr);
            ConstantInfo ci = declProvider.lookup(name);
            if (ci == null) {
                System.err.println("[FlatStoreWriter] WARNING: decl not found: " + nameStr);
                continue;
            }

            // Ensure data buffer has room
            if (data.remaining() < 4096) {
                data = grow(data, 4096);
            }

            int dataOffset = data.position();

            // Write declaration record
            writeDecl(data, ci, nameIndex);

            // Use the actual CI name for hash table (not fromString, which may differ
            // for names with special characters like dots in string components)
            long nameHash = ci.name.hashCode() & 0xFFFFFFFFL;
            if (nameHash == 0) nameHash = 1;
            int slot = (int)(nameHash & FlatStore.DECL_SLOT_MASK);

            for (int probe = 0; probe < FlatStore.DECL_SLOTS; probe++) {
                long slotBase = (long) slot * FlatStore.DECL_SLOT_SIZE;
                long storedHash = idxBuf.getLong((int) slotBase);
                if (storedHash == 0) {
                    // Empty slot — insert
                    idxBuf.putLong((int) slotBase, nameHash);
                    idxBuf.putInt((int) slotBase + 8, dataOffset);
                    break;
                }
                slot = (slot + 1) & FlatStore.DECL_SLOT_MASK;
            }

            if (i > 0 && i % 100000 == 0) {
                System.out.println("[FlatStoreWriter]   decls: " + i + "/" + declOrder.length);
            }
        }

        Files.write(outDir.resolve("decls.idx"), idx);

        data.flip();
        Files.write(outDir.resolve("decls.data"), Arrays.copyOf(data.array(), data.limit()));
    }

    private static void writeDecl(ByteBuffer data, ConstantInfo ci,
                                   Map<Object, Integer> nameIndex) {
        data.put(ci.tag);

        // Name ID
        Integer nameId = nameIndex.get(ci.name);
        data.putInt(nameId != null ? nameId : -1);

        // Type expr ID (storeId from the Expr)
        data.putInt(ci.type != null ? ci.type.storeId : -1);

        // Value expr ID
        data.putInt(ci.value != null ? ci.value.storeId : -1);

        // Hints
        data.putInt(ci.hints);

        // Safety
        data.put(ci.safety);

        // Flags: bit 0=isRec, bit 1=isReflexive, bit 2=isUnsafe, bit 3=isK
        byte flags = 0;
        if (ci.isRec) flags |= 1;
        if (ci.isReflexive) flags |= 2;
        if (ci.isUnsafe) flags |= 4;
        if (ci.isK) flags |= 8;
        data.put(flags);

        // Univ params
        data.putShort((short) ci.levelParams.length);
        for (Object lp : ci.levelParams) {
            Integer lpId = nameIndex.get(lp);
            data.putInt(lpId != null ? lpId : -1);
        }

        // Tag-specific fields
        switch (ci.tag) {
            case ConstantInfo.AXIOM:
            case ConstantInfo.QUOT:
                // No extra fields
                break;

            case ConstantInfo.DEF:
            case ConstantInfo.THM:
            case ConstantInfo.OPAQUE: {
                // all[] (mutual group names)
                Object[] all = ci.all;
                data.putShort((short) (all != null ? all.length : 0));
                if (all != null) {
                    for (Object a : all) {
                        Integer aId = nameIndex.get(a);
                        data.putInt(aId != null ? aId : -1);
                    }
                }
                break;
            }

            case ConstantInfo.INDUCT: {
                data.putInt(ci.numParams);
                data.putInt(ci.numIndices);
                data.putInt(ci.numNested);
                // all[]
                Object[] all = ci.all;
                data.putShort((short) (all != null ? all.length : 0));
                if (all != null) {
                    for (Object a : all) {
                        Integer aId = nameIndex.get(a);
                        data.putInt(aId != null ? aId : -1);
                    }
                }
                // ctors[]
                Name[] ctors = ci.ctors;
                data.putShort((short) (ctors != null ? ctors.length : 0));
                if (ctors != null) {
                    for (Name c : ctors) {
                        Integer cId = nameIndex.get(c);
                        data.putInt(cId != null ? cId : -1);
                    }
                }
                break;
            }

            case ConstantInfo.CTOR: {
                Integer inductId = nameIndex.get(ci.inductName);
                data.putInt(inductId != null ? inductId : -1);
                data.putInt(ci.cidx);
                data.putInt(ci.numParams);
                data.putInt(ci.numFields);
                break;
            }

            case ConstantInfo.RECURSOR: {
                data.putInt(ci.numParams);
                data.putInt(ci.numIndices);
                data.putInt(ci.numMotives);
                data.putInt(ci.numMinors);
                // all[]
                Object[] all = ci.all;
                data.putShort((short) (all != null ? all.length : 0));
                if (all != null) {
                    for (Object a : all) {
                        Integer aId = nameIndex.get(a);
                        data.putInt(aId != null ? aId : -1);
                    }
                }
                // rules[]
                ConstantInfo.RecursorRule[] rules = ci.rules;
                data.putShort((short) (rules != null ? rules.length : 0));
                if (rules != null) {
                    for (ConstantInfo.RecursorRule rule : rules) {
                        Integer ctorId = nameIndex.get(rule.ctor);
                        data.putInt(ctorId != null ? ctorId : -1);
                        data.putInt(rule.nfields);
                        data.putInt(rule.rhs != null ? rule.rhs.storeId : -1);
                    }
                }
                // majorIdx (numParams + numMotives, for compatibility)
                data.putInt(ci.numParams + ci.numMotives);
                break;
            }
        }
    }

    // ================================================================
    // Declaration order
    // ================================================================

    private static void writeDeclOrder(Path path, String[] declOrder) throws IOException {
        // Estimate: 4 + declOrder.length * 30
        ByteBuffer bb = ByteBuffer.allocate(4 + declOrder.length * 40);
        bb.putInt(declOrder.length);

        for (String name : declOrder) {
            byte[] strBytes = name.getBytes(StandardCharsets.UTF_8);
            if (bb.remaining() < strBytes.length + 2) {
                bb = grow(bb, strBytes.length + 2);
            }
            bb.putShort((short) strBytes.length);
            bb.put(strBytes);
        }

        bb.flip();
        Files.write(path, Arrays.copyOf(bb.array(), bb.limit()));
    }

    /**
     * Write a name-id order file mapping decl-order index to name-id.
     * This allows looking up the actual Name object from the names array,
     * avoiding Name.fromString roundtrip issues with special characters.
     *
     * @param nameIds array of name IDs (one per decl-order entry)
     */
    public static void writeDeclNameIds(Path path, int[] nameIds) throws IOException {
        ByteBuffer bb = ByteBuffer.allocate(4 + nameIds.length * 4);
        bb.order(ByteOrder.nativeOrder());
        bb.putInt(nameIds.length);
        for (int id : nameIds) {
            bb.putInt(id);
        }
        bb.flip();
        Files.write(path, Arrays.copyOf(bb.array(), bb.limit()));
    }

    // ================================================================
    // Utility: reading big-endian from byte arrays (ExprStore format)
    // ================================================================

    private static int readInt(byte[] buf, int off) {
        return ((buf[off] & 0xFF) << 24) |
               ((buf[off + 1] & 0xFF) << 16) |
               ((buf[off + 2] & 0xFF) << 8) |
               (buf[off + 3] & 0xFF);
    }

    private static int readUShort(byte[] buf, int off) {
        return ((buf[off] & 0xFF) << 8) | (buf[off + 1] & 0xFF);
    }

    private static long readLong(byte[] buf, int off) {
        return ((long)(buf[off] & 0xFF) << 56) |
               ((long)(buf[off + 1] & 0xFF) << 48) |
               ((long)(buf[off + 2] & 0xFF) << 40) |
               ((long)(buf[off + 3] & 0xFF) << 32) |
               ((long)(buf[off + 4] & 0xFF) << 24) |
               ((long)(buf[off + 5] & 0xFF) << 16) |
               ((long)(buf[off + 6] & 0xFF) << 8) |
               ((long)(buf[off + 7] & 0xFF));
    }

    // ================================================================
    // Writing native-endian to byte arrays (for mmap'd arena records)
    // FlatStore reads via MemorySegment with JAVA_INT/JAVA_LONG (native order)
    // ================================================================

    private static final boolean BIG_ENDIAN = ByteOrder.nativeOrder() == ByteOrder.BIG_ENDIAN;

    private static void putShort(byte[] buf, int off, short val) {
        if (BIG_ENDIAN) {
            buf[off]     = (byte) (val >> 8);
            buf[off + 1] = (byte) val;
        } else {
            buf[off]     = (byte) val;
            buf[off + 1] = (byte) (val >> 8);
        }
    }

    private static void putInt(byte[] buf, int off, int val) {
        if (BIG_ENDIAN) {
            buf[off]     = (byte) (val >> 24);
            buf[off + 1] = (byte) (val >> 16);
            buf[off + 2] = (byte) (val >> 8);
            buf[off + 3] = (byte) val;
        } else {
            buf[off]     = (byte) val;
            buf[off + 1] = (byte) (val >> 8);
            buf[off + 2] = (byte) (val >> 16);
            buf[off + 3] = (byte) (val >> 24);
        }
    }

    private static void putLong(byte[] buf, int off, long val) {
        if (BIG_ENDIAN) {
            buf[off]     = (byte) (val >> 56);
            buf[off + 1] = (byte) (val >> 48);
            buf[off + 2] = (byte) (val >> 40);
            buf[off + 3] = (byte) (val >> 32);
            buf[off + 4] = (byte) (val >> 24);
            buf[off + 5] = (byte) (val >> 16);
            buf[off + 6] = (byte) (val >> 8);
            buf[off + 7] = (byte) val;
        } else {
            buf[off]     = (byte) val;
            buf[off + 1] = (byte) (val >> 8);
            buf[off + 2] = (byte) (val >> 16);
            buf[off + 3] = (byte) (val >> 24);
            buf[off + 4] = (byte) (val >> 32);
            buf[off + 5] = (byte) (val >> 40);
            buf[off + 6] = (byte) (val >> 48);
            buf[off + 7] = (byte) (val >> 56);
        }
    }

    // ================================================================
    // ByteBuffer growth
    // ================================================================

    private static ByteBuffer grow(ByteBuffer bb) {
        return grow(bb, 0);
    }

    private static ByteBuffer grow(ByteBuffer bb, int extraNeeded) {
        int newCap = Math.max(bb.capacity() * 2, bb.position() + extraNeeded + 1024);
        ByteBuffer newBb = ByteBuffer.allocate(newCap);
        newBb.order(bb.order());
        bb.flip();
        newBb.put(bb);
        return newBb;
    }
}
