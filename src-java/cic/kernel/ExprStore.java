// Copyright (c) 2026 Simmis GmbH. All rights reserved.
// CIC kernel — File-backed expression store for large imports.

package cic.kernel;

import java.io.*;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * File-backed expression store that keeps expressions on disk and deserializes on demand.
 *
 * <p>Replaces ArrayList&lt;Expr&gt; in the parser to avoid holding all Expr objects on the
 * JVM heap simultaneously. For Mathlib (~91M expressions, ~7GB on heap), this reduces
 * heap usage to ~1.2GB by keeping expression data in a temp file backed by OS page cache.
 *
 * <p>Two-phase caching:
 * <ul>
 *   <li><b>Parse phase</b>: Direct-mapped ring buffer (256K slots). During bottom-up
 *       construction, recently stored IDs are the ones most likely to be resolved next.
 *   <li><b>TC phase</b>: Larger direct-mapped hash cache (1M slots) with SoftReferences
 *       for GC-friendly random access patterns during type checking.
 * </ul>
 *
 * <p>Binary format per expression tag (compact, average ~10 bytes):
 * <ul>
 *   <li>BVAR: tag(1) + index(8) = 9 bytes
 *   <li>SORT: tag(1) + level-id(4) = 5 bytes
 *   <li>CONST: tag(1) + name-id(4) + num-levels(2) + level-ids(4*n) = 7+4n bytes
 *   <li>APP: tag(1) + fn-id(4) + arg-id(4) = 9 bytes
 *   <li>LAM/FORALL: tag(1) + binder-info(1) + name-id(4) + type-id(4) + body-id(4) = 14 bytes
 *   <li>LET: tag(1) + name-id(4) + type-id(4) + value-id(4) + body-id(4) = 17 bytes
 *   <li>LIT_NAT: tag(1) + byte-length(2) + bigint-bytes(n) = 3+n bytes
 *   <li>LIT_STR: tag(1) + str-length(4) + utf8-bytes(n) = 5+n bytes
 *   <li>MDATA: tag(1) + expr-id(4) = 5 bytes
 *   <li>PROJ: tag(1) + name-id(4) + index(4) + expr-id(4) = 13 bytes
 *   <li>FVAR: tag(1) + id(8) = 9 bytes
 * </ul>
 */
public final class ExprStore implements Closeable {

    // --- Binary format tags ---
    private static final byte TAG_BVAR = 0;
    private static final byte TAG_SORT = 1;
    private static final byte TAG_CONST = 2;
    private static final byte TAG_APP = 3;
    private static final byte TAG_LAM = 4;
    private static final byte TAG_FORALL = 5;
    private static final byte TAG_LET = 6;
    private static final byte TAG_LIT_NAT = 7;
    private static final byte TAG_LIT_STR = 8;
    private static final byte TAG_MDATA = 9;
    private static final byte TAG_PROJ = 10;
    private static final byte TAG_FVAR = 11;

    // --- Binder info encoding ---
    private static final byte BI_DEFAULT = 0;
    private static final byte BI_IMPLICIT = 1;
    private static final byte BI_STRICT_IMPLICIT = 2;
    private static final byte BI_INST_IMPLICIT = 3;

    /** Binder info lookup table: byte → Clojure keyword. */
    private static final Object[] BINDER_INFOS;
    static {
        BINDER_INFOS = new Object[4];
        BINDER_INFOS[BI_DEFAULT] = clojure.lang.Keyword.intern(null, "default");
        BINDER_INFOS[BI_IMPLICIT] = clojure.lang.Keyword.intern(null, "implicit");
        BINDER_INFOS[BI_STRICT_IMPLICIT] = clojure.lang.Keyword.intern(null, "strict-implicit");
        BINDER_INFOS[BI_INST_IMPLICIT] = clojure.lang.Keyword.intern(null, "inst-implicit");
    }

    // --- Offset index (two-level paged array) ---
    private static final int PAGE_BITS = 12;
    private static final int PAGE_SIZE = 1 << PAGE_BITS; // 4096
    private static final int PAGE_MASK = PAGE_SIZE - 1;
    private static final long UNSET_OFFSET = -1L;

    private long[][] offsets; // offsets[id >> PAGE_BITS][id & PAGE_MASK]
    private int numPages;

    // --- Parse-phase ring buffer (direct-mapped cache) ---
    private static final int RING_BITS = 18;
    private static final int RING_SIZE = 1 << RING_BITS; // 262144 (256K)
    private static final int RING_MASK = RING_SIZE - 1;

    private final Expr[] ringBuf = new Expr[RING_SIZE];
    private final int[] ringIds = new int[RING_SIZE];

    // --- TC-phase hash cache (direct-mapped with SoftReferences) ---
    private static final int CACHE_BITS = 20;
    private static final int CACHE_SIZE = 1 << CACHE_BITS; // 1048576 (1M)
    private static final int CACHE_MASK = CACHE_SIZE - 1;

    private int[] cacheIds;
    @SuppressWarnings("unchecked")
    private java.lang.ref.SoftReference<Expr>[] cacheRefs;

    // --- File I/O ---
    private final File tempFile;
    private DataOutputStream writer;
    private RandomAccessFile reader;
    private long writePos;
    private boolean writerDirty;

    // --- Dependencies ---
    private final ArrayList<?> names;  // index → Name
    private final ArrayList<?> levels; // index → Level

    // --- State ---
    private int maxId; // 1 + highest stored ID
    private boolean parsePhase = true;

    /**
     * Create a new file-backed expression store.
     *
     * @param names  the name table (ArrayList of Name objects, indexed by name ID)
     * @param levels the level table (ArrayList of Level objects, indexed by level ID)
     */
    public ExprStore(ArrayList<?> names, ArrayList<?> levels) throws IOException {
        this.names = names;
        this.levels = levels;

        // Initialize offset index
        this.numPages = 64; // start with 64 pages = 256K slots
        this.offsets = new long[numPages][];

        // Initialize ring buffer IDs to -1 (no entry)
        Arrays.fill(ringIds, -1);

        // Open temp file
        this.tempFile = File.createTempFile("cic-expr-store-", ".bin");
        this.tempFile.deleteOnExit();
        FileOutputStream fos = new FileOutputStream(tempFile);
        this.writer = new DataOutputStream(new BufferedOutputStream(fos, 65536));
        this.reader = new RandomAccessFile(tempFile, "r");
        this.writePos = 0;
        this.writerDirty = false;
        this.maxId = 0;
    }

    // --- Offset index management ---

    private void ensureOffsetSlot(int id) {
        int pageIdx = id >> PAGE_BITS;
        if (pageIdx >= numPages) {
            int newNumPages = Math.max(numPages * 2, pageIdx + 1);
            long[][] newOffsets = new long[newNumPages][];
            System.arraycopy(offsets, 0, newOffsets, 0, numPages);
            offsets = newOffsets;
            numPages = newNumPages;
        }
        if (offsets[pageIdx] == null) {
            offsets[pageIdx] = new long[PAGE_SIZE];
            Arrays.fill(offsets[pageIdx], UNSET_OFFSET);
        }
    }

    private long getOffset(int id) {
        int pageIdx = id >> PAGE_BITS;
        if (pageIdx >= numPages || offsets[pageIdx] == null) {
            return UNSET_OFFSET;
        }
        return offsets[pageIdx][id & PAGE_MASK];
    }

    private void setOffset(int id, long offset) {
        ensureOffsetSlot(id);
        offsets[id >> PAGE_BITS][id & PAGE_MASK] = offset;
        if (id >= maxId) maxId = id + 1;
    }

    // --- Flush writer before reads ---

    private void flushIfNeeded() throws IOException {
        if (writerDirty) {
            writer.flush();
            writerDirty = false;
        }
    }

    // --- Store methods (called by parser with raw integer IDs from JSON) ---

    public void storeBvar(int id, long idx) throws IOException {
        setOffset(id, writePos);
        writer.writeByte(TAG_BVAR);
        writer.writeLong(idx);
        writePos += 9;
        writerDirty = true;
    }

    public void storeSort(int id, int levelId) throws IOException {
        setOffset(id, writePos);
        writer.writeByte(TAG_SORT);
        writer.writeInt(levelId);
        writePos += 5;
        writerDirty = true;
    }

    public void storeConst(int id, int nameId, int[] levelIds) throws IOException {
        setOffset(id, writePos);
        writer.writeByte(TAG_CONST);
        writer.writeInt(nameId);
        writer.writeShort(levelIds.length);
        for (int lid : levelIds) {
            writer.writeInt(lid);
        }
        writePos += 7 + 4 * levelIds.length;
        writerDirty = true;
    }

    public void storeApp(int id, int fnId, int argId) throws IOException {
        setOffset(id, writePos);
        writer.writeByte(TAG_APP);
        writer.writeInt(fnId);
        writer.writeInt(argId);
        writePos += 9;
        writerDirty = true;
    }

    public void storeLam(int id, byte binderInfo, int nameId, int typeId, int bodyId) throws IOException {
        setOffset(id, writePos);
        writer.writeByte(TAG_LAM);
        writer.writeByte(binderInfo);
        writer.writeInt(nameId);
        writer.writeInt(typeId);
        writer.writeInt(bodyId);
        writePos += 14;
        writerDirty = true;
    }

    public void storeForall(int id, byte binderInfo, int nameId, int typeId, int bodyId) throws IOException {
        setOffset(id, writePos);
        writer.writeByte(TAG_FORALL);
        writer.writeByte(binderInfo);
        writer.writeInt(nameId);
        writer.writeInt(typeId);
        writer.writeInt(bodyId);
        writePos += 14;
        writerDirty = true;
    }

    public void storeLet(int id, int nameId, int typeId, int valueId, int bodyId) throws IOException {
        setOffset(id, writePos);
        writer.writeByte(TAG_LET);
        writer.writeInt(nameId);
        writer.writeInt(typeId);
        writer.writeInt(valueId);
        writer.writeInt(bodyId);
        writePos += 17;
        writerDirty = true;
    }

    public void storeLitNat(int id, BigInteger n) throws IOException {
        setOffset(id, writePos);
        byte[] bytes = n.toByteArray();
        writer.writeByte(TAG_LIT_NAT);
        writer.writeShort(bytes.length);
        writer.write(bytes);
        writePos += 3 + bytes.length;
        writerDirty = true;
    }

    public void storeLitStr(int id, String s) throws IOException {
        setOffset(id, writePos);
        byte[] bytes = s.getBytes(StandardCharsets.UTF_8);
        writer.writeByte(TAG_LIT_STR);
        writer.writeInt(bytes.length);
        writer.write(bytes);
        writePos += 5 + bytes.length;
        writerDirty = true;
    }

    public void storeMdata(int id, int innerExprId) throws IOException {
        setOffset(id, writePos);
        writer.writeByte(TAG_MDATA);
        writer.writeInt(innerExprId);
        writePos += 5;
        writerDirty = true;
    }

    public void storeProj(int id, int nameId, int projIdx, int structId) throws IOException {
        setOffset(id, writePos);
        writer.writeByte(TAG_PROJ);
        writer.writeInt(nameId);
        writer.writeInt(projIdx);
        writer.writeInt(structId);
        writePos += 13;
        writerDirty = true;
    }

    public void storeFvar(int id, long fvarId) throws IOException {
        setOffset(id, writePos);
        writer.writeByte(TAG_FVAR);
        writer.writeLong(fvarId);
        writePos += 9;
        writerDirty = true;
    }

    // --- Resolve method ---

    /**
     * Resolve an expression by ID, returning a full in-memory Expr.
     * Checks cache first (ring buffer in parse phase, hash cache in TC phase),
     * then deserializes from the backing file on miss.
     */
    public Expr resolve(int id) throws IOException {
        // Check cache
        Expr cached = cacheGet(id);
        if (cached != null) return cached;

        // Deserialize from file
        long offset = getOffset(id);
        if (offset == UNSET_OFFSET) {
            throw new IllegalArgumentException("Unknown expr id: " + id);
        }

        flushIfNeeded();
        reader.seek(offset);
        byte tag = reader.readByte();

        Expr result;
        switch (tag) {
            case TAG_BVAR: {
                long idx = reader.readLong();
                result = Expr.bvar(idx);
                break;
            }
            case TAG_SORT: {
                int levelId = reader.readInt();
                Level level = (Level) levels.get(levelId);
                result = Expr.sort(level, Level.hasParam(level));
                break;
            }
            case TAG_CONST: {
                int nameId = reader.readInt();
                int numLevels = reader.readUnsignedShort();
                Object name = names.get(nameId);
                boolean hasParam = false;
                if (numLevels == 0) {
                    result = Expr.mkConst(name, java.util.Collections.emptyList(), false);
                } else {
                    Object[] lvls = new Object[numLevels];
                    for (int i = 0; i < numLevels; i++) {
                        Level l = (Level) levels.get(reader.readInt());
                        lvls[i] = l;
                        if (!hasParam && Level.hasParam(l)) hasParam = true;
                    }
                    result = Expr.mkConst(name, Arrays.asList(lvls), hasParam);
                }
                break;
            }
            case TAG_APP: {
                int fnId = reader.readInt();
                int argId = reader.readInt();
                Expr fn = resolve(fnId);
                Expr arg = resolve(argId);
                result = Expr.app(fn, arg);
                break;
            }
            case TAG_LAM: {
                byte bi = reader.readByte();
                int nameId = reader.readInt();
                int typeId = reader.readInt();
                int bodyId = reader.readInt();
                Object name = names.get(nameId);
                Expr type = resolve(typeId);
                Expr body = resolve(bodyId);
                result = Expr.lam(name, type, body, BINDER_INFOS[bi]);
                break;
            }
            case TAG_FORALL: {
                byte bi = reader.readByte();
                int nameId = reader.readInt();
                int typeId = reader.readInt();
                int bodyId = reader.readInt();
                Object name = names.get(nameId);
                Expr type = resolve(typeId);
                Expr body = resolve(bodyId);
                result = Expr.forall(name, type, body, BINDER_INFOS[bi]);
                break;
            }
            case TAG_LET: {
                int nameId = reader.readInt();
                int typeId = reader.readInt();
                int valueId = reader.readInt();
                int bodyId = reader.readInt();
                Object name = names.get(nameId);
                Expr type = resolve(typeId);
                Expr value = resolve(valueId);
                Expr body = resolve(bodyId);
                result = Expr.mkLet(name, type, value, body);
                break;
            }
            case TAG_LIT_NAT: {
                int len = reader.readUnsignedShort();
                byte[] bytes = new byte[len];
                reader.readFully(bytes);
                result = Expr.litNat(new BigInteger(bytes));
                break;
            }
            case TAG_LIT_STR: {
                int len = reader.readInt();
                byte[] bytes = new byte[len];
                reader.readFully(bytes);
                result = Expr.litStr(new String(bytes, StandardCharsets.UTF_8));
                break;
            }
            case TAG_MDATA: {
                int innerExprId = reader.readInt();
                Expr inner = resolve(innerExprId);
                // mdata metadata is not stored (definitionally transparent, unused in TC)
                result = Expr.mdata(null, inner);
                break;
            }
            case TAG_PROJ: {
                int nameId = reader.readInt();
                int projIdx = reader.readInt();
                int structId = reader.readInt();
                Object name = names.get(nameId);
                Expr struct = resolve(structId);
                result = Expr.proj(name, (long) projIdx, struct);
                break;
            }
            case TAG_FVAR: {
                long fvarId = reader.readLong();
                result = Expr.fvar(fvarId);
                break;
            }
            default:
                throw new IOException("Unknown expr tag: " + tag + " at offset " + offset);
        }

        // Tag with store ID for is_eqp semantics
        result.storeId = id;

        // Cache the resolved expression
        cachePut(id, result);
        return result;
    }

    // --- Cache operations ---

    private Expr cacheGet(int id) {
        if (parsePhase) {
            int slot = id & RING_MASK;
            if (ringIds[slot] == id) return ringBuf[slot];
            return null;
        } else {
            int slot = id & CACHE_MASK;
            if (cacheIds[slot] == id) {
                java.lang.ref.SoftReference<Expr> ref = cacheRefs[slot];
                if (ref != null) return ref.get();
            }
            return null;
        }
    }

    private void cachePut(int id, Expr expr) {
        if (parsePhase) {
            int slot = id & RING_MASK;
            ringIds[slot] = id;
            ringBuf[slot] = expr;
        } else {
            int slot = id & CACHE_MASK;
            cacheIds[slot] = id;
            cacheRefs[slot] = new java.lang.ref.SoftReference<>(expr);
        }
    }

    // --- Phase transition ---

    /**
     * Switch from parse phase (ring buffer cache) to TC phase (hash cache).
     * Call this after all expressions have been stored and before type checking begins.
     */
    @SuppressWarnings("unchecked")
    public void finishParsing() throws IOException {
        flushIfNeeded();
        // Release ring buffer
        Arrays.fill(ringBuf, null);
        Arrays.fill(ringIds, -1);
        // Initialize TC-phase hash cache
        cacheIds = new int[CACHE_SIZE];
        cacheRefs = new java.lang.ref.SoftReference[CACHE_SIZE];
        Arrays.fill(cacheIds, -1);
        parsePhase = false;
    }

    // --- Query ---

    /** Number of stored expressions (1 + highest stored ID). */
    public int size() {
        return maxId;
    }

    /** Highest stored ID + 1 (alias for size, for iteration). */
    public int maxId() {
        return maxId;
    }

    /**
     * Read raw binary record for an expression without deserializing into Expr.
     * Returns the complete binary record (tag byte + payload) as a byte array.
     * Useful for bulk export to persistent storage without incurring deserialization cost.
     *
     * @param id the expression ID
     * @return raw bytes for this expression record
     * @throws IOException on I/O error
     * @throws IllegalArgumentException if ID is unknown
     */
    public byte[] readRaw(int id) throws IOException {
        long offset = getOffset(id);
        if (offset == UNSET_OFFSET) {
            throw new IllegalArgumentException("Unknown expr id: " + id);
        }

        flushIfNeeded();
        reader.seek(offset);
        byte tag = reader.readByte();

        int payloadLen;
        switch (tag) {
            case TAG_BVAR:    payloadLen = 8; break;   // long idx
            case TAG_SORT:    payloadLen = 4; break;   // int levelId
            case TAG_CONST: {
                // name(4) + numLevels(2) + levelIds(4*n)
                reader.seek(offset + 1 + 4); // skip tag + nameId
                int numLevels = reader.readUnsignedShort();
                payloadLen = 4 + 2 + 4 * numLevels;
                break;
            }
            case TAG_APP:     payloadLen = 8; break;   // fnId(4) + argId(4)
            case TAG_LAM:     payloadLen = 13; break;  // bi(1) + nameId(4) + typeId(4) + bodyId(4)
            case TAG_FORALL:  payloadLen = 13; break;  // bi(1) + nameId(4) + typeId(4) + bodyId(4)
            case TAG_LET:     payloadLen = 16; break;  // nameId(4) + typeId(4) + valueId(4) + bodyId(4)
            case TAG_LIT_NAT: {
                reader.seek(offset + 1); // skip tag
                int len = reader.readUnsignedShort();
                payloadLen = 2 + len;
                break;
            }
            case TAG_LIT_STR: {
                reader.seek(offset + 1); // skip tag
                int len = reader.readInt();
                payloadLen = 4 + len;
                break;
            }
            case TAG_MDATA:   payloadLen = 4; break;   // innerExprId(4)
            case TAG_PROJ:    payloadLen = 12; break;  // nameId(4) + projIdx(4) + structId(4)
            case TAG_FVAR:    payloadLen = 8; break;   // long fvarId
            default:
                throw new IOException("Unknown expr tag: " + tag + " at offset " + offset);
        }

        byte[] result = new byte[1 + payloadLen];
        reader.seek(offset);
        reader.readFully(result);
        return result;
    }

    // --- Binder info conversion helper (for use from Clojure) ---

    /**
     * Convert a binder info keyword to a byte for storage.
     * Accepts Clojure keywords :default, :implicit, :strict-implicit, :inst-implicit.
     */
    public static byte binderInfoToByte(Object bi) {
        if (bi == BINDER_INFOS[BI_DEFAULT]) return BI_DEFAULT;
        if (bi == BINDER_INFOS[BI_IMPLICIT]) return BI_IMPLICIT;
        if (bi == BINDER_INFOS[BI_STRICT_IMPLICIT]) return BI_STRICT_IMPLICIT;
        if (bi == BINDER_INFOS[BI_INST_IMPLICIT]) return BI_INST_IMPLICIT;
        return BI_DEFAULT; // fallback
    }

    // --- Lifecycle ---

    @Override
    public void close() throws IOException {
        if (writer != null) {
            writer.close();
            writer = null;
        }
        if (reader != null) {
            reader.close();
            reader = null;
        }
        if (tempFile != null) {
            tempFile.delete();
        }
    }
}
