// Ansatz kernel — mmap'd flat store for expressions and declarations.

package ansatz.kernel;

import java.io.*;
import java.lang.foreign.*;
import java.math.BigInteger;
import java.nio.ByteOrder;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

/**
 * mmap'd flat store for zero-copy expression resolution and declaration lookup.
 *
 * <p>File layout:
 * <ul>
 *   <li>{@code exprs.arena} — fixed 32-byte records for expressions
 *   <li>{@code exprs.side} — overflow data (CONST levels, LIT_NAT big values, LIT_STR)
 *   <li>{@code decls.idx} — open-addressing hash table (name hash → data offset)
 *   <li>{@code decls.data} — variable-length declaration records
 *   <li>{@code names.data} — serialized Name array
 *   <li>{@code levels.data} — serialized Level array
 *   <li>{@code order.data} — declaration order (name strings)
 * </ul>
 *
 * <p>Expression arena record (32 bytes):
 * <pre>
 *   offset 0:  tag       (1 byte)
 *   offset 1:  aux       (1 byte, binderInfo for LAM/FORALL)
 *   offset 2:  reserved  (2 bytes)
 *   offset 4:  field0    (4 bytes, int)
 *   offset 8:  field1    (4 bytes, int)
 *   offset 12: field2    (4 bytes, int)
 *   offset 16: field3    (4 bytes, int)
 *   offset 20: reserved  (4 bytes)
 *   offset 24: longVal   (8 bytes, long)
 * </pre>
 *
 * <p>Branching via filesystem reflink: {@code cp --reflink=auto -r store-a/ store-b/}
 */
public final class FlatStore implements AutoCloseable {

    // --- Expression arena constants ---
    static final int ARENA_HEADER = 16;
    static final int RECORD_SIZE = 32;
    private static final byte[] MAGIC = {'C', 'I', 'C', '1'};

    // Field offsets within a 32-byte record
    static final int OFF_TAG = 0;
    static final int OFF_AUX = 1;
    static final int OFF_F0 = 4;
    static final int OFF_F1 = 8;
    static final int OFF_F2 = 12;
    static final int OFF_F3 = 16;
    static final int OFF_LONG = 24;

    // Unaligned value layouts for packed data (decl records, side data)
    private static final ValueLayout.OfInt INT_UNALIGNED =
        ValueLayout.JAVA_INT.withByteAlignment(1);
    private static final ValueLayout.OfLong LONG_UNALIGNED =
        ValueLayout.JAVA_LONG.withByteAlignment(1);
    private static final ValueLayout.OfShort SHORT_UNALIGNED =
        ValueLayout.JAVA_SHORT.withByteAlignment(1);

    // Binder info lookup
    private static final Object[] BINDER_INFOS = {
        clojure.lang.Keyword.intern(null, "default"),
        clojure.lang.Keyword.intern(null, "implicit"),
        clojure.lang.Keyword.intern(null, "strict-implicit"),
        clojure.lang.Keyword.intern(null, "inst-implicit")
    };

    // --- Decl index constants ---
    // 4M slots, load factor ~0.16 for 648K mathlib decls. Room for ~2M decls.
    static final int DECL_SLOTS = 1 << 22;  // 4M
    static final int DECL_SLOT_MASK = DECL_SLOTS - 1;
    static final int DECL_SLOT_SIZE = 16;  // 8 hash + 4 offset + 4 reserved
    static final int DECL_IDX_SIZE = DECL_SLOTS * DECL_SLOT_SIZE;  // 64MB

    // --- mmap'd segments ---
    private final Arena mmapArena;
    private final MemorySegment exprSeg;      // exprs.arena
    private final MemorySegment sideSeg;      // exprs.side (nullable)
    private final MemorySegment declIdxSeg;   // decls.idx
    private final MemorySegment declDataSeg;  // decls.data
    private final int exprCount;

    // --- In-memory lookup tables ---
    private final Name[] names;
    private final Level[] levels;
    private final String[] declOrder;
    private final int[] declNameIds;  // decl-order index → name ID in names[]

    // --- Expression resolution cache ---
    private static final int CACHE_BITS = 18;  // 256K slots
    private static final int CACHE_SIZE = 1 << CACHE_BITS;
    private static final int CACHE_MASK = CACHE_SIZE - 1;
    private final Expr[] exprCache = new Expr[CACHE_SIZE];
    private final int[] cacheIds = new int[CACHE_SIZE];

    private FlatStore(Arena mmapArena, MemorySegment exprSeg, MemorySegment sideSeg,
                      MemorySegment declIdxSeg, MemorySegment declDataSeg,
                      int exprCount, Name[] names, Level[] levels, String[] declOrder,
                      int[] declNameIds) {
        this.mmapArena = mmapArena;
        this.exprSeg = exprSeg;
        this.sideSeg = sideSeg;
        this.declIdxSeg = declIdxSeg;
        this.declDataSeg = declDataSeg;
        this.exprCount = exprCount;
        this.names = names;
        this.levels = levels;
        this.declOrder = declOrder;
        this.declNameIds = declNameIds;
        Arrays.fill(cacheIds, -1);
    }

    // ================================================================
    // Opening a flat store
    // ================================================================

    public static FlatStore open(Path dir) throws IOException {
        Arena arena = Arena.ofShared();
        try {
            // mmap expression arena
            MemorySegment exprSeg;
            int exprCount;
            try (FileChannel fc = FileChannel.open(dir.resolve("exprs.arena"), StandardOpenOption.READ)) {
                exprSeg = fc.map(FileChannel.MapMode.READ_ONLY, 0, fc.size(), arena);
            }
            // Verify magic
            byte[] magic = new byte[4];
            MemorySegment.copy(exprSeg, ValueLayout.JAVA_BYTE, 0, magic, 0, 4);
            if (magic[0] != 'C' || magic[1] != 'I' || magic[2] != 'C' || magic[3] != '1') {
                throw new IOException("Invalid arena magic");
            }
            exprCount = exprSeg.get(ValueLayout.JAVA_INT, 8);

            // mmap side data (optional)
            MemorySegment sideSeg = null;
            Path sidePath = dir.resolve("exprs.side");
            if (Files.exists(sidePath) && Files.size(sidePath) > 0) {
                try (FileChannel fc = FileChannel.open(sidePath, StandardOpenOption.READ)) {
                    sideSeg = fc.map(FileChannel.MapMode.READ_ONLY, 0, fc.size(), arena);
                }
            }

            // mmap decl index
            MemorySegment declIdxSeg;
            try (FileChannel fc = FileChannel.open(dir.resolve("decls.idx"), StandardOpenOption.READ)) {
                declIdxSeg = fc.map(FileChannel.MapMode.READ_ONLY, 0, fc.size(), arena);
            }

            // mmap decl data
            MemorySegment declDataSeg;
            try (FileChannel fc = FileChannel.open(dir.resolve("decls.data"), StandardOpenOption.READ)) {
                declDataSeg = fc.map(FileChannel.MapMode.READ_ONLY, 0, fc.size(), arena);
            }

            // Load names into memory
            Name[] names = loadNames(dir.resolve("names.data"));

            // Load levels into memory
            Level[] levels = loadLevels(dir.resolve("levels.data"), names);

            // Load declaration order
            String[] declOrder = loadDeclOrder(dir.resolve("order.data"));

            // Load name IDs for decl order (optional, for special-character name lookup)
            int[] declNameIds = null;
            Path nameIdsPath = dir.resolve("name-ids.data");
            if (Files.exists(nameIdsPath)) {
                declNameIds = loadDeclNameIds(nameIdsPath);
            }

            return new FlatStore(arena, exprSeg, sideSeg, declIdxSeg, declDataSeg,
                                exprCount, names, levels, declOrder, declNameIds);
        } catch (Exception e) {
            arena.close();
            throw e instanceof IOException ? (IOException) e : new IOException(e);
        }
    }

    @Override
    public void close() {
        mmapArena.close();
    }

    // ================================================================
    // Expression resolution
    // ================================================================

    public int getExprCount() { return exprCount; }

    /**
     * Resolve an expression by store ID. Returns a fully constructed Expr
     * with storeId set. Uses a direct-mapped cache for fast repeated lookups.
     */
    public Expr resolveExpr(int id) {
        int slot = id & CACHE_MASK;
        if (cacheIds[slot] == id) return exprCache[slot];
        Expr result = resolveExprUncached(id);
        result.storeId = id;
        exprCache[slot] = result;
        cacheIds[slot] = id;
        return result;
    }

    private Expr resolveExprUncached(int id) {
        long base = ARENA_HEADER + (long) id * RECORD_SIZE;
        byte tag = exprSeg.get(ValueLayout.JAVA_BYTE, base + OFF_TAG);
        byte aux = exprSeg.get(ValueLayout.JAVA_BYTE, base + OFF_AUX);
        int f0 = exprSeg.get(ValueLayout.JAVA_INT, base + OFF_F0);
        int f1 = exprSeg.get(ValueLayout.JAVA_INT, base + OFF_F1);
        int f2 = exprSeg.get(ValueLayout.JAVA_INT, base + OFF_F2);
        int f3 = exprSeg.get(ValueLayout.JAVA_INT, base + OFF_F3);
        long lv = exprSeg.get(ValueLayout.JAVA_LONG, base + OFF_LONG);

        switch (tag) {
            case Expr.BVAR:
                return Expr.bvar(lv);

            case Expr.SORT:
                return Expr.sort(levels[f0], Level.hasParam(levels[f0]));

            case Expr.CONST: {
                Name name = names[f0];
                int numLevels = f1;
                if (numLevels == 0) {
                    return Expr.mkConst(name, Collections.emptyList(), false);
                }
                // Level IDs stored in side data at offset lv
                Object[] lvls = new Object[numLevels];
                boolean hasParam = false;
                for (int i = 0; i < numLevels; i++) {
                    int levelId = sideSeg.get(INT_UNALIGNED, lv + (long) i * 4);
                    Level l = levels[levelId];
                    lvls[i] = l;
                    if (!hasParam && Level.hasParam(l)) hasParam = true;
                }
                return Expr.mkConst(name, Arrays.asList(lvls), hasParam);
            }

            case Expr.APP:
                return Expr.app(resolveExpr(f0), resolveExpr(f1));

            case Expr.LAM:
                return Expr.lam(names[f0], resolveExpr(f1), resolveExpr(f2), BINDER_INFOS[aux & 3]);

            case Expr.FORALL:
                return Expr.forall(names[f0], resolveExpr(f1), resolveExpr(f2), BINDER_INFOS[aux & 3]);

            case Expr.LET:
                return Expr.mkLet(names[f0], resolveExpr(f1), resolveExpr(f2), resolveExpr(f3));

            case Expr.LIT_NAT: {
                if ((lv & (1L << 63)) == 0) {
                    // Small value: fits in 63 bits
                    return Expr.litNat(BigInteger.valueOf(lv));
                }
                // Big value: read from side data
                long sideOff = lv & ~(1L << 63);
                int len = sideSeg.get(SHORT_UNALIGNED, sideOff) & 0xFFFF;
                byte[] bytes = new byte[len];
                MemorySegment.copy(sideSeg, ValueLayout.JAVA_BYTE, sideOff + 2, bytes, 0, len);
                return Expr.litNat(new BigInteger(bytes));
            }

            case Expr.LIT_STR: {
                // f0 = side offset, f1 = string length
                long sideOff = Integer.toUnsignedLong(f0) | ((long) f1 << 32);
                // Actually: use longVal for side offset, f0 for length
                int len = f0;
                byte[] bytes = new byte[len];
                MemorySegment.copy(sideSeg, ValueLayout.JAVA_BYTE, lv, bytes, 0, len);
                return Expr.litStr(new String(bytes, StandardCharsets.UTF_8));
            }

            case Expr.MDATA:
                return Expr.mdata(null, resolveExpr(f0));

            case Expr.PROJ:
                return Expr.proj(names[f0], (long) f1, resolveExpr(f2));

            case Expr.FVAR:
                return Expr.fvar(lv);

            default:
                throw new RuntimeException("Unknown expr tag: " + tag + " at id " + id);
        }
    }

    // ================================================================
    // Declaration lookup
    // ================================================================

    public String[] getDeclOrder() { return declOrder; }

    /**
     * Get the actual Name object for a decl-order index.
     * Uses name-ids.data mapping to avoid Name.fromString roundtrip issues.
     * Falls back to Name.fromString if name-ids.data is not available.
     */
    public Name getDeclName(int orderIdx) {
        if (declNameIds != null && orderIdx >= 0 && orderIdx < declNameIds.length) {
            int nameId = declNameIds[orderIdx];
            if (nameId >= 0 && nameId < names.length) {
                return names[nameId];
            }
        }
        return Name.fromString(declOrder[orderIdx]);
    }

    /**
     * Look up a declaration by name. Uses the mmap'd open-addressing hash table.
     * Returns null if not found.
     */
    public ConstantInfo lookupDecl(Name name) {
        long nameHash = name.hashCode() & 0xFFFFFFFFL;
        if (nameHash == 0) nameHash = 1;  // 0 = empty slot sentinel
        int slot = (int)(nameHash & DECL_SLOT_MASK);

        for (int i = 0; i < DECL_SLOTS; i++) {
            long slotBase = (long) slot * DECL_SLOT_SIZE;
            long storedHash = declIdxSeg.get(ValueLayout.JAVA_LONG, slotBase);
            if (storedHash == 0) return null;  // empty slot — not found
            if (storedHash == nameHash) {
                int dataOffset = declIdxSeg.get(ValueLayout.JAVA_INT, slotBase + 8);
                ConstantInfo ci = readDecl(dataOffset);
                if (ci.name.equals(name)) return ci;
                // Hash collision with different name — continue probing
            }
            slot = (slot + 1) & DECL_SLOT_MASK;
        }
        return null;  // table full (shouldn't happen)
    }

    private ConstantInfo readDecl(int offset) {
        long off = Integer.toUnsignedLong(offset);
        byte ciTag = declDataSeg.get(ValueLayout.JAVA_BYTE, /* byte always aligned */ off); off++;
        int nameId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
        int typeExprId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
        int valueExprId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
        int hints = declDataSeg.get(INT_UNALIGNED, off); off += 4;
        byte safety = declDataSeg.get(ValueLayout.JAVA_BYTE, /* byte always aligned */ off); off++;
        byte flags = declDataSeg.get(ValueLayout.JAVA_BYTE, /* byte always aligned */ off); off++;
        // flags: bit 0=isRec, bit 1=isReflexive, bit 2=isUnsafe, bit 3=isK

        // Univ params
        int numUnivParams = declDataSeg.get(SHORT_UNALIGNED, off) & 0xFFFF; off += 2;
        Object[] univParams = new Object[numUnivParams];
        for (int i = 0; i < numUnivParams; i++) {
            int upId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
            univParams[i] = names[upId];
        }

        Name ciName = names[nameId];
        Expr type = resolveExpr(typeExprId);
        Expr value = valueExprId >= 0 ? resolveExpr(valueExprId) : null;

        switch (ciTag) {
            case ConstantInfo.AXIOM:
                return ConstantInfo.mkAxiom(ciName, univParams, type, (flags & 4) != 0);

            case ConstantInfo.DEF: {
                int numAll = declDataSeg.get(SHORT_UNALIGNED, off) & 0xFFFF; off += 2;
                Object[] all = new Object[numAll];
                for (int i = 0; i < numAll; i++) {
                    int allId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                    all[i] = names[allId];
                }
                return ConstantInfo.mkDef(ciName, univParams, type, value, hints, safety, all);
            }

            case ConstantInfo.THM: {
                int numAll = declDataSeg.get(SHORT_UNALIGNED, off) & 0xFFFF; off += 2;
                Object[] all = new Object[numAll];
                for (int i = 0; i < numAll; i++) {
                    int allId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                    all[i] = names[allId];
                }
                return ConstantInfo.mkThm(ciName, univParams, type, value, all);
            }

            case ConstantInfo.OPAQUE: {
                int numAll = declDataSeg.get(SHORT_UNALIGNED, off) & 0xFFFF; off += 2;
                Object[] all = new Object[numAll];
                for (int i = 0; i < numAll; i++) {
                    int allId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                    all[i] = names[allId];
                }
                return ConstantInfo.mkOpaque(ciName, univParams, type, value, all, (flags & 4) != 0);
            }

            case ConstantInfo.QUOT:
                return ConstantInfo.mkQuot(ciName, univParams, type, null);

            case ConstantInfo.INDUCT: {
                int numParams = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                int numIndices = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                int numNested = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                int numAll = declDataSeg.get(SHORT_UNALIGNED, off) & 0xFFFF; off += 2;
                Object[] all = new Object[numAll];
                for (int i = 0; i < numAll; i++) {
                    int allId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                    all[i] = names[allId];
                }
                int numCtors = declDataSeg.get(SHORT_UNALIGNED, off) & 0xFFFF; off += 2;
                Name[] ctors = new Name[numCtors];
                for (int i = 0; i < numCtors; i++) {
                    int ctorId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                    ctors[i] = names[ctorId];
                }
                return ConstantInfo.mkInduct(ciName, univParams, type,
                    numParams, numIndices, all, ctors, numNested,
                    (flags & 1) != 0, (flags & 2) != 0, (flags & 4) != 0);
            }

            case ConstantInfo.CTOR: {
                int inductNameId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                int cidx = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                int numParams = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                int numFields = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                return ConstantInfo.mkCtor(ciName, univParams, type,
                    names[inductNameId], cidx, numParams, numFields, (flags & 4) != 0);
            }

            case ConstantInfo.RECURSOR: {
                int numParams = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                int numIndices = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                int numMotives = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                int numMinors = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                int numAll = declDataSeg.get(SHORT_UNALIGNED, off) & 0xFFFF; off += 2;
                Object[] all = new Object[numAll];
                for (int i = 0; i < numAll; i++) {
                    int allId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                    all[i] = names[allId];
                }
                int numRules = declDataSeg.get(SHORT_UNALIGNED, off) & 0xFFFF; off += 2;
                ConstantInfo.RecursorRule[] rules = new ConstantInfo.RecursorRule[numRules];
                for (int i = 0; i < numRules; i++) {
                    int ctorNameId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                    int nfields = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                    int rhsExprId = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                    rules[i] = new ConstantInfo.RecursorRule(names[ctorNameId], nfields, resolveExpr(rhsExprId));
                }
                int majorIdx = declDataSeg.get(INT_UNALIGNED, off); off += 4;
                ConstantInfo ci = ConstantInfo.mkRecursor(ciName, univParams, type,
                    all, numParams, numIndices, numMotives, numMinors, rules,
                    (flags & 8) != 0, (flags & 4) != 0);
                // majorIdx is numParams + numMotives (already encoded in those fields)
                return ci;
            }

            default:
                throw new RuntimeException("Unknown decl tag: " + ciTag);
        }
    }

    // ================================================================
    // Env adapter — creates an Env backed by this FlatStore
    // ================================================================

    /**
     * Create an Env that uses this FlatStore for lookups.
     * Much faster than PSS-backed lookup.
     */
    public Env createEnv() {
        Env env = new Env();
        FlatStore self = this;
        env.setExternalLookup(new clojure.lang.AFn() {
            @Override
            public Object invoke(Object nameObj) {
                if (nameObj instanceof Name) {
                    return self.lookupDecl((Name) nameObj);
                }
                return null;
            }
        }, declOrder.length);
        return env;
    }

    // ================================================================
    // Loading helper files into memory
    // ================================================================

    /**
     * Load names from flat file.
     * Format: 4 bytes count, then for each: 1 byte tag, then:
     *   STR: 4 bytes prefix-id, 2 bytes strlen, N bytes UTF-8
     *   NUM: 4 bytes prefix-id, 8 bytes number
     *   ANONYMOUS: nothing
     */
    private static Name[] loadNames(Path path) throws IOException {
        byte[] data = Files.readAllBytes(path);
        java.nio.ByteBuffer bb = java.nio.ByteBuffer.wrap(data);
        int count = bb.getInt();
        Name[] names = new Name[count];
        for (int i = 0; i < count; i++) {
            byte tag = bb.get();
            switch (tag) {
                case Name.ANONYMOUS:
                    names[i] = Name.ANONYMOUS_NAME;
                    break;
                case Name.STR: {
                    int prefixId = bb.getInt();
                    int len = bb.getShort() & 0xFFFF;
                    byte[] strBytes = new byte[len];
                    bb.get(strBytes);
                    Name prefix = prefixId >= 0 ? names[prefixId] : Name.ANONYMOUS_NAME;
                    names[i] = Name.mkStr(prefix, new String(strBytes, StandardCharsets.UTF_8));
                    break;
                }
                case Name.NUM: {
                    int prefixId = bb.getInt();
                    long num = bb.getLong();
                    Name prefix = prefixId >= 0 ? names[prefixId] : Name.ANONYMOUS_NAME;
                    names[i] = Name.mkNum(prefix, num);
                    break;
                }
                default:
                    throw new IOException("Unknown name tag: " + tag);
            }
        }
        return names;
    }

    /**
     * Load levels from flat file.
     * Handles forward references (child ID > current ID) via recursive resolution.
     * Format: 4 bytes count, then for each: 1 byte tag, then:
     *   ZERO: nothing
     *   SUCC: 4 bytes child-id
     *   MAX/IMAX: 4 bytes lhs-id, 4 bytes rhs-id
     *   PARAM: 4 bytes name-id
     */
    private static Level[] loadLevels(Path path, Name[] names) throws IOException {
        byte[] data = Files.readAllBytes(path);
        java.nio.ByteBuffer bb = java.nio.ByteBuffer.wrap(data);
        int count = bb.getInt();

        // First pass: read raw records
        byte[] tags = new byte[count];
        int[] arg0 = new int[count];
        int[] arg1 = new int[count];
        for (int i = 0; i < count; i++) {
            tags[i] = bb.get();
            switch (tags[i]) {
                case Level.ZERO:
                    break;
                case Level.SUCC:
                    arg0[i] = bb.getInt();
                    break;
                case Level.MAX:
                case Level.IMAX:
                    arg0[i] = bb.getInt();
                    arg1[i] = bb.getInt();
                    break;
                case Level.PARAM:
                    arg0[i] = bb.getInt();
                    break;
                default:
                    throw new IOException("Unknown level tag: " + tags[i] + " at index " + i);
            }
        }

        // Second pass: resolve with recursive forward reference handling
        Level[] levels = new Level[count];
        for (int i = 0; i < count; i++) {
            if (levels[i] == null) {
                resolveLevel(i, tags, arg0, arg1, levels, names);
            }
        }
        return levels;
    }

    private static Level resolveLevel(int idx, byte[] tags, int[] arg0, int[] arg1,
                                       Level[] levels, Name[] names) {
        if (levels[idx] != null) return levels[idx];
        Level result;
        switch (tags[idx]) {
            case Level.ZERO:
                result = Level.ZERO_LEVEL;
                break;
            case Level.SUCC:
                result = Level.succ(resolveLevel(arg0[idx], tags, arg0, arg1, levels, names));
                break;
            case Level.MAX:
                result = Level.max(
                    resolveLevel(arg0[idx], tags, arg0, arg1, levels, names),
                    resolveLevel(arg1[idx], tags, arg0, arg1, levels, names));
                break;
            case Level.IMAX:
                result = Level.imax(
                    resolveLevel(arg0[idx], tags, arg0, arg1, levels, names),
                    resolveLevel(arg1[idx], tags, arg0, arg1, levels, names));
                break;
            case Level.PARAM:
                result = Level.param(names[arg0[idx]]);
                break;
            default:
                result = Level.ZERO_LEVEL;
        }
        levels[idx] = result;
        return result;
    }

    /**
     * Load declaration order from flat file.
     * Format: 4 bytes count, then for each: 2 bytes strlen, N bytes UTF-8
     */
    /**
     * Load decl name IDs from flat file.
     * Format: 4 bytes count, then count × 4 bytes (native-endian int32).
     */
    private static int[] loadDeclNameIds(Path path) throws IOException {
        byte[] data = Files.readAllBytes(path);
        java.nio.ByteBuffer bb = java.nio.ByteBuffer.wrap(data);
        bb.order(java.nio.ByteOrder.nativeOrder());
        int count = bb.getInt();
        int[] ids = new int[count];
        for (int i = 0; i < count; i++) {
            ids[i] = bb.getInt();
        }
        return ids;
    }

    private static String[] loadDeclOrder(Path path) throws IOException {
        byte[] data = Files.readAllBytes(path);
        java.nio.ByteBuffer bb = java.nio.ByteBuffer.wrap(data);
        int count = bb.getInt();
        String[] order = new String[count];
        for (int i = 0; i < count; i++) {
            int len = bb.getShort() & 0xFFFF;
            byte[] strBytes = new byte[len];
            bb.get(strBytes);
            order[i] = new String(strBytes, StandardCharsets.UTF_8);
        }
        return order;
    }
}
