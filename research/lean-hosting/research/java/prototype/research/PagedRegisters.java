package prototype.research;

import java.util.Arrays;

/** Research only. Private mutable bank, read-only captures, no guest RC effects. */
public final class PagedRegisters {
    private static final int SHIFT = 4;
    private static final int SIZE = 1 << SHIFT;
    private final int width;
    private final Object unbound;
    private final Object[][] pages;
    private final int[] owners; // null on read-only captures
    private int epoch = 1;
    private PagedRegisters lastSnapshot;

    public PagedRegisters(int width, Object unbound) {
        this(width, unbound, new Object[(width + SIZE - 1) >>> SHIFT][],
             new int[(width + SIZE - 1) >>> SHIFT]);
    }

    private PagedRegisters(int width, Object unbound, Object[][] pages, int[] owners) {
        this.width = width;
        this.unbound = unbound;
        this.pages = pages;
        this.owners = owners;
    }

    public int width() { return width; }

    private void check(int slot) {
        if (slot < 0 || slot >= width)
            throw new ArrayIndexOutOfBoundsException("Index " + slot + " out of bounds for length " + width);
    }

    public Object get(int slot) {
        check(slot);
        Object[] page = pages[slot >>> SHIFT];
        return page == null ? unbound : page[slot & (SIZE - 1)];
    }

    public void set(int slot, Object value) {
        check(slot);
        if (owners == null) throw new IllegalStateException("Read-only register capture");
        int index = slot >>> SHIFT;
        Object[] page = pages[index];
        if (page == null) {
            page = new Object[Math.min(SIZE, width - (index << SHIFT))];
            Arrays.fill(page, unbound);
            pages[index] = page;
            owners[index] = epoch;
        } else if (owners[index] != epoch) {
            pages[index] = page = page.clone();
            owners[index] = epoch;
        }
        page[slot & (SIZE - 1)] = value;
        lastSnapshot = null;
    }

    public PagedRegisters snapshot() {
        if (owners == null) return this;
        if (lastSnapshot == null) {
            lastSnapshot = new PagedRegisters(width, unbound, pages.clone(), null);
            if (epoch == Integer.MAX_VALUE) {
                Arrays.fill(owners, 0);
                epoch = 1;
            } else ++epoch;
        }
        return lastSnapshot;
    }

    public PagedRegisters fork() {
        PagedRegisters immutable = snapshot();
        return new PagedRegisters(width, unbound, immutable.pages.clone(), new int[pages.length]);
    }

    public void clear() {
        if (owners == null) throw new IllegalStateException("Read-only register capture");
        Arrays.fill(pages, null);
        Arrays.fill(owners, 0);
        epoch = 1;
        lastSnapshot = null;
    }

    public Object[] toArray() {
        Object[] result = new Object[width];
        Arrays.fill(result, unbound);
        for (int i = 0; i < pages.length; ++i)
            if (pages[i] != null) System.arraycopy(pages[i], 0, result, i << SHIFT, pages[i].length);
        return result;
    }
}
