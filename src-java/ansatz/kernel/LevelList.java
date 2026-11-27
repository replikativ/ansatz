// Ansatz kernel — immutable universe-argument list of a constant.

package ansatz.kernel;

/**
 * The universe arguments a CONST node stores. Expression fields are public, so the list a node
 * exposes must not be writable: a caller changing a looked-up constant's universe would change
 * an expression the caches already hold (its hash and every cached judgment about it). This is
 * an unmodifiable List over an array the node owns; the kernel reads the array directly.
 */
public final class LevelList extends java.util.AbstractList<Object> implements java.util.RandomAccess {
    static final LevelList EMPTY = new LevelList(new Object[0]);

    final Object[] arr;   // owned, never written after construction

    private LevelList(Object[] arr) { this.arr = arr; }

    /** Wrap an array the caller hands over and never writes again. */
    static LevelList owned(Object[] arr) { return arr.length == 0 ? EMPTY : new LevelList(arr); }

    @Override public Object get(int i) { return arr[i]; }
    @Override public int size() { return arr.length; }
    @Override public Object[] toArray() { return arr.clone(); }
}
