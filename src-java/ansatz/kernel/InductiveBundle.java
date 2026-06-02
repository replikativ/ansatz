package ansatz.kernel;

import java.util.HashMap;

/**
 * Unified representation for a mutual inductive declaration bundle.
 *
 * <p>This type is used for both the original imported/generated declaration and
 * the auxiliary declaration produced by nested inductive elimination.
 * Lean uses one declaration language and transforms it into another declaration
 * of the same kind; we mirror that structure here instead of introducing a
 * separate aux-only bundle type.
 */
public final class InductiveBundle {
    public final Object[] levelParams;
    public final int numParams;
    public final boolean isUnsafe;

    public final ConstantInfo[] inductives;
    public final ConstantInfo[] ctors;
    public final ConstantInfo[] recursors;

    public InductiveBundle(Object[] levelParams, int numParams, boolean isUnsafe,
            ConstantInfo[] inductives, ConstantInfo[] ctors, ConstantInfo[] recursors) {
        this.levelParams = levelParams != null ? levelParams : new Object[0];
        this.numParams = numParams;
        this.isUnsafe = isUnsafe;
        this.inductives = inductives != null ? inductives : new ConstantInfo[0];
        this.ctors = ctors != null ? ctors : new ConstantInfo[0];
        this.recursors = recursors != null ? recursors : new ConstantInfo[0];
    }

    public boolean isEmpty() {
        return inductives.length == 0 && ctors.length == 0 && recursors.length == 0;
    }

    public boolean hasNestedInductives() {
        for (ConstantInfo ind : inductives) {
            if (ind != null && ind.numNested > 0) {
                return true;
            }
        }
        return false;
    }

    public Object[] allNames() {
        if (inductives.length == 0 || inductives[0] == null || inductives[0].all == null) {
            Object[] names = new Object[inductives.length];
            for (int i = 0; i < inductives.length; i++) {
                names[i] = inductives[i].name;
            }
            return names;
        }
        return inductives[0].all;
    }

    public HashMap<Name, ConstantInfo> inductiveMap() {
        HashMap<Name, ConstantInfo> out = new HashMap<>(inductives.length * 2 + 1);
        for (ConstantInfo ci : inductives) {
            if (ci != null) out.put(ci.name, ci);
        }
        return out;
    }

    public HashMap<Name, ConstantInfo> ctorMap() {
        HashMap<Name, ConstantInfo> out = new HashMap<>(ctors.length * 2 + 1);
        for (ConstantInfo ci : ctors) {
            if (ci != null) out.put(ci.name, ci);
        }
        return out;
    }

    public HashMap<Name, ConstantInfo> recursorMap() {
        HashMap<Name, ConstantInfo> out = new HashMap<>(recursors.length * 2 + 1);
        for (ConstantInfo ci : recursors) {
            if (ci != null) out.put(ci.name, ci);
        }
        return out;
    }
}
