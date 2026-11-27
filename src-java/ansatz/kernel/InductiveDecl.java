package ansatz.kernel;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * A mutual inductive declaration — Lean's {@code inductive_decl} (declaration.h): universe
 * parameters, the number of shared parameters, the safety flag and the ordered types, each
 * with its ordered constructors. This is everything the kernel takes as input; every
 * {@link ConstantInfo} of the block (types, constructors, recursors) is generated from it by
 * {@link AddInductive#add}. Immutable.
 */
public final class InductiveDecl {
    /** Lean's {@code constructor}: a name and a type. */
    public static final class Constructor {
        public final Name name;
        public final Expr type;

        public Constructor(Name name, Expr type) {
            if (name == null || type == null) throw new IllegalArgumentException("constructor needs a name and a type");
            this.name = name;
            this.type = type;
        }
    }

    /** Lean's {@code inductive_type}: a name, a type and the ordered constructors. */
    public static final class Type {
        public final Name name;
        public final Expr type;
        public final List<Constructor> constructors;

        public Type(Name name, Expr type, List<Constructor> constructors) {
            if (name == null || type == null || constructors == null)
                throw new IllegalArgumentException("inductive type needs a name, a type and constructors");
            this.name = name;
            this.type = type;
            this.constructors = Collections.unmodifiableList(Arrays.asList(constructors.toArray(new Constructor[0])));
        }
    }

    private final Object[] levelParams;
    public final int numParams;
    public final boolean isUnsafe;
    public final List<Type> types;

    public InductiveDecl(Object[] levelParams, int numParams, boolean isUnsafe, List<Type> types) {
        if (levelParams == null || types == null) throw new IllegalArgumentException("inductive declaration needs level parameters and types");
        if (numParams < 0) throw new IllegalArgumentException("invalid inductive datatype, negative number of parameters");
        for (Object lp : levelParams)
            if (!(lp instanceof Name)) throw new IllegalArgumentException("universe parameter must be a Name: " + lp);
        this.levelParams = levelParams.clone();
        this.numParams = numParams;
        this.isUnsafe = isUnsafe;
        this.types = Collections.unmodifiableList(Arrays.asList(types.toArray(new Type[0])));
    }

    /** The universe parameter names (a copy). */
    public Object[] levelParams() {
        return levelParams.clone();
    }

    int numLevelParams() {
        return levelParams.length;
    }

    Name levelParam(int i) {
        return (Name) levelParams[i];
    }
}
