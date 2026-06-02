package ansatz.kernel;

final class LocalDecl {
    final long id;
    final Object name;
    final Expr type;
    final Object binderInfo;
    final Expr fvar;

    LocalDecl(long id, Object name, Expr type, Object binderInfo) {
        this.id = id;
        this.name = name;
        this.type = type;
        this.binderInfo = binderInfo;
        this.fvar = Expr.fvar(id);
    }
}
