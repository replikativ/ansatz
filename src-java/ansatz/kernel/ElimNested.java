package ansatz.kernel;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * Nested inductive elimination — Lean's {@code elim_nested_inductive_fn} and
 * {@code elim_nested_inductive_result} (inductive.cpp).
 *
 * <p>Every nested occurrence {@code I Ds is} — {@code I} a previously declared inductive whose
 * parametric arguments {@code Ds} mention a type being declared — is replaced by
 * {@code Iaux As is}, where {@code Iaux} is a copy of {@code I} specialised to {@code Ds} and added
 * to the mutual block (with copies of {@code I}'s mutual siblings). Discovery is syntactic and
 * runs on every declaration; the copies' constructors are processed in turn, so nesting through
 * a container that uses its parameter negatively is exposed to the positivity check.
 * {@link #restore} maps auxiliary types, constructors and recursors back.
 */
final class ElimNested {
    static final Name NESTED = Name.fromString("_nested");

    private final Env env;
    private final InductiveDecl decl;
    private final int nparams;
    private final Object[] lvls;
    private final LocalCtx paramsLctx = new LocalCtx(1L << 40);
    private final ArrayList<Expr> params = new ArrayList<>();
    /** (I Ds over {@link #params}, auxiliary name), in creation order — Lean's m_nested_aux. */
    private final ArrayList<Map.Entry<LeanExprKey, Name>> nestedAux = new ArrayList<>();
    private final ArrayList<MutType> newTypes = new ArrayList<>();
    private final LocalCtx ctorLctx = new LocalCtx(1L << 41);
    private int nextIdx = 1;

    private static final class MutType {
        final Name name;
        final Expr type;
        List<InductiveDecl.Constructor> ctors;

        MutType(Name name, Expr type, List<InductiveDecl.Constructor> ctors) {
            this.name = name;
            this.type = type;
            this.ctors = ctors;
        }
    }

    /** The auxiliary declaration and what {@link #restore} needs. */
    static final class Result {
        final InductiveDecl auxDecl;
        final List<Expr> params;
        final LocalCtx paramsLctx;
        /** auxiliary type name → the nested application {@code I Ds} it stands for, over {@link #params}. */
        final LinkedHashMap<Name, Expr> aux2nested;

        Result(InductiveDecl auxDecl, List<Expr> params, LocalCtx paramsLctx, LinkedHashMap<Name, Expr> aux2nested) {
            this.auxDecl = auxDecl;
            this.params = params;
            this.paramsLctx = paramsLctx;
            this.aux2nested = aux2nested;
        }

        /** Lean's get_nested_if_aux_constructor: the nested application and auxiliary type of an auxiliary constructor. */
        private Map.Entry<Expr, Name> nestedIfAuxConstructor(Env auxEnv, Name c) {
            ConstantInfo info = auxEnv.lookup(c);
            if (info == null || !info.isCtor()) return null;
            Expr nested = aux2nested.get(info.inductName);
            return nested == null ? null : Map.entry(nested, info.inductName);
        }

        /** Lean's restore_constructor_name. */
        Name restoreConstructorName(Env auxEnv, Name ctor) {
            Map.Entry<Expr, Name> p = nestedIfAuxConstructor(auxEnv, ctor);
            if (p == null)
                throw new RuntimeException("failed to restore nested inductive types, '" + ctor + "' is not a constructor of an auxiliary type");
            Expr I = AddInductive.appFn(p.getKey());
            if (I.tag != Expr.CONST)
                throw new RuntimeException("failed to restore nested inductive types, nested occurrence is not an inductive type application");
            return ctor.replacePrefix(p.getValue(), (Name) I.o0);
        }

        /** Lean's restore_nested: under the parameter binders, auxiliary types, constructors and recursors are mapped back. */
        Expr restore(Expr e, Env auxEnv, Map<Name, Name> auxRecNames) {
            LocalCtx lctx = new LocalCtx(1L << 42);
            ArrayList<Expr> as = new ArrayList<>();
            boolean pi = e.tag == Expr.FORALL;
            for (int i = 0; i < params.size(); i++) {
                if (e.tag != Expr.FORALL && e.tag != Expr.LAM)
                    throw new RuntimeException("failed to restore nested inductive types, fewer binders than parameters");
                as.add(lctx.mkLocalDecl(e.o0, (Expr) e.o1, e.o3));
                e = Reducer.instantiate1((Expr) e.o2, as.get(i));
            }
            Expr[] asArr = as.toArray(new Expr[0]);
            long[] paramIds = AddInductive.fvarIds(params);
            Function<Expr, Expr> overParams = nested ->
                Reducer.instantiateRev(Reducer.abstractFvars(nested, paramIds.length, paramIds), asArr.length, asArr, 0);
            e = AddInductive.replace(e, t -> {
                if (t.tag == Expr.CONST) {
                    Name rec = auxRecNames.get((Name) t.o0);
                    if (rec != null) return Expr.mkConstOwned(rec, t.o1);
                }
                Expr fn = AddInductive.appFn(t);
                if (fn.tag != Expr.CONST) return null;
                Expr nested = aux2nested.get((Name) fn.o0);
                if (nested != null) {
                    Expr[] args = AddInductive.appArgs(t);
                    if (args.length < params.size())
                        throw new RuntimeException("failed to restore nested inductive types, auxiliary type is not applied to all parameters");
                    return AddInductive.mkApp(overParams.apply(nested), args, params.size(), args.length);
                }
                Map.Entry<Expr, Name> r = nestedIfAuxConstructor(auxEnv, (Name) fn.o0);
                if (r != null) {
                    Expr[] args = AddInductive.appArgs(t);
                    if (args.length < params.size())
                        throw new RuntimeException("failed to restore nested inductive types, auxiliary constructor is not applied to all parameters");
                    Expr newNested = overParams.apply(r.getKey());
                    Expr I = AddInductive.appFn(newNested);
                    if (I.tag != Expr.CONST)
                        throw new RuntimeException("failed to restore nested inductive types, nested occurrence is not an inductive type application");
                    Name newFn = ((Name) fn.o0).replacePrefix(r.getValue(), (Name) I.o0);
                    Expr[] iArgs = AddInductive.appArgs(newNested);
                    Expr out = AddInductive.mkApp(Expr.mkConstOwned(newFn, I.o1), iArgs, 0, iArgs.length);
                    return AddInductive.mkApp(out, args, params.size(), args.length);
                }
                return null;
            });
            return pi ? lctx.mkPi(as, e) : lctx.mkLambda(as, e);
        }
    }

    ElimNested(Env env, InductiveDecl decl) {
        this.env = env;
        this.decl = decl;
        this.nparams = decl.numParams;
        this.lvls = AddInductive.paramLevels(decl);
    }

    Result run() {
        for (InductiveDecl.Type t : decl.types) newTypes.add(new MutType(t.name, t.type, t.constructors));
        if (newTypes.isEmpty())
            throw new RuntimeException("invalid empty (mutual) inductive datatype declaration, it must contain at least one inductive type.");
        getParams(newTypes.get(0).type, paramsLctx, params);
        for (int qhead = 0; qhead < newTypes.size(); qhead++) {
            MutType indType = newTypes.get(qhead);
            ArrayList<InductiveDecl.Constructor> newCtors = new ArrayList<>();
            for (InductiveDecl.Constructor c : indType.ctors) {
                // the parameters are re-created per constructor to keep its binder infos
                ArrayList<Expr> as = new ArrayList<>();
                Expr body = getParams(c.type, ctorLctx, as);
                Expr replaced = AddInductive.replace(body, e -> replaceIfNested(as, e));
                newCtors.add(new InductiveDecl.Constructor(c.name, ctorLctx.mkPi(as, replaced)));
            }
            indType.ctors = newCtors;
        }
        ArrayList<InductiveDecl.Type> types = new ArrayList<>();
        for (MutType t : newTypes) types.add(new InductiveDecl.Type(t.name, t.type, t.ctors));
        LinkedHashMap<Name, Expr> aux2nested = new LinkedHashMap<>();
        for (Map.Entry<LeanExprKey, Name> p : nestedAux) aux2nested.put(p.getValue(), p.getKey().expr);
        return new Result(new InductiveDecl(decl.levelParams(), nparams, decl.isUnsafe, types),
                          params, paramsLctx, aux2nested);
    }

    private Expr getParams(Expr type, LocalCtx lctx, List<Expr> out) {
        for (int i = 0; i < nparams; i++) {
            if (type.tag != Expr.FORALL)
                throw new RuntimeException("invalid inductive datatype declaration, incorrect number of parameters");
            Expr p = lctx.mkLocalDecl(type.o0, (Expr) type.o1, type.o3);
            out.add(p);
            type = Reducer.instantiate1((Expr) type.o2, p);
        }
        return type;
    }

    private boolean isNewType(Name n) {
        for (MutType t : newTypes) if (t.name.equals(n)) return true;
        return false;
    }

    /** Lean's is_nested_inductive_app: the inductive {@code I} when {@code e = I Ds is} nests a new type in {@code Ds}. */
    private ConstantInfo isNestedInductiveApp(Expr e) {
        if (e.tag != Expr.APP) return null;
        Expr fn = AddInductive.appFn(e);
        if (fn.tag != Expr.CONST) return null;
        ConstantInfo info = env.lookup((Name) fn.o0);
        if (info == null || !info.isInduct()) return null;
        Expr[] args = AddInductive.appArgs(e);
        if (info.numParams > args.length) return null;
        boolean nested = false, looseBVars = false;
        for (int i = 0; i < info.numParams; i++) {
            if (args[i].bvarRange() > 0) looseBVars = true;
            if (AddInductive.find(args[i], t -> t.tag == Expr.CONST && isNewType((Name) t.o0))) nested = true;
        }
        if (!nested) return null;
        if (looseBVars)
            throw new RuntimeException("invalid nested inductive datatype '" + fn.o0
                + "', nested inductive datatypes parameters cannot contain local variables.");
        return info;
    }

    private Expr instantiatePiParams(Expr e, int n, Expr[] args) {
        for (int i = 0; i < n; i++) {
            if (e.tag != Expr.FORALL) throw new RuntimeException("invalid nested inductive datatype, ill-formed declaration");
            e = (Expr) e.o2;
        }
        return Reducer.instantiateRev(e, n, args, 0);
    }

    /** Replace the constructor's own parameters {@code as} by the declaration's {@link #params}. */
    private Expr replaceParams(Expr e, List<Expr> as) {
        long[] ids = AddInductive.fvarIds(as);
        return Reducer.instantiateRev(Reducer.abstractFvars(e, ids.length, ids), params.size(), params.toArray(new Expr[0]), 0);
    }

    private Name mkUniqueName(Name n) {
        while (true) {
            Name r = n.appendAfter(nextIdx++);
            if (env.lookup(r) == null) return r;
        }
    }

    private Expr auxApp(Name aux, List<Expr> as, Expr[] args, int from) {
        Expr r = Expr.mkConstOwned(aux, lvls);
        for (Expr a : as) r = Expr.app(r, a);
        return AddInductive.mkApp(r, args, from, args.length);
    }

    /** Lean's replace_if_nested: {@code I Ds is} becomes {@code Iaux As is}. */
    private Expr replaceIfNested(List<Expr> as, Expr e) {
        ConstantInfo iVal = isNestedInductiveApp(e);
        if (iVal == null) return null;
        Expr[] args = AddInductive.appArgs(e);
        Expr fn = AddInductive.appFn(e);
        Name iName = (Name) fn.o0;
        Object[] iLvls = Reducer.constLevels(fn);
        int iNparams = iVal.numParams;
        LeanExprKey key = new LeanExprKey(replaceParams(AddInductive.mkApp(fn, args, 0, iNparams), as));
        for (Map.Entry<LeanExprKey, Name> p : nestedAux)
            if (p.getKey().equals(key)) return auxApp(p.getValue(), as, args, iNparams);
        Expr result = null;
        for (Object jObj : iVal.all) {
            Name jName = (Name) jObj;
            ConstantInfo jInfo = env.lookupOrThrow(jName);
            if (!jInfo.isInduct()) throw new RuntimeException("invalid nested inductive datatype, '" + jName + "' is not an inductive type");
            Name auxJName = mkUniqueName(AddInductive.concat(NESTED, jName));
            Expr jAs = AddInductive.mkApp(Expr.mkConstOwned(jName, iLvls), args, 0, iNparams);
            Expr auxJType = instantiatePiParams(instantiateLParams(jInfo.type, jInfo.levelParams, iLvls), iNparams, args);
            nestedAux.add(Map.entry(new LeanExprKey(replaceParams(jAs, as)), auxJName));
            if (jName.equals(iName)) result = auxApp(auxJName, as, args, iNparams);
            ArrayList<InductiveDecl.Constructor> auxCtors = new ArrayList<>();
            for (Name jCtorName : jInfo.ctors) {
                ConstantInfo jCtor = env.lookupOrThrow(jCtorName);
                Expr t = instantiatePiParams(instantiateLParams(jCtor.type, jCtor.levelParams, iLvls), iNparams, args);
                // still mentions J; fixed when this auxiliary type is processed
                auxCtors.add(new InductiveDecl.Constructor(jCtorName.replacePrefix(jName, auxJName), ctorLctx.mkPi(as, t)));
            }
            newTypes.add(new MutType(auxJName, ctorLctx.mkPi(as, auxJType), auxCtors));
        }
        return result;
    }

    private static Expr instantiateLParams(Expr e, Object[] ps, Object[] ls) {
        if (ps.length != ls.length)
            throw new RuntimeException("invalid nested inductive datatype, incorrect number of universe levels");
        if (ps.length == 0) return e;
        HashMap<Object, Level> subst = new HashMap<>();
        for (int i = 0; i < ps.length; i++) subst.put(ps[i], (Level) ls[i]);
        return Reducer.instantiateLevelParams(e, subst);
    }
}
