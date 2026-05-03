package ansatz.kernel;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;

/**
 * Lean-style nested inductive elimination.
 *
 * <p>This pass now performs the first real transformation stage instead of
 * throwing immediately for nested bundles: it discovers nested occurrences,
 * creates explicit auxiliary inductive types and constructors, rewrites
 * constructor bodies to refer to those auxiliaries, and records the metadata
 * needed for restoration. Bundle admission still remains conservative until
 * restoration/comparison is wired into the checker.
 */
public final class NestedInductiveEliminator {
    private NestedInductiveEliminator() {}

    public static NestedElimResult eliminate(Env env, InductiveBundle bundle) {
        if (bundle == null) {
            throw new RuntimeException("invalid inductive bundle: null");
        }
        if (!bundle.hasNestedInductives()) {
            return new NestedElimResult(
                bundle,
                new Expr[0],
                new HashMap<>(),
                new HashMap<>(),
                new HashMap<>(),
                new ArrayList<>(),
                new ArrayList<>());
        }
        return new Eliminator(env, bundle).run();
    }

    private static final class ParamBinder {
        final long fvarId;
        final Object name;
        final Expr type;
        final Object binderInfo;

        ParamBinder(long fvarId, Object name, Expr type, Object binderInfo) {
            this.fvarId = fvarId;
            this.name = name;
            this.type = type;
            this.binderInfo = binderInfo;
        }
    }

    private static final class ParamScope {
        final ParamBinder[] binders;
        final Expr[] fvars;
        final Expr body;

        ParamScope(ParamBinder[] binders, Expr[] fvars, Expr body) {
            this.binders = binders;
            this.fvars = fvars;
            this.body = body;
        }
    }

    private static final class TypeSpec {
        final ConstantInfo baseInductive;
        final Name name;
        Expr type;
        ConstantInfo[] ctors;

        TypeSpec(ConstantInfo baseInductive, Name name, Expr type, ConstantInfo[] ctors) {
            this.baseInductive = baseInductive;
            this.name = name;
            this.type = type;
            this.ctors = ctors;
        }
    }

    private static final class Eliminator {
        final Env env;
        final InductiveBundle bundle;
        final HashMap<Name, ConstantInfo> bundleCtorMap;
        final ArrayList<TypeSpec> newTypes = new ArrayList<>();
        final ArrayList<Name> newTypeNames = new ArrayList<>();
        final HashMap<Name, Expr> auxToNested = new HashMap<>();
        final HashMap<Name, Name> auxPrefixToRestoredPrefix = new HashMap<>();
        final ArrayList<Expr> nestedKeys = new ArrayList<>();
        final ArrayList<Name> auxNames = new ArrayList<>();
        final Expr[] params;
        final ParamBinder[] paramBinders;
        final Name mainName;
        final Object[] bundleLevelValues;
        final boolean bundleHasLevelParams;
        int nextAuxIdx = 1;
        long nextFVarId = 10_000_000L;

        Eliminator(Env env, InductiveBundle bundle) {
            this.env = env;
            this.bundle = bundle;
            this.bundleCtorMap = bundle.ctorMap();
            this.mainName = bundle.inductives[0].name;
            this.bundleLevelValues = mkBundleLevelValues(bundle.levelParams);
            this.bundleHasLevelParams = bundleLevelValues.length > 0;
            ParamScope globalParams = peelParams(bundle.inductives[0].type, bundle.numParams);
            this.params = globalParams.fvars;
            this.paramBinders = globalParams.binders;
            for (ConstantInfo ind : bundle.inductives) {
                ConstantInfo[] ctors = new ConstantInfo[ind.ctors.length];
                for (int i = 0; i < ind.ctors.length; i++) {
                    ConstantInfo ctor = bundleCtorMap.get(ind.ctors[i]);
                    if (ctor == null) {
                        throw new RuntimeException("invalid inductive bundle: missing constructor " + ind.ctors[i]);
                    }
                    ctors[i] = ctor;
                }
                newTypes.add(new TypeSpec(ind, ind.name, ind.type, ctors));
                newTypeNames.add(ind.name);
            }
        }

        NestedElimResult run() {
            int qhead = 0;
            while (qhead < newTypes.size()) {
                TypeSpec spec = newTypes.get(qhead);
                ConstantInfo[] newCtors = new ConstantInfo[spec.ctors.length];
                for (int i = 0; i < spec.ctors.length; i++) {
                    ConstantInfo ctor = spec.ctors[i];
                    ParamScope scope = peelParams(ctor.type, bundle.numParams);
                    Expr newBody = replaceAllNested(scope.fvars, scope.body, new IdentityHashMap<>());
                    Expr newType = buildForall(scope.binders, newBody);
                    newCtors[i] = ConstantInfo.mkCtor(
                        ctor.name,
                        bundle.levelParams,
                        newType,
                        ctor.inductName,
                        ctor.cidx,
                        ctor.numParams,
                        ctor.numFields,
                        ctor.isUnsafe);
                }
                spec.ctors = newCtors;
                qhead++;
            }

            Object[] all = new Object[newTypes.size()];
            for (int i = 0; i < newTypes.size(); i++) all[i] = newTypes.get(i).name;

            ConstantInfo[] inductives = new ConstantInfo[newTypes.size()];
            ArrayList<ConstantInfo> ctorList = new ArrayList<>();
            for (int i = 0; i < newTypes.size(); i++) {
                TypeSpec spec = newTypes.get(i);
                Name[] ctorNames = new Name[spec.ctors.length];
                for (int j = 0; j < spec.ctors.length; j++) {
                    ctorNames[j] = spec.ctors[j].name;
                    ctorList.add(spec.ctors[j]);
                }
                ConstantInfo base = spec.baseInductive;
                inductives[i] = ConstantInfo.mkInduct(
                    spec.name,
                    bundle.levelParams,
                    spec.type,
                    bundle.numParams,
                    base.numIndices,
                    all,
                    ctorNames,
                    0,
                    base.isRec,
                    base.isReflexive,
                    base.isUnsafe);
            }

            HashMap<Name, Name> auxRecToRestoredRec = new HashMap<>();
            Name mainRec = Name.mkStr(mainName, "rec");
            for (int i = 0; i < auxNames.size(); i++) {
                Name auxRec = Name.mkStr(auxNames.get(i), "rec");
                Name restoredRec = mainRec.appendAfter(i + 1);
                auxRecToRestoredRec.put(auxRec, restoredRec);
            }

            InductiveBundle auxBundle = new InductiveBundle(
                bundle.levelParams,
                bundle.numParams,
                bundle.isUnsafe,
                inductives,
                ctorList.toArray(new ConstantInfo[0]),
                new ConstantInfo[0]);

            return new NestedElimResult(
                auxBundle,
                params,
                auxToNested,
                auxRecToRestoredRec,
                auxPrefixToRestoredPrefix,
                nestedKeys,
                auxNames);
        }

        private Expr replaceAllNested(Expr[] localParams, Expr e, IdentityHashMap<Expr, Expr> visited) {
            Expr cached = visited.get(e);
            if (cached != null) return cached;
            Expr replaced = replaceIfNested(localParams, e);
            if (replaced != null) {
                visited.put(e, replaced);
                return replaced;
            }
            Expr result;
            switch (e.tag) {
                case Expr.APP: {
                    Expr fn = replaceAllNested(localParams, (Expr) e.o0, visited);
                    Expr arg = replaceAllNested(localParams, (Expr) e.o1, visited);
                    result = (fn == e.o0 && arg == e.o1) ? e : Expr.app(fn, arg);
                    break;
                }
                case Expr.FORALL: {
                    Expr type = replaceAllNested(localParams, (Expr) e.o1, visited);
                    Expr body = replaceAllNested(localParams, (Expr) e.o2, visited);
                    result = (type == e.o1 && body == e.o2) ? e : Expr.forall(e.o0, type, body, e.o3);
                    break;
                }
                case Expr.LAM: {
                    Expr type = replaceAllNested(localParams, (Expr) e.o1, visited);
                    Expr body = replaceAllNested(localParams, (Expr) e.o2, visited);
                    result = (type == e.o1 && body == e.o2) ? e : Expr.lam(e.o0, type, body, e.o3);
                    break;
                }
                case Expr.LET: {
                    Expr type = replaceAllNested(localParams, (Expr) e.o1, visited);
                    Expr val = replaceAllNested(localParams, (Expr) e.o2, visited);
                    Expr body = replaceAllNested(localParams, (Expr) e.o3, visited);
                    result = (type == e.o1 && val == e.o2 && body == e.o3) ? e : Expr.mkLet(e.o0, type, val, body);
                    break;
                }
                case Expr.MDATA: {
                    Expr inner = replaceAllNested(localParams, (Expr) e.o1, visited);
                    result = inner == e.o1 ? e : Expr.mdata(e.o0, inner);
                    break;
                }
                case Expr.PROJ: {
                    Expr inner = replaceAllNested(localParams, (Expr) e.o1, visited);
                    result = inner == e.o1 ? e : Expr.proj(e.o0, e.longVal, inner);
                    break;
                }
                default:
                    result = e;
            }
            visited.put(e, result);
            return result;
        }

        private Expr replaceIfNested(Expr[] localParams, Expr e) {
            NestedApp nested = isNestedInductiveApp(e);
            if (nested == null) return null;

            Expr keyWithLocalParams = mkApp(nested.headConst, nested.paramArgs, nested.iNumParams);
            Expr key = replaceParams(keyWithLocalParams, localParams);
            Name existing = findExistingAux(key);
            if (existing != null) {
                return mkAuxApp(existing, nested.headConst.o1, localParams, nested.indexArgs);
            }

            Expr result = null;
            Name[] group = nested.indInfo.all != null
                ? toNameArray(nested.indInfo.all)
                : new Name[] { nested.indName };
            for (Name jName : group) {
                ConstantInfo jInfo = env.lookup(jName);
                if (jInfo == null || !jInfo.isInduct()) continue;

                Expr jConst = Expr.mkConst(jName, nested.headConst.o1, nested.headConst.hasLevelParam());
                Expr jKeyWithLocalParams = mkApp(jConst, nested.paramArgs, nested.iNumParams);
                Expr jKey = replaceParams(jKeyWithLocalParams, localParams);

                Name auxName = mkUniqueAuxName(jName);
                auxToNested.put(auxName, jKey);
                auxPrefixToRestoredPrefix.put(auxName, jName);
                nestedKeys.add(jKey);
                auxNames.add(auxName);
                newTypeNames.add(auxName);

                Expr auxTypeBody = instantiateNestedLevels(jInfo.type, jInfo.levelParams, nested.headConst.o1);
                auxTypeBody = instantiatePiParams(auxTypeBody, nested.iNumParams, nested.paramArgs);
                Expr auxType = buildForall(paramBinders, auxTypeBody);

                Name[] ctorNames = jInfo.ctors != null ? jInfo.ctors : new Name[0];
                ConstantInfo[] auxCtors = new ConstantInfo[ctorNames.length];
                for (int i = 0; i < ctorNames.length; i++) {
                    ConstantInfo ctor = env.lookup(ctorNames[i]);
                    if (ctor == null) {
                        throw new RuntimeException("invalid nested inductive datatype, missing constructor " + ctorNames[i]);
                    }
                    Name auxCtorName = ctor.name.replacePrefix(jName, auxName);
                    Expr auxCtorBody = instantiateNestedLevels(ctor.type, ctor.levelParams, nested.headConst.o1);
                    auxCtorBody = instantiatePiParams(auxCtorBody, nested.iNumParams, nested.paramArgs);
                    Expr auxCtorType = buildForall(paramBinders, auxCtorBody);
                    auxCtors[i] = ConstantInfo.mkCtor(
                        auxCtorName,
                        bundle.levelParams,
                        auxCtorType,
                        auxName,
                        ctor.cidx,
                        bundle.numParams,
                        ctor.numFields,
                        ctor.isUnsafe);
                }
                newTypes.add(new TypeSpec(jInfo, auxName, auxType, auxCtors));

                if (jName.equals(nested.indName)) {
                    result = mkAuxApp(auxName, nested.headConst.o1, localParams, nested.indexArgs);
                }
            }
            return result;
        }

        private Name findExistingAux(Expr key) {
            for (Name auxName : auxNames) {
                Expr prev = auxToNested.get(auxName);
                if (prev != null && prev.equals(key)) return auxName;
            }
            return null;
        }

        private Name mkUniqueAuxName(Name base) {
            while (true) {
                Name candidate = Name.mkStr(base, "nested").appendAfter(nextAuxIdx++);
                if (env.lookup(candidate) != null) continue;
                boolean clash = false;
                for (TypeSpec spec : newTypes) {
                    if (spec.name.equals(candidate)) {
                        clash = true;
                        break;
                    }
                }
                if (!clash) return candidate;
            }
        }

        private Expr mkAuxApp(Name auxName, Object levels, Expr[] localParams, Expr[] indexArgs) {
            Expr result = Expr.mkConst(auxName, bundleLevelValues, bundleHasLevelParams);
            for (Expr p : localParams) result = Expr.app(result, p);
            for (Expr arg : indexArgs) result = Expr.app(result, arg);
            return result;
        }

        private ParamScope peelParams(Expr type, int nparams) {
            ParamBinder[] binders = new ParamBinder[nparams];
            Expr[] fvars = new Expr[nparams];
            Expr cur = type;
            for (int i = 0; i < nparams; i++) {
                if (cur.tag != Expr.FORALL) {
                    throw new RuntimeException("invalid nested inductive datatype, incorrect number of parameters");
                }
                long fvarId = nextFVarId++;
                binders[i] = new ParamBinder(fvarId, cur.o0, (Expr) cur.o1, cur.o3);
                fvars[i] = Expr.fvar(fvarId);
                cur = Reducer.instantiateRev((Expr) cur.o2, 1, new Expr[] { fvars[i] }, 0);
            }
            return new ParamScope(binders, fvars, cur);
        }

        private Expr buildForall(ParamBinder[] binders, Expr body) {
            long[] ids = new long[binders.length];
            for (int i = 0; i < binders.length; i++) ids[i] = binders[i].fvarId;
            Expr result = Reducer.abstractFvars(body, binders.length, ids);
            for (int i = binders.length - 1; i >= 0; i--) {
                Expr domain = Reducer.abstractFvars(binders[i].type, i, ids);
                result = Expr.forall(binders[i].name, domain, result, binders[i].binderInfo);
            }
            return result;
        }

        private Expr instantiatePiParams(Expr e, int nparams, Expr[] params) {
            Expr cur = e;
            for (int i = 0; i < nparams; i++) {
                if (cur.tag != Expr.FORALL) {
                    throw new RuntimeException("invalid nested inductive datatype, ill-formed declaration");
                }
                cur = (Expr) cur.o2;
            }
            return Reducer.instantiateRev(cur, nparams, params, 0);
        }

        private Expr instantiateNestedLevels(Expr e, Object[] levelParams, Object occurrenceLevelsObj) {
            Object[] occurrenceLevels;
            if (occurrenceLevelsObj instanceof Object[]) {
                occurrenceLevels = (Object[]) occurrenceLevelsObj;
            } else if (occurrenceLevelsObj == null) {
                occurrenceLevels = new Object[0];
            } else if (occurrenceLevelsObj instanceof java.util.List) {
                java.util.List<?> lst = (java.util.List<?>) occurrenceLevelsObj;
                occurrenceLevels = lst.toArray();
            } else if (occurrenceLevelsObj instanceof clojure.lang.IPersistentVector) {
                clojure.lang.IPersistentVector v = (clojure.lang.IPersistentVector) occurrenceLevelsObj;
                occurrenceLevels = new Object[v.count()];
                for (int i = 0; i < v.count(); i++) occurrenceLevels[i] = v.nth(i);
            } else {
                occurrenceLevels = new Object[0];
            }
            if (levelParams == null || levelParams.length == 0) return e;
            if (levelParams.length != occurrenceLevels.length) {
                throw new RuntimeException("invalid nested inductive datatype, level parameter arity mismatch");
            }
            HashMap<Object, Level> subst = new HashMap<>();
            for (int i = 0; i < levelParams.length; i++) {
                subst.put(levelParams[i], (Level) occurrenceLevels[i]);
            }
            return Reducer.instantiateLevelParams(e, subst);
        }

        private Expr replaceParams(Expr e, Expr[] localParams) {
            long[] localIds = new long[localParams.length];
            for (int i = 0; i < localParams.length; i++) localIds[i] = localParams[i].longVal;
            Expr abstracted = Reducer.abstractFvars(e, localParams.length, localIds);
            return Reducer.instantiateRev(abstracted, params.length, params, 0);
        }

        private NestedApp isNestedInductiveApp(Expr e) {
            if (e.tag != Expr.APP) return null;
            Expr head = getAppFn(e);
            if (head.tag != Expr.CONST) return null;
            Name indName = (Name) head.o0;
            if (containsName(newTypeNames, indName)) return null;
            ConstantInfo indInfo = env.lookup(indName);
            if (indInfo == null || !indInfo.isInduct()) return null;
            Expr[] args = getAppArgs(e);
            int iNumParams = indInfo.numParams;
            if (args.length < iNumParams) return null;
            boolean nested = false;
            for (int i = 0; i < iNumParams; i++) {
                if (args[i].bvarRange() > 0) {
                    throw new RuntimeException(
                        "invalid nested inductive datatype '" + indName +
                        "', nested inductive datatype parameters cannot contain local variables");
                }
                if (exprContainsAnyName(args[i], newTypeNames, new IdentityHashMap<>())) {
                    nested = true;
                }
            }
            if (!nested) return null;
            Expr[] paramArgs = new Expr[iNumParams];
            Expr[] indexArgs = new Expr[args.length - iNumParams];
            System.arraycopy(args, 0, paramArgs, 0, iNumParams);
            System.arraycopy(args, iNumParams, indexArgs, 0, indexArgs.length);
            return new NestedApp(head, indName, indInfo, iNumParams, paramArgs, indexArgs);
        }
    }

    private static final class NestedApp {
        final Expr headConst;
        final Name indName;
        final ConstantInfo indInfo;
        final int iNumParams;
        final Expr[] paramArgs;
        final Expr[] indexArgs;

        NestedApp(Expr headConst, Name indName, ConstantInfo indInfo, int iNumParams, Expr[] paramArgs, Expr[] indexArgs) {
            this.headConst = headConst;
            this.indName = indName;
            this.indInfo = indInfo;
            this.iNumParams = iNumParams;
            this.paramArgs = paramArgs;
            this.indexArgs = indexArgs;
        }
    }

    private static boolean exprContainsAnyName(Expr e, ArrayList<Name> names, IdentityHashMap<Expr, Boolean> visited) {
        if (e == null) return false;
        Boolean cached = visited.get(e);
        if (cached != null) return cached;
        boolean result;
        switch (e.tag) {
            case Expr.CONST: {
                Name n = (Name) e.o0;
                result = containsName(names, n);
                break;
            }
            case Expr.APP:
                result = exprContainsAnyName((Expr) e.o0, names, visited)
                    || exprContainsAnyName((Expr) e.o1, names, visited);
                break;
            case Expr.LAM:
            case Expr.FORALL:
                result = exprContainsAnyName((Expr) e.o1, names, visited)
                    || exprContainsAnyName((Expr) e.o2, names, visited);
                break;
            case Expr.LET:
                result = exprContainsAnyName((Expr) e.o1, names, visited)
                    || exprContainsAnyName((Expr) e.o2, names, visited)
                    || exprContainsAnyName((Expr) e.o3, names, visited);
                break;
            case Expr.MDATA:
            case Expr.PROJ:
                result = exprContainsAnyName((Expr) e.o1, names, visited);
                break;
            default:
                result = false;
        }
        visited.put(e, result);
        return result;
    }

    private static boolean containsName(ArrayList<Name> names, Name n) {
        for (Name existing : names) {
            if (existing.equals(n)) return true;
        }
        return false;
    }

    private static Expr getAppFn(Expr e) {
        Expr cur = e;
        while (cur.tag == Expr.APP) cur = (Expr) cur.o0;
        return cur;
    }

    private static Expr[] getAppArgs(Expr e) {
        int n = 0;
        Expr cur = e;
        while (cur.tag == Expr.APP) {
            n++;
            cur = (Expr) cur.o0;
        }
        Expr[] args = new Expr[n];
        cur = e;
        for (int i = n - 1; i >= 0; i--) {
            args[i] = (Expr) cur.o1;
            cur = (Expr) cur.o0;
        }
        return args;
    }

    private static Expr mkApp(Expr head, Expr[] args, int count) {
        Expr result = head;
        for (int i = 0; i < count; i++) result = Expr.app(result, args[i]);
        return result;
    }

    private static Name[] toNameArray(Object[] all) {
        Name[] out = new Name[all.length];
        for (int i = 0; i < all.length; i++) out[i] = (Name) all[i];
        return out;
    }

    private static boolean hasLevelParams(Object levels) {
        if (levels == null) return false;
        if (levels instanceof Object[]) return ((Object[]) levels).length > 0;
        if (levels instanceof java.util.List) return !((java.util.List<?>) levels).isEmpty();
        if (levels instanceof clojure.lang.IPersistentVector) return ((clojure.lang.IPersistentVector) levels).count() > 0;
        return true;
    }

    private static Object[] mkBundleLevelValues(Object[] levelParams) {
        if (levelParams == null || levelParams.length == 0) return new Object[0];
        Object[] out = new Object[levelParams.length];
        for (int i = 0; i < levelParams.length; i++) {
            out[i] = Level.param((Name) levelParams[i]);
        }
        return out;
    }
}
