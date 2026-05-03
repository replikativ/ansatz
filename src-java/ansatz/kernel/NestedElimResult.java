package ansatz.kernel;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

/**
 * Result of nested inductive elimination.
 *
 * <p>Matches Lean's design more closely than our previous recursor-only
 * reconstruction: we keep the transformed bundle together with the explicit
 * restoration metadata required to map auxiliary declarations back to the
 * original nested declaration.
 */
public final class NestedElimResult {
    public final InductiveBundle auxBundle;
    public final Expr[] params;

    /** Auxiliary inductive name -> nested application key I(Ds). */
    public final HashMap<Name, Expr> auxToNested;

    /** Auxiliary recursor name -> restored recursor name. */
    public final HashMap<Name, Name> auxRecToRestoredRec;

    /** Auxiliary inductive prefix -> restored inductive prefix. */
    public final HashMap<Name, Name> auxPrefixToRestoredPrefix;

    /** Canonical discovery order of nested applications. */
    public final ArrayList<Expr> nestedKeys;
    public final ArrayList<Name> auxNames;

    public NestedElimResult(InductiveBundle auxBundle, Expr[] params,
            HashMap<Name, Expr> auxToNested,
            HashMap<Name, Name> auxRecToRestoredRec,
            HashMap<Name, Name> auxPrefixToRestoredPrefix,
            ArrayList<Expr> nestedKeys,
            ArrayList<Name> auxNames) {
        this.auxBundle = auxBundle;
        this.params = params != null ? params : new Expr[0];
        this.auxToNested = auxToNested != null ? auxToNested : new HashMap<>();
        this.auxRecToRestoredRec = auxRecToRestoredRec != null ? auxRecToRestoredRec : new HashMap<>();
        this.auxPrefixToRestoredPrefix = auxPrefixToRestoredPrefix != null ? auxPrefixToRestoredPrefix : new HashMap<>();
        this.nestedKeys = nestedKeys != null ? nestedKeys : new ArrayList<>();
        this.auxNames = auxNames != null ? auxNames : new ArrayList<>();
    }

    public Expr restoreNested(Expr e) {
        return withParamBinders(e, auxRecToRestoredRec, true);
    }

    public Expr restoreNested(Expr e, HashMap<Name, Name> recMap) {
        return withParamBinders(e, recMap, true);
    }

    public Expr lowerToAux(Expr e) {
        HashMap<Name, Name> restoredRecToAux = invertNameMap(auxRecToRestoredRec);
        return withParamBinders(e, restoredRecToAux, false);
    }

    public Name restoreConstructorName(Name ctorName) {
        for (HashMap.Entry<Name, Name> entry : auxPrefixToRestoredPrefix.entrySet()) {
            Name auxPrefix = entry.getKey();
            if (ctorName.equals(auxPrefix) || hasPrefix(ctorName, auxPrefix)) {
                return ctorName.replacePrefix(auxPrefix, entry.getValue());
            }
        }
        return ctorName;
    }

    public Name lowerConstructorName(Name ctorName, Expr[] currentParams) {
        for (Map.Entry<Name, Name> entry : auxPrefixToRestoredPrefix.entrySet()) {
            Name auxPrefix = entry.getKey();
            Name restoredPrefix = entry.getValue();
            if (!ctorName.equals(restoredPrefix) && !hasPrefix(ctorName, restoredPrefix)) continue;
            Expr nested = auxToNested.get(auxPrefix);
            if (nested == null) continue;
            Expr instantiated = instantiateStoredParams(nested, currentParams);
            Expr[] instArgs = getAppArgs(instantiated);
            Expr head = getAppFn(instantiated);
            if (head.tag != Expr.CONST) continue;
            int paramCount = instArgs.length;
            return ctorName.replacePrefix(restoredPrefix, auxPrefix);
        }
        return ctorName;
    }

    private Expr withParamBinders(Expr e, HashMap<Name, Name> recMap, boolean restoreDirection) {
        if (e == null) return null;
        if (params.length == 0 || (e.tag != Expr.FORALL && e.tag != Expr.LAM)) {
            return transform(e, params, recMap, restoreDirection);
        }
        ParamFrame frame = peelParamBinders(e);
        Expr newBody = transform(frame.body, frame.locals, recMap, restoreDirection);
        return rebuild(frame, newBody);
    }

    private Expr transform(Expr e, Expr[] currentParams, HashMap<Name, Name> recMap, boolean restoreDirection) {
        if (e == null) return null;
        if (e.tag == Expr.CONST) {
            Name n = (Name) e.o0;
            if (recMap != null) {
                Name restoredRec = recMap.get(n);
                if (restoredRec != null) {
                    return Expr.mkConst(restoredRec, e.o1, e.hasLevelParam());
                }
            }
            if (restoreDirection) {
                Expr nested = auxToNested.get(n);
                if (nested != null) return instantiateStoredParams(nested, currentParams);
                for (Map.Entry<Name, Name> entry : auxPrefixToRestoredPrefix.entrySet()) {
                    Name auxPrefix = entry.getKey();
                    Name restoredPrefix = entry.getValue();
                    if (!n.equals(auxPrefix) && !hasPrefix(n, auxPrefix)) continue;
                    Expr nestedBase = instantiateStoredParams(auxToNested.get(auxPrefix), currentParams);
                    Expr[] nestedArgs = getAppArgs(nestedBase);
                    Expr nestedHead = getAppFn(nestedBase);
                    if (nestedHead.tag != Expr.CONST) continue;
                    Name newFnName = n.replacePrefix(auxPrefix, restoredPrefix);
                    Expr restored = Expr.mkConst(newFnName, nestedHead.o1, nestedHead.hasLevelParam());
                    for (Expr nestedArg : nestedArgs) restored = Expr.app(restored, nestedArg);
                    return restored;
                }
            }
            return e;
        }
        if (e.tag == Expr.APP) {
            Expr special = restoreDirection
                ? tryRestoreApp(e, currentParams, recMap)
                : tryLowerApp(e, currentParams, recMap);
            if (special != null) return special;
        }
        switch (e.tag) {
            case Expr.APP: {
                Expr fn = transform((Expr) e.o0, currentParams, recMap, restoreDirection);
                Expr arg = transform((Expr) e.o1, currentParams, recMap, restoreDirection);
                return (fn == e.o0 && arg == e.o1) ? e : Expr.app(fn, arg);
            }
            case Expr.LAM: {
                Expr type = transform((Expr) e.o1, currentParams, recMap, restoreDirection);
                Expr body = transform((Expr) e.o2, currentParams, recMap, restoreDirection);
                return (type == e.o1 && body == e.o2) ? e : Expr.lam(e.o0, type, body, e.o3);
            }
            case Expr.FORALL: {
                Expr type = transform((Expr) e.o1, currentParams, recMap, restoreDirection);
                Expr body = transform((Expr) e.o2, currentParams, recMap, restoreDirection);
                return (type == e.o1 && body == e.o2) ? e : Expr.forall(e.o0, type, body, e.o3);
            }
            case Expr.LET: {
                Expr type = transform((Expr) e.o1, currentParams, recMap, restoreDirection);
                Expr val = transform((Expr) e.o2, currentParams, recMap, restoreDirection);
                Expr body = transform((Expr) e.o3, currentParams, recMap, restoreDirection);
                return (type == e.o1 && val == e.o2 && body == e.o3) ? e : Expr.mkLet(e.o0, type, val, body);
            }
            case Expr.MDATA: {
                Expr inner = transform((Expr) e.o1, currentParams, recMap, restoreDirection);
                return inner == e.o1 ? e : Expr.mdata(e.o0, inner);
            }
            case Expr.PROJ: {
                Expr inner = transform((Expr) e.o1, currentParams, recMap, restoreDirection);
                return inner == e.o1 ? e : Expr.proj(e.o0, e.longVal, inner);
            }
            default:
                return e;
        }
    }

    private Expr tryRestoreApp(Expr e, Expr[] currentParams, HashMap<Name, Name> recMap) {
        Expr[] args = getAppArgs(e);
        Expr head = getAppFn(e);
        if (head.tag != Expr.CONST) return null;
        Name headName = (Name) head.o0;
        if (recMap != null && recMap.containsKey(headName)) return null;
        Expr nested = auxToNested.get(headName);
        if (nested != null) {
            Expr restored = instantiateStoredParams(nested, currentParams);
            int paramCount = currentParams.length;
            for (int i = paramCount; i < args.length; i++) {
                restored = Expr.app(restored, transform(args[i], currentParams, recMap, true));
            }
            return restored;
        }
        for (Map.Entry<Name, Name> entry : auxPrefixToRestoredPrefix.entrySet()) {
            Name auxPrefix = entry.getKey();
            Name restoredPrefix = entry.getValue();
            if (!headName.equals(auxPrefix) && !hasPrefix(headName, auxPrefix)) continue;
            Expr nestedBase = instantiateStoredParams(auxToNested.get(auxPrefix), currentParams);
            Expr[] nestedArgs = getAppArgs(nestedBase);
            Expr nestedHead = getAppFn(nestedBase);
            if (nestedHead.tag != Expr.CONST) return null;
            Name newFnName = headName.replacePrefix(auxPrefix, restoredPrefix);
            Expr restored = Expr.mkConst(newFnName, nestedHead.o1, nestedHead.hasLevelParam());
            for (Expr nestedArg : nestedArgs) restored = Expr.app(restored, nestedArg);
            for (int i = currentParams.length; i < args.length; i++) {
                restored = Expr.app(restored, transform(args[i], currentParams, recMap, true));
            }
            return restored;
        }
        return null;
    }

    private Expr tryLowerApp(Expr e, Expr[] currentParams, HashMap<Name, Name> recMap) {
        Expr[] args = getAppArgs(e);
        Expr head = getAppFn(e);
        if (head.tag != Expr.CONST) return null;
        Name headName = (Name) head.o0;
        Object[] auxLevels = auxLevelValues();
        boolean auxHasLevelParams = auxLevels.length > 0;

        for (Map.Entry<Name, Expr> entry : auxToNested.entrySet()) {
            Name auxName = entry.getKey();
            Expr nestedBase = instantiateStoredParams(entry.getValue(), currentParams);
            Expr[] nestedArgs = getAppArgs(nestedBase);
            Expr nestedHead = getAppFn(nestedBase);
            if (nestedHead.tag != Expr.CONST) continue;
            Name restoredPrefix = auxPrefixToRestoredPrefix.get(auxName);
            if (restoredPrefix == null) continue;

            if (headName.equals((Name) nestedHead.o0) && hasAppPrefix(args, nestedArgs)) {
                Expr lowered = Expr.mkConst(auxName, auxLevels, auxHasLevelParams);
                for (Expr p : currentParams) lowered = Expr.app(lowered, p);
                for (int i = nestedArgs.length; i < args.length; i++) {
                    lowered = Expr.app(lowered, transform(args[i], currentParams, recMap, false));
                }
                return lowered;
            }

            if ((headName.equals(restoredPrefix) || hasPrefix(headName, restoredPrefix)) && hasAppPrefix(args, nestedArgs)) {
                Name loweredCtor = headName.replacePrefix(restoredPrefix, auxName);
                Expr lowered = Expr.mkConst(loweredCtor, auxLevels, auxHasLevelParams);
                for (Expr p : currentParams) lowered = Expr.app(lowered, p);
                for (int i = nestedArgs.length; i < args.length; i++) {
                    lowered = Expr.app(lowered, transform(args[i], currentParams, recMap, false));
                }
                return lowered;
            }
        }
        return null;
    }

    private static boolean hasPrefix(Name n, Name prefix) {
        if (n == null || prefix == null) return false;
        if (n.equals(prefix)) return true;
        return n.prefix != null && hasPrefix(n.prefix, prefix);
    }

    private static boolean hasAppPrefix(Expr[] args, Expr[] prefix) {
        if (args.length < prefix.length) return false;
        for (int i = 0; i < prefix.length; i++) {
            if (!args[i].equals(prefix[i])) return false;
        }
        return true;
    }

    private Expr instantiateStoredParams(Expr e, Expr[] currentParams) {
        if (params.length == 0) return e;
        long[] paramIds = new long[params.length];
        for (int i = 0; i < params.length; i++) paramIds[i] = params[i].longVal;
        Expr abstracted = Reducer.abstractFvars(e, params.length, paramIds);
        return Reducer.instantiateRev(abstracted, currentParams.length, currentParams, 0);
    }

    private static HashMap<Name, Name> invertNameMap(HashMap<Name, Name> in) {
        HashMap<Name, Name> out = new HashMap<>();
        for (Map.Entry<Name, Name> entry : in.entrySet()) {
            out.put(entry.getValue(), entry.getKey());
        }
        return out;
    }

    private Object[] auxLevelValues() {
        Object[] lp = auxBundle.levelParams;
        if (lp == null || lp.length == 0) return new Object[0];
        Object[] out = new Object[lp.length];
        for (int i = 0; i < lp.length; i++) {
            out[i] = Level.param((Name) lp[i]);
        }
        return out;
    }

    private ParamFrame peelParamBinders(Expr e) {
        Expr cur = e;
        ParamBinder[] binders = new ParamBinder[params.length];
        Expr[] locals = new Expr[params.length];
        long nextFVar = 20_000_000L;
        for (int i = 0; i < params.length; i++) {
            if (cur.tag != Expr.FORALL && cur.tag != Expr.LAM) {
                throw new RuntimeException("invalid nested restoration shape");
            }
            long fvarId = nextFVar++;
            binders[i] = new ParamBinder(cur.tag, cur.o0, (Expr) cur.o1, cur.o3, fvarId);
            locals[i] = Expr.fvar(fvarId);
            cur = Reducer.instantiateRev((Expr) cur.o2, 1, new Expr[] { locals[i] }, 0);
        }
        return new ParamFrame(binders, locals, cur);
    }

    private Expr rebuild(ParamFrame frame, Expr body) {
        long[] ids = new long[frame.binders.length];
        for (int i = 0; i < frame.binders.length; i++) ids[i] = frame.binders[i].fvarId;
        Expr result = Reducer.abstractFvars(body, frame.binders.length, ids);
        for (int i = frame.binders.length - 1; i >= 0; i--) {
            Expr domain = Reducer.abstractFvars(frame.binders[i].type, i, ids);
            result = frame.binders[i].tag == Expr.FORALL
                ? Expr.forall(frame.binders[i].name, domain, result, frame.binders[i].binderInfo)
                : Expr.lam(frame.binders[i].name, domain, result, frame.binders[i].binderInfo);
        }
        return result;
    }

    private static final class ParamFrame {
        final ParamBinder[] binders;
        final Expr[] locals;
        final Expr body;

        ParamFrame(ParamBinder[] binders, Expr[] locals, Expr body) {
            this.binders = binders;
            this.locals = locals;
            this.body = body;
        }
    }

    private static final class ParamBinder {
        final byte tag;
        final Object name;
        final Expr type;
        final Object binderInfo;
        final long fvarId;

        ParamBinder(byte tag, Object name, Expr type, Object binderInfo, long fvarId) {
            this.tag = tag;
            this.name = name;
            this.type = type;
            this.binderInfo = binderInfo;
            this.fvarId = fvarId;
        }
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
}
