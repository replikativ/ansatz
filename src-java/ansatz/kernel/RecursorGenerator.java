package ansatz.kernel;

import java.util.ArrayList;
import java.util.HashMap;

/**
 * Lean-shaped recursor generator for inductive bundle admission.
 *
 * <p>This mirrors the recursor-generation half of Lean's add_inductive_fn:
 * mk_rec_infos -> collect_Cs/collect_minor_premises -> mk_rec_rules ->
 * declare_recursors. Lean constructs recursor declarations directly. Ansatz
 * regenerates the expected type/rules, compares them with bundle recursor
 * declarations, and then admits them. The Clojure inductive frontend also uses
 * this generator to populate Lean-shaped iota rules before bundle admission.
 */
final class RecursorGenerator {
    private static final Object BINDER_DEFAULT = clojure.lang.Keyword.intern(null, "default");
    private static final Object BINDER_IMPLICIT = clojure.lang.Keyword.intern(null, "implicit");

    private static final class RecInfo {
        final ArrayList<LocalDecl> indices = new ArrayList<>();
        LocalDecl motive;
        LocalDecl major;
        final ArrayList<LocalDecl> minors = new ArrayList<>();
    }

    private Env workingEnv;
    private final InductiveBundle bundle;
    private final long fuel;
    private final Object[] levelValues;
    private final boolean hasLevelParams;
    private final ArrayList<LocalDecl> params;
    private final int[] numIndices;
    private final Expr[] indConsts;
    private final Level elimLevel;
    private final RecInfo[] recInfos;
    private long nextLocalId;

    RecursorGenerator(Env env, InductiveBundle bundle, long fuel,
            Object[] levelValues, boolean hasLevelParams,
            ArrayList<LocalDecl> params, int[] numIndices, Expr[] indConsts,
            Level elimLevel, long nextLocalId) {
        this.workingEnv = env;
        this.bundle = bundle;
        this.fuel = fuel;
        this.levelValues = levelValues;
        this.hasLevelParams = hasLevelParams;
        this.params = params;
        this.numIndices = numIndices;
        this.indConsts = indConsts;
        this.elimLevel = elimLevel;
        this.nextLocalId = nextLocalId;
        this.recInfos = new RecInfo[bundle.inductives.length];
        for (int i = 0; i < recInfos.length; i++) {
            recInfos[i] = new RecInfo();
        }
    }

    /**
     * Mirrors Lean add_inductive_fn::mk_rec_infos.
     */
    void mkRecInfos() {
        TypeChecker tc = new TypeChecker(workingEnv, bundle.isUnsafe ? TypeChecker.DEFN_UNSAFE : TypeChecker.DEFN_SAFE, bundle.levelParams);
        tc.setFuel(fuel);
        addParamsTo(tc);

        for (int dIdx = 0; dIdx < bundle.inductives.length; dIdx++) {
            ConstantInfo ind = bundle.inductives[dIdx];
            RecInfo info = recInfos[dIdx];
            Expr t = tc.whnfExpr(ind.type);
            int i = 0;
            while (t.tag == Expr.FORALL) {
                if (i < bundle.numParams) {
                    t = Reducer.instantiate1((Expr) t.o2, params.get(i).fvar);
                } else {
                    LocalDecl idx = mkLocalDeclFor(tc, t);
                    info.indices.add(idx);
                    t = Reducer.instantiate1((Expr) t.o2, idx.fvar);
                }
                i++;
                t = tc.whnfExpr(t);
            }
            Expr majorType = mkApp(indConsts[dIdx], appendLocals(params, info.indices));
            info.major = mkLocalDecl(tc, Name.fromString("t"), majorType, BINDER_DEFAULT);
            Expr motiveType = Expr.sort(elimLevel, Level.hasParam(elimLevel));
            ArrayList<LocalDecl> motiveTele = new ArrayList<>(info.indices.size() + 1);
            motiveTele.addAll(info.indices);
            motiveTele.add(info.major);
            motiveType = buildPi(motiveTele, motiveType);
            Name motiveName = Name.fromString("motive");
            if (bundle.inductives.length > 1) {
                motiveName = motiveName.appendAfter(dIdx + 1);
            }
            info.motive = mkLocalDecl(tc, motiveName, motiveType, BINDER_IMPLICIT);
        }

        for (int dIdx = 0; dIdx < bundle.inductives.length; dIdx++) {
            ConstantInfo ind = bundle.inductives[dIdx];
            RecInfo info = recInfos[dIdx];
            for (Name ctorName : ind.ctors) {
                ConstantInfo ctor = workingEnv.lookup(ctorName);
                ArrayList<LocalDecl> bU = new ArrayList<>();
                ArrayList<LocalDecl> u = new ArrayList<>();
                TypeChecker ctorTc = new TypeChecker(workingEnv, bundle.isUnsafe ? TypeChecker.DEFN_UNSAFE : TypeChecker.DEFN_SAFE, bundle.levelParams);
                ctorTc.setFuel(fuel);
                addParamsTo(ctorTc);

                Expr t = ctor.type;
                int i = 0;
                while (t.tag == Expr.FORALL) {
                    if (i < bundle.numParams) {
                        t = Reducer.instantiate1((Expr) t.o2, params.get(i).fvar);
                    } else {
                        LocalDecl l = mkLocalDeclFor(ctorTc, t);
                        bU.add(l);
                        if (isRecArgument(ctorTc, l.type)) {
                            u.add(l);
                        }
                        t = Reducer.instantiate1((Expr) t.o2, l.fvar);
                    }
                    i++;
                }

                ArrayList<LocalDecl> v = new ArrayList<>();
                for (LocalDecl uI : u) {
                    Expr uTy = ctorTc.whnfExpr(ctorTc.inferType(uI.fvar));
                    TypeChecker uTc = new TypeChecker(workingEnv, bundle.isUnsafe ? TypeChecker.DEFN_UNSAFE : TypeChecker.DEFN_SAFE, bundle.levelParams);
                    uTc.setFuel(fuel);
                    addParamsTo(uTc);
                    addLocalsTo(uTc, bU);
                    ArrayList<LocalDecl> xs = new ArrayList<>();
                    while (uTy.tag == Expr.FORALL) {
                        LocalDecl x = mkLocalDeclFor(uTc, uTy);
                        xs.add(x);
                        uTy = uTc.whnfExpr(Reducer.instantiate1((Expr) uTy.o2, x.fvar));
                    }
                    ArrayList<Expr> itIndices = new ArrayList<>();
                    int itIdx = getIIndices(uTy, itIndices);
                    Expr cApp = mkApp(recInfos[itIdx].motive.fvar, appendExprs(itIndices, mkApp(uI.fvar, xs)));
                    Expr vTy = buildPi(xs, cApp);
                    Object ihName = appendAfterIH(uI.name);
                    v.add(mkLocalDecl(ctorTc, ihName, vTy, BINDER_DEFAULT));
                }

                ArrayList<Expr> itIndices = new ArrayList<>();
                int itIdx = getIIndices(t, itIndices);
                Expr cApp = mkApp(recInfos[itIdx].motive.fvar, appendExprs(itIndices, mkApp(Expr.mkConst(ctorName, levelValues, hasLevelParams),
                    appendLocals(params, bU))));
                ArrayList<LocalDecl> minorTele = new ArrayList<>(bU.size() + v.size());
                minorTele.addAll(bU);
                minorTele.addAll(v);
                Expr minorTy = buildPi(minorTele, cApp);
                Name minorName = stripCtorPrefix(ctorName, ind.name);
                info.minors.add(mkLocalDecl(tc, minorName, minorTy, BINDER_DEFAULT));
            }
        }
    }

    /**
     * Ansatz counterpart of Lean add_inductive_fn::declare_recursors.
     */
    Env checkAndDeclareRecursors() {
        for (int i = 0; i < bundle.recursors.length; i++) {
            ConstantInfo rec = bundle.recursors[i];
            int indIdx = recursorInductiveIndex(rec.name);
            Expr expectedType = buildExpectedRecursorType(indIdx);
            compareGeneratedType(rec, expectedType);
            ConstantInfo.RecursorRule[] expectedRules = buildExpectedRecursorRules(indIdx, rec);
            compareGeneratedRules(rec, expectedRules);
            TypeChecker.checkRecursorDeclaration(workingEnv, rec, fuel);
            workingEnv = workingEnv.addConstant(rec);
        }
        return workingEnv;
    }

    /**
     * Mirrors Lean add_inductive_fn::declare_recursors recursor type construction.
     */
    private Expr buildExpectedRecursorType(int dIdx) {
        RecInfo info = recInfos[dIdx];
        ArrayList<LocalDecl> motives = collectMotives();
        ArrayList<LocalDecl> minors = collectMinors();
        Expr cApp = mkApp(info.motive.fvar, appendExprs(extractFvars(info.indices), info.major.fvar));
        ArrayList<LocalDecl> recTele = new ArrayList<>(
            params.size() + motives.size() + minors.size() + info.indices.size() + 1);
        recTele.addAll(params);
        recTele.addAll(motives);
        recTele.addAll(minors);
        recTele.addAll(info.indices);
        recTele.add(info.major);
        return buildPi(recTele, cApp);
    }

    /**
     * Mirrors Lean collect_Cs.
     */
    private ArrayList<LocalDecl> collectMotives() {
        ArrayList<LocalDecl> out = new ArrayList<>();
        for (RecInfo info : recInfos) out.add(info.motive);
        return out;
    }

    /**
     * Mirrors Lean collect_minor_premises.
     */
    private ArrayList<LocalDecl> collectMinors() {
        ArrayList<LocalDecl> out = new ArrayList<>();
        for (RecInfo info : recInfos) out.addAll(info.minors);
        return out;
    }

    /**
     * Mirrors Lean add_inductive_fn::mk_rec_rules.
     */
    private ConstantInfo.RecursorRule[] buildExpectedRecursorRules(int recIdx, ConstantInfo recCi) {
        if (recCi.numMotives > recCi.all.length) {
            throw new RuntimeException("expected non-nested recursor declaration: " + recCi.name);
        }

        ArrayList<LocalDecl> motives = collectMotives();
        ArrayList<LocalDecl> minors = collectMinors();
        Object[] recLevelValues = getExpectedRecLevelValues();
        boolean recHasLevelParams = recLevelValues.length > 0;

        int minorIdx = 0;
        for (int i = 0; i < recIdx; i++) {
            minorIdx += recInfos[i].minors.size();
        }

        ConstantInfo ind = bundle.inductives[recIdx];
        ConstantInfo.RecursorRule[] out = new ConstantInfo.RecursorRule[ind.ctors.length];
        for (int ruleIdx = 0; ruleIdx < ind.ctors.length; ruleIdx++) {
            Name ctorName = ind.ctors[ruleIdx];
            ConstantInfo ctorCi = workingEnv.lookup(ctorName);
            if (ctorCi == null || !ctorCi.isCtor()) {
                throw new RuntimeException("Recursor rule references unknown constructor: " + ctorName);
            }

            ArrayList<LocalDecl> bU = new ArrayList<>();
            ArrayList<LocalDecl> u = new ArrayList<>();
            TypeChecker ctorTc = new TypeChecker(workingEnv, bundle.isUnsafe ? TypeChecker.DEFN_UNSAFE : TypeChecker.DEFN_SAFE, bundle.levelParams);
            ctorTc.setFuel(fuel);
            addParamsTo(ctorTc);

            Expr t = ctorCi.type;
            int i = 0;
            while (t.tag == Expr.FORALL) {
                if (i < bundle.numParams) {
                    t = Reducer.instantiate1((Expr) t.o2, params.get(i).fvar);
                } else {
                    LocalDecl l = mkLocalDeclFor(ctorTc, t);
                    bU.add(l);
                    if (isRecArgument(ctorTc, l.type)) {
                        u.add(l);
                    }
                    t = Reducer.instantiate1((Expr) t.o2, l.fvar);
                }
                i++;
            }

            ArrayList<Expr> v = new ArrayList<>();
            for (LocalDecl uI : u) {
                Expr uTy = ctorTc.whnfExpr(ctorTc.inferType(uI.fvar));
                TypeChecker uTc = new TypeChecker(workingEnv, bundle.isUnsafe ? TypeChecker.DEFN_UNSAFE : TypeChecker.DEFN_SAFE, bundle.levelParams);
                uTc.setFuel(fuel);
                addParamsTo(uTc);
                addLocalsTo(uTc, bU);
                ArrayList<LocalDecl> xs = new ArrayList<>();
                while (uTy.tag == Expr.FORALL) {
                    LocalDecl x = mkLocalDeclFor(uTc, uTy);
                    xs.add(x);
                    uTy = uTc.whnfExpr(Reducer.instantiate1((Expr) uTy.o2, x.fvar));
                }
                ArrayList<Expr> itIndices = new ArrayList<>();
                int indIdx = getIIndices(uTy, itIndices);
                Name targetRecName = bundle.inductives.length == 1 ? recCi.name : recursorNameForInductiveIndex(indIdx);
                Expr recApp = Expr.mkConst(targetRecName, recLevelValues, recHasLevelParams);
                recApp = mkApp(recApp, params);
                recApp = mkApp(recApp, motives);
                recApp = mkApp(recApp, minors);
                recApp = mkApp(recApp, itIndices);
                recApp = Expr.app(recApp, mkApp(uI.fvar, xs));
                v.add(buildLambda(xs, recApp));
            }

            Expr eApp = mkApp(minors.get(minorIdx).fvar, bU);
            eApp = mkApp(eApp, v);
            Expr expectedRhs = buildLambda(params,
                buildLambda(motives,
                    buildLambda(minors,
                        buildLambda(bU, eApp)),
                    BINDER_DEFAULT));
            out[ruleIdx] = new ConstantInfo.RecursorRule(ctorName, bU.size(), expectedRhs);
            minorIdx++;
        }
        return out;
    }

    Expr debugBuildExpectedRecursorType(int recIdx) {
        return buildExpectedRecursorType(recIdx);
    }

    Expr debugBuildNormalizedExpectedRecursorType(int recIdx, ConstantInfo recCi) {
        return normalizeExpectedRecursorType(buildExpectedRecursorType(recIdx), recCi);
    }

    ConstantInfo.RecursorRule[] debugBuildExpectedRecursorRules(int recIdx, ConstantInfo recCi) {
        return buildExpectedRecursorRules(recIdx, recCi);
    }

    private Object[] getExpectedRecLevelValues() {
        int extra = elimLevel.tag == Level.PARAM ? 1 : 0;
        Object[] out = new Object[levelValues.length + extra];
        int offset = 0;
        if (extra == 1) {
            out[0] = elimLevel;
            offset = 1;
        }
        for (int i = 0; i < levelValues.length; i++) {
            out[i + offset] = levelValues[i];
        }
        return out;
    }

    private void compareGeneratedType(ConstantInfo importedRec, Expr expectedType) {
        Expr normalizedExpected = normalizeExpectedRecursorType(expectedType, importedRec);
        if (TypeChecker.exprDeepEquals(importedRec.type, normalizedExpected)) {
            return;
        }
        TypeChecker tc = new TypeChecker(workingEnv, bundle.isUnsafe ? TypeChecker.DEFN_UNSAFE : TypeChecker.DEFN_SAFE, importedRec.levelParams);
        tc.setFuel(fuel);
        if (tc.isDefEq(importedRec.type, normalizedExpected)) return;
        throw new RuntimeException("generated recursor type mismatch for " + importedRec.name);
    }

    private Expr normalizeExpectedRecursorType(Expr expectedType, ConstantInfo importedRec) {
        if (importedRec.levelParams.length == 0 && bundle.levelParams.length == 0) {
            return expectedType;
        }
        HashMap<Object, Level> subst = new HashMap<>();
        int offset = importedRec.levelParams.length - bundle.levelParams.length;
        if (elimLevel.tag == Level.PARAM && offset > 0) {
            subst.put(elimLevel.paramName(), Level.param((Name) importedRec.levelParams[0]));
        }
        for (int i = 0; i < bundle.levelParams.length; i++) {
            int targetIdx = i + Math.max(offset, 0);
            if (targetIdx < importedRec.levelParams.length) {
                subst.put(bundle.levelParams[i], Level.param((Name) importedRec.levelParams[targetIdx]));
            }
        }
        return subst.isEmpty() ? expectedType : Reducer.instantiateLevelParams(expectedType, subst);
    }

    private void compareGeneratedRules(ConstantInfo importedRec, ConstantInfo.RecursorRule[] expectedRules) {
        if (importedRec.rules == null && expectedRules == null) return;
        if (importedRec.rules == null || expectedRules == null || importedRec.rules.length != expectedRules.length) {
            throw new RuntimeException("generated recursor rule count mismatch for " + importedRec.name);
        }
        for (int i = 0; i < importedRec.rules.length; i++) {
            ConstantInfo.RecursorRule actual = importedRec.rules[i];
            ConstantInfo.RecursorRule expected = expectedRules[i];
            // ctor name and field count are the rule's structural identity — must match exactly.
            if (!actual.ctor.equals(expected.ctor) || actual.nfields != expected.nfields) {
                throw new RuntimeException("generated recursor rule mismatch for " + importedRec.name +
                    " rule #" + (i + 1));
            }
            // The rule RHS is only determined up to definitional equality: Lean's exported recursor
            // and our correct-by-construction generated one differ in defeq-invisible ways (stripped
            // optParam/autoParam field wrappers, binder info, binder names). Mirror compareGeneratedType:
            // accept on structural equality, else fall back to isDefEq. (Validation only — the stored
            // recursor is Lean's, already kernel-checked at export time.)
            if (TypeChecker.exprDeepEquals(actual.rhs, expected.rhs)) {
                continue;
            }
            TypeChecker tc = new TypeChecker(workingEnv, bundle.isUnsafe ? TypeChecker.DEFN_UNSAFE : TypeChecker.DEFN_SAFE, importedRec.levelParams);
            tc.setFuel(fuel);
            if (tc.isDefEq(actual.rhs, expected.rhs)) {
                continue;
            }
            if (System.getProperty("ansatz.debugRecRules") != null) {
                System.err.println("=== REC RULE MISMATCH " + importedRec.name + " rule #" + (i + 1) + " (not defeq) ===");
                System.err.println("  IMPORTED rhs (Lean): " + actual.rhs);
                System.err.println("  GENERATED rhs (ours): " + expected.rhs);
            }
            throw new RuntimeException("generated recursor rule mismatch for " + importedRec.name +
                " rule #" + (i + 1));
        }
    }

    private int recursorInductiveIndex(Name recName) {
        for (int i = 0; i < bundle.inductives.length; i++) {
            Name expected = Name.mkStr(bundle.inductives[i].name, "rec");
            if (expected.equals(recName)) return i;
        }
        throw new RuntimeException("recursor does not match any inductive in bundle: " + recName);
    }

    private Name recursorNameForInductiveIndex(int indIdx) {
        Name expected = Name.mkStr(bundle.inductives[indIdx].name, "rec");
        for (ConstantInfo rec : bundle.recursors) {
            if (expected.equals(rec.name)) return rec.name;
        }
        throw new RuntimeException("missing recursor for inductive in bundle: " + bundle.inductives[indIdx].name);
    }

    private LocalDecl mkLocalDecl(TypeChecker tc, Object name, Expr type, Object binderInfo) {
        long id = nextLocalId++;
        Expr localType = TypeChecker.consumeTypeAnnotations(type);
        tc.addLocalDecl(id, name, localType);
        return new LocalDecl(id, name, localType, binderInfo);
    }

    private LocalDecl mkLocalDeclFor(TypeChecker tc, Expr forallExpr) {
        return mkLocalDecl(tc, forallExpr.o0, (Expr) forallExpr.o1, forallExpr.o3);
    }

    private void addParamsTo(TypeChecker tc) {
        addLocalsTo(tc, params);
    }

    private void addLocalsTo(TypeChecker tc, ArrayList<LocalDecl> locals) {
        for (LocalDecl local : locals) {
            tc.addLocalDecl(local.id, local.name, local.type);
        }
    }

    private int getIIndices(Expr t, ArrayList<Expr> indices) {
        int idx = isValidIndApp(t);
        Expr[] args = getAppArgs(t);
        for (int i = bundle.numParams; i < args.length; i++) {
            indices.add(args[i]);
        }
        return idx;
    }

    private boolean isRecArgument(TypeChecker tc, Expr t) {
        Expr current = tc.whnfExpr(t);
        while (current.tag == Expr.FORALL) {
            LocalDecl local = mkLocalDeclFor(tc, current);
            current = tc.whnfExpr(Reducer.instantiate1((Expr) current.o2, local.fvar));
        }
        return isValidIndAppOptional(current) >= 0;
    }

    private int isValidIndApp(Expr t) {
        int idx = isValidIndAppOptional(t);
        if (idx < 0) {
            throw new RuntimeException("invalid inductive application in recursor generation");
        }
        return idx;
    }

    private int isValidIndAppOptional(Expr t) {
        Expr head = t;
        int argCount = 0;
        while (head.tag == Expr.APP) {
            head = (Expr) head.o0;
            argCount++;
        }
        if (head.tag != Expr.CONST) return -1;
        Expr[] args = getAppArgs(t);
        for (int i = 0; i < indConsts.length; i++) {
            Expr indConst = indConsts[i];
            if (!head.equals(indConst) || args.length != bundle.numParams + numIndices[i]) continue;
            boolean paramsOk = true;
            for (int j = 0; j < bundle.numParams; j++) {
                if (!args[j].isEqp(params.get(j).fvar)) {
                    paramsOk = false;
                    break;
                }
            }
            if (!paramsOk) continue;
            boolean idxOk = true;
            for (int j = bundle.numParams; j < args.length; j++) {
                if (hasIndOcc(args[j])) {
                    idxOk = false;
                    break;
                }
            }
            if (idxOk) return i;
        }
        return -1;
    }

    private boolean hasIndOcc(Expr e) {
        if (e == null) return false;
        switch (e.tag) {
            case Expr.CONST:
                for (Expr indConst : indConsts) {
                    if (e.equals(indConst)) return true;
                }
                return false;
            case Expr.APP:
                return hasIndOcc((Expr) e.o0) || hasIndOcc((Expr) e.o1);
            case Expr.LAM:
            case Expr.FORALL:
                return hasIndOcc((Expr) e.o1) || hasIndOcc((Expr) e.o2);
            case Expr.LET:
                return hasIndOcc((Expr) e.o1) || hasIndOcc((Expr) e.o2) || hasIndOcc((Expr) e.o3);
            case Expr.PROJ:
            case Expr.MDATA:
                return hasIndOcc((Expr) e.o1);
            default:
                return false;
        }
    }

    private static Expr buildPi(ArrayList<LocalDecl> locals, Expr body) {
        if (locals.isEmpty()) return body;
        long[] ids = new long[locals.size()];
        for (int i = 0; i < locals.size(); i++) ids[i] = locals.get(i).id;
        Expr result = Reducer.abstractFvars(body, ids.length, ids);
        for (int i = locals.size() - 1; i >= 0; i--) {
            LocalDecl local = locals.get(i);
            Expr domain = Reducer.abstractFvars(local.type, i, ids);
            result = Expr.forall(local.name, domain, result, local.binderInfo);
        }
        return result;
    }

    private static Expr buildLambda(ArrayList<LocalDecl> locals, Expr body) {
        return buildLambda(locals, body, null);
    }

    private static Expr buildLambda(ArrayList<LocalDecl> locals, Expr body, Object binderInfoOverride) {
        if (locals.isEmpty()) return body;
        long[] ids = new long[locals.size()];
        for (int i = 0; i < locals.size(); i++) ids[i] = locals.get(i).id;
        Expr result = Reducer.abstractFvars(body, ids.length, ids);
        for (int i = locals.size() - 1; i >= 0; i--) {
            LocalDecl local = locals.get(i);
            Expr domain = Reducer.abstractFvars(local.type, i, ids);
            Object binderInfo = binderInfoOverride != null ? binderInfoOverride : local.binderInfo;
            result = Expr.lam(local.name, domain, result, binderInfo);
        }
        return result;
    }

    private static Expr mkApp(Expr fn, ArrayList<? extends Object> args) {
        Expr result = fn;
        for (Object arg : args) {
            result = Expr.app(result, arg instanceof LocalDecl ? ((LocalDecl) arg).fvar : (Expr) arg);
        }
        return result;
    }

    private static ArrayList<Object> appendLocals(ArrayList<LocalDecl> left, ArrayList<LocalDecl> right) {
        ArrayList<Object> out = new ArrayList<>(left.size() + right.size());
        out.addAll(left);
        out.addAll(right);
        return out;
    }

    private static ArrayList<Expr> appendExprs(ArrayList<Expr> left, Expr last) {
        ArrayList<Expr> out = new ArrayList<>(left.size() + 1);
        out.addAll(left);
        out.add(last);
        return out;
    }

    private static ArrayList<Expr> extractFvars(ArrayList<LocalDecl> locals) {
        ArrayList<Expr> out = new ArrayList<>(locals.size());
        for (LocalDecl local : locals) out.add(local.fvar);
        return out;
    }

    private static Object[] decomposeApp(Expr e) {
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
        return new Object[]{cur, args};
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

    private static Name stripCtorPrefix(Name ctorName, Name indName) {
        if (ctorName.equals(indName)) return Name.ANONYMOUS_NAME;
        if (hasPrefix(ctorName, indName)) {
            return ctorName.replacePrefix(indName, Name.ANONYMOUS_NAME);
        }
        return ctorName;
    }

    private static Object appendAfterIH(Object name) {
        if (name instanceof Name) {
            Name n = (Name) name;
            if (n.tag == Name.STR) return Name.mkStr(n.prefix, n.str + "_ih");
            return Name.mkStr(n, "_ih");
        }
        return name + "_ih";
    }

    private static boolean hasPrefix(Name n, Name prefix) {
        if (n == null || prefix == null) return false;
        if (n.equals(prefix)) return true;
        return n.prefix != null && hasPrefix(n.prefix, prefix);
    }
}
