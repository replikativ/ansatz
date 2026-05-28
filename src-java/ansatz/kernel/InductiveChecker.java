package ansatz.kernel;

import java.util.ArrayList;
import java.util.HashMap;

/**
 * Lean-shaped inductive checker object.
 *
 * <p>This owns one inductive bundle admission run and makes the phase structure
 * explicit, closer to Lean's add_inductive_fn:
 * check inductive headers -> declare inductives -> check constructors ->
 * declare constructors -> handle recursors.
 *
 * <p>The checker regenerates the recursor type and reduction rules and compares
 * them with the imported constants before admitting the bundle.
 */
final class InductiveChecker {
    private static final Object BINDER_DEFAULT = clojure.lang.Keyword.intern(null, "default");
    private static final Object BINDER_IMPLICIT = clojure.lang.Keyword.intern(null, "implicit");

    private static final class LocalDecl {
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

    private static final class RecInfo {
        final ArrayList<LocalDecl> indices = new ArrayList<>();
        LocalDecl motive;
        LocalDecl major;
        final ArrayList<LocalDecl> minors = new ArrayList<>();
    }

    private final Env baseEnv;
    private Env workingEnv;
    private final InductiveBundle bundle;
    private final long fuel;
    private final Object[] levelValues;
    private final boolean hasLevelParams;

    private final ArrayList<LocalDecl> params = new ArrayList<>();
    private final int[] numIndices;
    private final Expr[] indConsts;
    private final RecInfo[] recInfos;
    private Level resultLevel = Level.ZERO_LEVEL;
    private boolean isResultNeverZero;
    private Level elimLevel = Level.ZERO_LEVEL;
    private boolean kTarget;
    private long nextLocalId = 1;

    InductiveChecker(Env env, InductiveBundle bundle, long fuel) {
        this.baseEnv = env;
        this.workingEnv = env;
        this.bundle = bundle;
        this.fuel = fuel;
        this.levelValues = new Object[bundle.levelParams.length];
        for (int i = 0; i < bundle.levelParams.length; i++) {
            this.levelValues[i] = Level.param((Name) bundle.levelParams[i]);
        }
        this.hasLevelParams = levelValues.length > 0;
        this.numIndices = new int[bundle.inductives.length];
        this.indConsts = new Expr[bundle.inductives.length];
        this.recInfos = new RecInfo[bundle.inductives.length];
    }

    Env run() {
        checkInductiveTypes();
        declareInductiveTypes();
        checkConstructors();
        declareConstructors();
        initElimLevel();
        initKTarget();
        mkRecInfos();
        checkAndDeclareRecursors();
        return workingEnv;
    }

    void prepareRecursorState() {
        checkInductiveTypes();
        declareInductiveTypes();
        checkConstructors();
        declareConstructors();
        initElimLevel();
        initKTarget();
        mkRecInfos();
    }

    private void checkInductiveTypes() {
        boolean first = true;
        TypeChecker tc = new TypeChecker(baseEnv, bundle.isUnsafe ? TypeChecker.DEFN_UNSAFE : TypeChecker.DEFN_SAFE, bundle.levelParams);
        tc.setFuel(fuel);
        for (int dIdx = 0; dIdx < bundle.inductives.length; dIdx++) {
            ConstantInfo ind = bundle.inductives[dIdx];
            TypeChecker.checkInductiveHeader(baseEnv, ind, fuel);
            Expr type = ind.type;
            int i = 0;
            type = tc.whnfExpr(type);
            while (type.tag == Expr.FORALL) {
                if (i < bundle.numParams) {
                    if (first) {
                        LocalDecl param = mkLocalDeclFor(tc, type);
                        params.add(param);
                        type = Reducer.instantiate1((Expr) type.o2, param.fvar);
                    } else {
                        if (!tc.isDefEq((Expr) type.o1, params.get(i).type)) {
                            throw new RuntimeException("parameters of all inductive datatypes must match");
                        }
                        type = Reducer.instantiate1((Expr) type.o2, params.get(i).fvar);
                    }
                } else {
                    LocalDecl idx = mkLocalDeclFor(tc, type);
                    type = Reducer.instantiate1((Expr) type.o2, idx.fvar);
                    numIndices[dIdx]++;
                }
                i++;
                type = tc.whnfExpr(type);
            }
            if (i != bundle.numParams + numIndices[dIdx]) {
                throw new RuntimeException("number of parameters mismatch in inductive datatype declaration");
            }
            Expr sort = tc.ensureSortExpr(type);
            Level lvl = (Level) sort.o0;
            if (first) {
                resultLevel = lvl;
                isResultNeverZero = Level.isNeverZero(lvl);
            } else if (!resultLevel.equals(lvl)) {
                throw new RuntimeException("mutually inductive types must live in the same universe");
            }
            indConsts[dIdx] = Expr.mkConst(ind.name, levelValues, hasLevelParams);
            recInfos[dIdx] = new RecInfo();
            first = false;
        }
    }

    private void declareInductiveTypes() {
        for (ConstantInfo ind : bundle.inductives) {
            workingEnv = workingEnv.addConstant(ind);
        }
    }

    private void checkConstructors() {
        for (ConstantInfo ctor : bundle.ctors) {
            TypeChecker.checkConstructorDeclaration(workingEnv, ctor, fuel);
        }
    }

    private void declareConstructors() {
        for (ConstantInfo ctor : bundle.ctors) {
            workingEnv = workingEnv.addConstant(ctor);
        }
    }

    private void checkAndDeclareRecursors() {
        for (int i = 0; i < bundle.recursors.length; i++) {
            ConstantInfo rec = bundle.recursors[i];
            Expr expectedType = buildExpectedRecursorType(i);
            compareGeneratedType(rec, expectedType);
            ConstantInfo.RecursorRule[] expectedRules = buildExpectedRecursorRules(i, rec);
            compareGeneratedRules(rec, expectedRules);
            TypeChecker.checkRecursorDeclaration(workingEnv, rec, fuel);
            workingEnv = workingEnv.addConstant(rec);
            TypeChecker.validateRecursorDeclarationRules(workingEnv, rec);
        }
    }

    private void initElimLevel() {
        if (elimOnlyAtUniverseZero()) {
            elimLevel = Level.ZERO_LEVEL;
            return;
        }
        Name u = Name.fromString("u");
        int i = 1;
        while (containsLevelParam(u)) {
            u = Name.fromString("u").appendAfter(i);
            i++;
        }
        elimLevel = Level.param(u);
    }

    private boolean elimOnlyAtUniverseZero() {
        if (isResultNeverZero) return false;
        if (bundle.inductives.length > 1) return true;
        ConstantInfo ind = bundle.inductives[0];
        int numIntros = ind.ctors != null ? ind.ctors.length : 0;
        if (numIntros > 1) return true;
        if (numIntros == 0) return false;

        ConstantInfo ctor = workingEnv.lookup(ind.ctors[0]);
        if (ctor == null || !ctor.isCtor()) return false;
        TypeChecker tc = new TypeChecker(workingEnv, bundle.isUnsafe ? TypeChecker.DEFN_UNSAFE : TypeChecker.DEFN_SAFE, bundle.levelParams);
        tc.setFuel(fuel);
        addParamsTo(tc);

        Expr type = ctor.type;
        int i = 0;
        ArrayList<Expr> toCheck = new ArrayList<>();
        while (type.tag == Expr.FORALL) {
            LocalDecl fvar = mkLocalDeclFor(tc, type);
            if (i >= bundle.numParams) {
                Expr s = tc.ensureSortExpr(tc.check((Expr) type.o1));
                if (!((Level) s.o0).equals(Level.ZERO_LEVEL)) {
                    toCheck.add(fvar.fvar);
                }
            }
            type = Reducer.instantiate1((Expr) type.o2, fvar.fvar);
            i++;
        }
        Expr[] resultArgs = getAppArgs(type);
        for (Expr arg : toCheck) {
            boolean found = false;
            for (Expr resultArg : resultArgs) {
                if (resultArg.isEqp(arg) || TypeChecker.exprDeepEquals(resultArg, arg)) {
                    found = true;
                    break;
                }
            }
            if (!found) return true;
        }
        return false;
    }

    private void initKTarget() {
        kTarget =
            bundle.inductives.length == 1 &&
            resultLevel.equals(Level.ZERO_LEVEL) &&
            bundle.inductives[0].ctors != null &&
            bundle.inductives[0].ctors.length == 1;
        if (!kTarget) return;
        ConstantInfo ctor = workingEnv.lookup(bundle.inductives[0].ctors[0]);
        Expr type = ctor.type;
        int i = 0;
        while (type.tag == Expr.FORALL) {
            if (i >= bundle.numParams) {
                kTarget = false;
                break;
            }
            type = (Expr) type.o2;
            i++;
        }
    }

    private void mkRecInfos() {
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
            info.major = mkLocalDecl(tc, "t", majorType, BINDER_DEFAULT);
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
                    Object ihName = uI.name instanceof Name ? Name.mkStr((Name) uI.name, "_ih") : uI.name + "_ih";
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

    private ArrayList<LocalDecl> collectMotives() {
        ArrayList<LocalDecl> out = new ArrayList<>();
        for (RecInfo info : recInfos) out.add(info.motive);
        return out;
    }

    private ArrayList<LocalDecl> collectMinors() {
        ArrayList<LocalDecl> out = new ArrayList<>();
        for (RecInfo info : recInfos) out.addAll(info.minors);
        return out;
    }

    private ConstantInfo.RecursorRule[] buildExpectedRecursorRules(int recIdx, ConstantInfo recCi) {
        if (recCi.rules == null) return null;
        if (recCi.numMotives > recCi.all.length) {
            throw new RuntimeException("expected non-nested recursor declaration: " + recCi.name);
        }

        int np = recCi.numParams;
        int nm = recCi.numMotives;
        int nmi = recCi.numMinors;
        Object[] recLevelValues = getRecLevelValues(recCi);
        boolean recHasLevelParams = recLevelValues.length > 0;

        int minorOffset = 0;
        for (int i = 0; i < recIdx; i++) {
            minorOffset += recInfos[i].minors.size();
        }

        ConstantInfo.RecursorRule[] out = new ConstantInfo.RecursorRule[recCi.rules.length];
        int minorIdx = minorOffset;
        for (int ruleIdx = 0; ruleIdx < recCi.rules.length; ruleIdx++) {
            ConstantInfo.RecursorRule rule = recCi.rules[ruleIdx];
            ConstantInfo ctorCi = workingEnv.lookup(rule.ctor);
            if (ctorCi == null || !ctorCi.isCtor()) {
                throw new RuntimeException("Recursor rule references unknown constructor: " + rule.ctor);
            }
            int nf = rule.nfields;
            Expr imported = rule.rhs;
            int lambdaCount = 0;
            while (imported.tag == Expr.LAM) {
                imported = (Expr) imported.o2;
                lambdaCount++;
            }

            Expr ctorType = ctorCi.type;
            for (int i = 0; i < np; i++) {
                if (ctorType.tag != Expr.FORALL) {
                    throw new RuntimeException("Constructor " + rule.ctor +
                        " type has fewer binders than numParams=" + np);
                }
                ctorType = (Expr) ctorType.o2;
            }

            boolean[] isRecField = new boolean[nf];
            int[] recFieldExtraPis = new int[nf];
            int[] recFieldIndIdx = new int[nf];
            Expr[][] recFieldIndices = new Expr[nf][];
            Expr[] fieldTypesRaw = new Expr[nf];

            TypeChecker fieldTc = new TypeChecker(workingEnv);
            fieldTc.setFuel(fuel);
            HashMap<Name, Integer> inductiveIdxByName = new HashMap<>();
            for (int i = 0; i < bundle.inductives.length; i++) {
                inductiveIdxByName.put(bundle.inductives[i].name, i);
            }

            Expr ctorTypeWalk = ctorType;
            for (int fi = 0; fi < nf; fi++) {
                if (ctorTypeWalk.tag != Expr.FORALL) break;
                Expr fieldType = (Expr) ctorTypeWalk.o1;
                fieldTypesRaw[fi] = fieldType;

                Expr ft = fieldTc.whnfExpr(fieldType);
                int extraPis = 0;
                while (ft.tag == Expr.FORALL) {
                    ft = fieldTc.whnfExpr((Expr) ft.o2);
                    extraPis++;
                }

                Object[] app = decomposeApp(ft);
                Expr head = (Expr) app[0];
                Expr[] args = (Expr[]) app[1];

                if (head.tag == Expr.CONST) {
                    Name headName = (Name) head.o0;
                    Integer indIdx = inductiveIdxByName.get(headName);
                    if (indIdx != null) {
                        ConstantInfo indCi = bundle.inductives[indIdx];
                        int indNp = indCi.numParams;
                        int expectedArgs = indNp + indCi.numIndices;
                        if (args.length == expectedArgs) {
                            boolean paramsOk = true;
                            for (int pi = 0; pi < indNp; pi++) {
                                Expr paramArg = args[pi];
                                long expectedBvar = np + fi + extraPis - 1 - pi;
                                if (paramArg.tag != Expr.BVAR || paramArg.longVal != expectedBvar) {
                                    paramsOk = false;
                                    break;
                                }
                            }
                            if (paramsOk) {
                                isRecField[fi] = true;
                                recFieldExtraPis[fi] = extraPis;
                                recFieldIndIdx[fi] = indIdx;
                                int numInd = indCi.numIndices;
                                recFieldIndices[fi] = new Expr[numInd];
                                for (int j = 0; j < numInd; j++) {
                                    recFieldIndices[fi][j] = args[indNp + j];
                                }
                            }
                        }
                    }
                }
                ctorTypeWalk = (Expr) ctorTypeWalk.o2;
            }

            Expr expectedBody = Expr.bvar(nf + nmi - 1 - minorIdx);
            for (int fi = 0; fi < nf; fi++) {
                expectedBody = Expr.app(expectedBody, Expr.bvar(nf - 1 - fi));
            }
            for (int fi = 0; fi < nf; fi++) {
                if (!isRecField[fi]) continue;
                int indIdx = recFieldIndIdx[fi];
                Expr[] indices = recFieldIndices[fi];
                int extraPis = recFieldExtraPis[fi];
                Name targetRecName = bundle.inductives.length == 1 ? recCi.name : bundle.recursors[indIdx].name;
                if (extraPis == 0) {
                    Expr ih = Expr.mkConst(targetRecName, recLevelValues, recHasLevelParams);
                    for (int j = 0; j < np; j++) ih = Expr.app(ih, Expr.bvar(lambdaCount - 1 - j));
                    for (int j = 0; j < nm; j++) ih = Expr.app(ih, Expr.bvar(nf + nmi + nm - 1 - j));
                    for (int j = 0; j < nmi; j++) ih = Expr.app(ih, Expr.bvar(nf + nmi - 1 - j));
                    if (indices != null && indices.length > 0) {
                        for (Expr index : indices) ih = Expr.app(ih, TypeChecker.reindexBvarsIH(index, 0, fi, nm + nmi, nf));
                    }
                    ih = Expr.app(ih, Expr.bvar(nf - 1 - fi));
                    expectedBody = Expr.app(expectedBody, ih);
                } else {
                    Expr ihInner = Expr.mkConst(targetRecName, recLevelValues, recHasLevelParams);
                    for (int j = 0; j < np; j++) ihInner = Expr.app(ihInner, Expr.bvar(lambdaCount - 1 - j + extraPis));
                    for (int j = 0; j < nm; j++) ihInner = Expr.app(ihInner, Expr.bvar(nf + nmi + nm - 1 - j + extraPis));
                    for (int j = 0; j < nmi; j++) ihInner = Expr.app(ihInner, Expr.bvar(nf + nmi - 1 - j + extraPis));
                    if (indices != null && indices.length > 0) {
                        for (Expr index : indices) ihInner = Expr.app(ihInner, TypeChecker.reindexBvarsIH(index, extraPis, fi, nm + nmi, nf));
                    }
                    Expr fApp = Expr.bvar(nf - 1 - fi + extraPis);
                    for (int j = 0; j < extraPis; j++) fApp = Expr.app(fApp, Expr.bvar(extraPis - 1 - j));
                    ihInner = Expr.app(ihInner, fApp);
                    Expr ih = ihInner;
                    for (int j = extraPis - 1; j >= 0; j--) {
                        Expr ftj = fieldTypesRaw[fi];
                        for (int k = 0; k < j; k++) ftj = (Expr) ftj.o2;
                        Expr binderType = TypeChecker.reindexBvarsIH((Expr) ftj.o1, j, fi, nm + nmi, nf);
                        ih = Expr.lam(ftj.o0, binderType, ih, ftj.o3);
                    }
                    expectedBody = Expr.app(expectedBody, ih);
                }
            }
            Expr expectedRhs = rebuildRuleLambdas(rule.rhs, expectedBody);
            out[ruleIdx] = new ConstantInfo.RecursorRule(rule.ctor, rule.nfields, expectedRhs);
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

    private Object[] getRecLevelValues(ConstantInfo recCi) {
        Object[] out = new Object[recCi.levelParams.length];
        for (int i = 0; i < recCi.levelParams.length; i++) {
            out[i] = Level.param((Name) recCi.levelParams[i]);
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
            if (!actual.ctor.equals(expected.ctor) || actual.nfields != expected.nfields ||
                    !TypeChecker.exprDeepEquals(actual.rhs, expected.rhs)) {
                throw new RuntimeException("generated recursor rule mismatch for " + importedRec.name +
                    " rule #" + (i + 1));
            }
        }
    }

    static ConstantInfo[] lowerImportedRecursors(InductiveBundle original, NestedElimResult elim) {
        HashMap<Name, ConstantInfo> byAuxName = new HashMap<>();
        for (int i = 0; i < original.recursors.length; i++) {
            ConstantInfo rec = original.recursors[i];
            Name auxName = lowerRecursorName(elim, rec.name);
            Expr auxType = elim.lowerToAux(rec.type);
            ConstantInfo.RecursorRule[] auxRules = null;
            if (rec.rules != null) {
                auxRules = new ConstantInfo.RecursorRule[rec.rules.length];
                for (int j = 0; j < rec.rules.length; j++) {
                    ConstantInfo.RecursorRule rule = rec.rules[j];
                    auxRules[j] = new ConstantInfo.RecursorRule(
                        lowerConstructorName(elim, rule.ctor),
                        rule.nfields,
                        elim.lowerToAux(rule.rhs));
                }
            }
            ConstantInfo lowered = ConstantInfo.mkRecursor(
                auxName,
                rec.levelParams,
                auxType,
                elim.auxBundle.allNames(),
                rec.numParams,
                rec.numIndices,
                rec.numMotives,
                rec.numMinors,
                auxRules,
                rec.isK,
                rec.isUnsafe);
            byAuxName.put(auxName, lowered);
        }

        ConstantInfo[] out = new ConstantInfo[elim.auxBundle.inductives.length];
        for (int i = 0; i < elim.auxBundle.inductives.length; i++) {
            Name expectedRecName = Name.mkStr(elim.auxBundle.inductives[i].name, "rec");
            ConstantInfo rec = byAuxName.get(expectedRecName);
            if (rec == null) {
                throw new RuntimeException("missing imported recursor for auxiliary inductive " +
                    elim.auxBundle.inductives[i].name);
            }
            out[i] = rec;
        }
        return out;
    }

    static void compareRestoredImportedBundle(InductiveBundle original, NestedElimResult elim, ConstantInfo[] auxRecursors) {
        compareInductiveTypes(original.inductives, elim);
        compareConstructorTypes(original.ctors, elim);
        compareRecursors(original.recursors, auxRecursors, elim);
    }

    static Env admitOriginalBundle(Env env, InductiveBundle bundle) {
        Env current = env;
        for (ConstantInfo ind : bundle.inductives) current = current.addConstant(ind);
        for (ConstantInfo ctor : bundle.ctors) current = current.addConstant(ctor);
        for (ConstantInfo rec : bundle.recursors) current = current.addConstant(rec);
        return current;
    }

    private static void compareInductiveTypes(ConstantInfo[] original, NestedElimResult elim) {
        if (original.length > elim.auxBundle.inductives.length) {
            throw new RuntimeException("invalid nested inductive bundle: auxiliary bundle lost original inductive types");
        }
        for (int i = 0; i < original.length; i++) {
            ConstantInfo restored = elim.auxBundle.inductives[i];
            ConstantInfo expected = original[i];
            Expr restoredType = elim.restoreNested(restored.type);
            if (!restoredType.equals(expected.type)) {
                throw new RuntimeException("nested inductive restoration mismatch for " + expected.name + " type");
            }
        }
    }

    private static void compareConstructorTypes(ConstantInfo[] original, NestedElimResult elim) {
        HashMap<Name, ConstantInfo> auxCtorMap = elim.auxBundle.ctorMap();
        for (ConstantInfo expected : original) {
            ConstantInfo restored = auxCtorMap.get(lowerConstructorName(elim, expected.name));
            if (restored == null) {
                throw new RuntimeException("invalid nested inductive bundle: missing restored constructor " + expected.name);
            }
            Expr restoredType = elim.restoreNested(restored.type);
            if (!restoredType.equals(expected.type)) {
                throw new RuntimeException("nested inductive restoration mismatch for constructor " + expected.name);
            }
        }
    }

    private static void compareRecursors(ConstantInfo[] original, ConstantInfo[] auxRecursors, NestedElimResult elim) {
        HashMap<Name, ConstantInfo> auxRecMap = new HashMap<>();
        for (ConstantInfo auxRec : auxRecursors) auxRecMap.put(auxRec.name, auxRec);
        for (ConstantInfo expected : original) {
            Name auxName = lowerRecursorName(elim, expected.name);
            ConstantInfo auxRec = auxRecMap.get(auxName);
            if (auxRec == null) {
                throw new RuntimeException("invalid nested inductive bundle: missing aux recursor for " + expected.name);
            }
            Expr restoredType = elim.restoreNested(auxRec.type, elim.auxRecToRestoredRec);
            if (!restoredType.equals(expected.type)) {
                throw new RuntimeException("nested inductive restoration mismatch for recursor " + expected.name);
            }
            compareRecursorRules(expected, auxRec, elim);
        }
    }

    private static void compareRecursorRules(ConstantInfo expected, ConstantInfo auxRec, NestedElimResult elim) {
        if (expected.rules == null && auxRec.rules == null) return;
        if (expected.rules == null || auxRec.rules == null || expected.rules.length != auxRec.rules.length) {
            throw new RuntimeException("nested inductive recursor rule mismatch for " + expected.name);
        }
        for (int i = 0; i < expected.rules.length; i++) {
            ConstantInfo.RecursorRule expectedRule = expected.rules[i];
            ConstantInfo.RecursorRule auxRule = auxRec.rules[i];
            Name loweredExpectedCtor = lowerConstructorName(elim, expectedRule.ctor);
            if (!auxRule.ctor.equals(loweredExpectedCtor)) {
                throw new RuntimeException(
                    "nested inductive recursor constructor mismatch for " + expected.name + " rule #" + (i + 1));
            }
            Expr restoredRhs = elim.restoreNested(auxRule.rhs, elim.auxRecToRestoredRec);
            if (!restoredRhs.equals(expectedRule.rhs)) {
                throw new RuntimeException(
                    "nested inductive recursor RHS mismatch for " + expected.name + " rule #" + (i + 1));
            }
        }
    }

    private static Name lowerRecursorName(NestedElimResult elim, Name restoredName) {
        for (java.util.Map.Entry<Name, Name> entry : elim.auxRecToRestoredRec.entrySet()) {
            if (entry.getValue().equals(restoredName)) return entry.getKey();
        }
        return restoredName;
    }

    private static Name lowerConstructorName(NestedElimResult elim, Name restoredCtorName) {
        for (java.util.Map.Entry<Name, Name> entry : elim.auxPrefixToRestoredPrefix.entrySet()) {
            Name auxPrefix = entry.getKey();
            Name restoredPrefix = entry.getValue();
            if (restoredCtorName.equals(restoredPrefix) || hasPrefix(restoredCtorName, restoredPrefix)) {
                return restoredCtorName.replacePrefix(restoredPrefix, auxPrefix);
            }
        }
        return restoredCtorName;
    }

    private static boolean hasPrefix(Name n, Name prefix) {
        if (n == null || prefix == null) return false;
        if (n.equals(prefix)) return true;
        return n.prefix != null && hasPrefix(n.prefix, prefix);
    }

    private LocalDecl mkLocalDecl(TypeChecker tc, Object name, Expr type, Object binderInfo) {
        long id = nextLocalId++;
        tc.addLocalDecl(id, name, type);
        return new LocalDecl(id, name, type, binderInfo);
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

    private boolean containsLevelParam(Name name) {
        for (Object lp : bundle.levelParams) {
            if (name.equals(lp)) return true;
        }
        return false;
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

    private static Expr rebuildRuleLambdas(Expr template, Expr body) {
        ArrayList<Expr> binders = new ArrayList<>();
        Expr cur = template;
        while (cur.tag == Expr.LAM) {
            binders.add(cur);
            cur = (Expr) cur.o2;
        }
        Expr result = body;
        for (int i = binders.size() - 1; i >= 0; i--) {
            Expr lam = binders.get(i);
            result = Expr.lam(lam.o0, (Expr) lam.o1, result, lam.o3);
        }
        return result;
    }

    private static ArrayList<LocalDecl> singleton(LocalDecl local) {
        ArrayList<LocalDecl> out = new ArrayList<>(1);
        out.add(local);
        return out;
    }

    private static ArrayList<Expr> singletonExpr(Expr e) {
        ArrayList<Expr> out = new ArrayList<>(1);
        out.add(e);
        return out;
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
}
