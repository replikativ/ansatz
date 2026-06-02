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
 * <p>Recursor type/rule generation is delegated to RecursorGenerator so the
 * recursor logic can be studied side-by-side with Lean's mk_rec_infos,
 * mk_rec_rules, and declare_recursors.
 */
final class InductiveChecker {
    private final Env baseEnv;
    private Env workingEnv;
    private final InductiveBundle bundle;
    private final long fuel;
    private final Object[] levelValues;
    private final boolean hasLevelParams;

    private final ArrayList<LocalDecl> params = new ArrayList<>();
    private final int[] numIndices;
    private final Expr[] indConsts;
    private RecursorGenerator recursorGenerator;
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
    }

    Env run() {
        checkInductiveTypes();
        declareInductiveTypes();
        checkConstructors();
        declareConstructors();
        initElimLevel();
        initKTarget();
        initRecursorGenerator();
        recursorGenerator.mkRecInfos();
        workingEnv = recursorGenerator.checkAndDeclareRecursors();
        return workingEnv;
    }

    void prepareRecursorState() {
        checkInductiveTypes();
        declareInductiveTypes();
        checkConstructors();
        declareConstructors();
        initElimLevel();
        initKTarget();
        initRecursorGenerator();
        recursorGenerator.mkRecInfos();
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
            } else if (!Level.eq(resultLevel, lvl)) {
                throw new RuntimeException("mutually inductive types must live in the same universe");
            }
            indConsts[dIdx] = Expr.mkConst(ind.name, levelValues, hasLevelParams);
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
                Expr s = tc.ensureSortExpr(tc.inferType((Expr) type.o1));
                if (!Level.eq((Level) s.o0, Level.ZERO_LEVEL)) {
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

    private void initRecursorGenerator() {
        recursorGenerator = new RecursorGenerator(
            workingEnv,
            bundle,
            fuel,
            levelValues,
            hasLevelParams,
            params,
            numIndices,
            indConsts,
            elimLevel,
            nextLocalId);
    }

    Expr debugBuildExpectedRecursorType(int recIdx) {
        return recursorGenerator.debugBuildExpectedRecursorType(recIdx);
    }

    Expr debugBuildNormalizedExpectedRecursorType(int recIdx, ConstantInfo recCi) {
        return recursorGenerator.debugBuildNormalizedExpectedRecursorType(recIdx, recCi);
    }

    ConstantInfo.RecursorRule[] debugBuildExpectedRecursorRules(int recIdx, ConstantInfo recCi) {
        return recursorGenerator.debugBuildExpectedRecursorRules(recIdx, recCi);
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
                        lowerConstructorNameForRecursor(elim, auxName, rule.ctor),
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
            if (!TypeChecker.exprDeepEquals(restoredType, expected.type)) {
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
            if (!TypeChecker.exprDeepEquals(restoredType, expected.type)) {
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
            if (!TypeChecker.exprDeepEquals(restoredType, expected.type)) {
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
            Name loweredExpectedCtor = lowerConstructorNameForRecursor(elim, auxRec.name, expectedRule.ctor);
            if (!auxRule.ctor.equals(loweredExpectedCtor)) {
                throw new RuntimeException(
                    "nested inductive recursor constructor mismatch for " + expected.name + " rule #" + (i + 1));
            }
            Expr restoredRhs = elim.restoreNested(auxRule.rhs, elim.auxRecToRestoredRec);
            if (!TypeChecker.exprDeepEquals(restoredRhs, expectedRule.rhs)) {
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

    private static Name lowerConstructorNameForRecursor(NestedElimResult elim, Name auxRecName, Name restoredCtorName) {
        Name auxIndName = recursorInductiveName(elim, auxRecName);
        if (auxIndName == null) return lowerConstructorName(elim, restoredCtorName);

        Name restoredPrefix = elim.auxPrefixToRestoredPrefix.get(auxIndName);
        if (restoredPrefix == null) return restoredCtorName;

        Name lowered = restoredCtorName.replacePrefix(restoredPrefix, auxIndName);
        return lowered.equals(restoredCtorName) ? restoredCtorName : lowered;
    }

    private static Name recursorInductiveName(NestedElimResult elim, Name recName) {
        for (ConstantInfo ind : elim.auxBundle.inductives) {
            Name expected = Name.mkStr(ind.name, "rec");
            if (expected.equals(recName)) return ind.name;
        }
        return null;
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
