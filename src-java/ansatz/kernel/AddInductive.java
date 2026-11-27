package ansatz.kernel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Inductive admission — a port of Lean v4.36.0's {@code environment::add_inductive}
 * (src/kernel/inductive.cpp). The input is an {@link InductiveDecl}; every {@link ConstantInfo}
 * of the block — types, constructors, recursors with their rules, auxiliary recursors of a nested
 * declaration — is generated here, so no caller-supplied metadata reaches a kernel judgment.
 *
 * <p>The steps are Lean's: closedness and reserved-name preflight
 * ({@code check_no_metavar_no_fvar}, {@code check_no_nested_aux}), {@code check_uniform_ind_occs},
 * nested elimination ({@link ElimNested}), {@code add_inductive_fn} on the auxiliary block
 * ({@link Core}), restoration of the nested occurrences, and the final-environment checks.
 * One fuel budget covers every type checker the admission creates.
 */
public final class AddInductive {
    private AddInductive() {}

    static final Object BINDER_DEFAULT = clojure.lang.Keyword.intern(null, "default");
    static final Object BINDER_IMPLICIT = clojure.lang.Keyword.intern(null, "implicit");
    private static final Name OPT_PARAM = Name.fromString("optParam");
    private static final Name AUTO_PARAM = Name.fromString("autoParam");

    /** Lean's environment::add_inductive. */
    public static Env add(Env env, InductiveDecl d, long fuel) {
        for (InductiveDecl.Type t : d.types) {
            checkNoMVarNoFVar(t.name, t.type);
            checkNoNestedAux(t.name, t.type);
            for (InductiveDecl.Constructor c : t.constructors) {
                checkNoMVarNoFVar(c.name, c.type);
                checkNoNestedAux(c.name, c.type);
            }
        }
        checkUniformIndOccs(d);
        ElimNested.Result res = new ElimNested(env, d).run();
        int nnested = res.aux2nested.size();
        Budget budget = new Budget(fuel, d.isUnsafe);
        Env auxEnv = new Core(env, res.auxDecl, nnested, budget).run();
        if (nnested == 0) return auxEnv;
        return restoreNested(env, d, res, auxEnv, budget);
    }

    /**
     * The constants {@link #add} generated for {@code d}, in Lean's order: each type, its
     * constructors and its recursor, then the auxiliary recursors {@code <first>.rec_<i>}.
     */
    public static List<ConstantInfo> constants(Env env, InductiveDecl d) {
        ArrayList<ConstantInfo> out = new ArrayList<>();
        for (InductiveDecl.Type t : d.types) {
            out.add(env.lookupOrThrow(t.name));
            for (InductiveDecl.Constructor c : t.constructors) out.add(env.lookupOrThrow(c.name));
            out.add(env.lookupOrThrow(recName(t.name)));
        }
        for (Name aux : auxRecNames(env, d)) out.add(env.lookupOrThrow(aux));
        return out;
    }

    /** The auxiliary recursor names of an admitted declaration: {@code <first>.rec_1 …}, one per auxiliary type. */
    static List<Name> auxRecNames(Env env, InductiveDecl d) {
        Name first = d.types.get(0).name;
        int naux = env.lookupOrThrow(recName(first)).numMotives - d.types.size();
        ArrayList<Name> out = new ArrayList<>();
        for (int i = 1; i <= naux; i++) out.add(recName(first).appendAfter(i));
        return out;
    }

    static Name recName(Name ind) {
        return Name.mkStr(ind, "rec");
    }

    // ========================================================================
    // Preflight: closedness, the reserved `_nested` prefix, uniform occurrences
    // ========================================================================

    /** Lean's check_no_metavar_no_fvar. */
    static void checkNoMVarNoFVar(Name n, Expr e) {
        if (e.hasMVar()) throw new RuntimeException("declaration has metavariables '" + n + "'");
        if (e.hasFVar()) throw new RuntimeException("declaration has free variables '" + n + "'");
    }

    /** Lean's check_no_nested_aux: no constant or projection owner under {@code _nested}. */
    static void checkNoNestedAux(Name n, Expr e) {
        if (find(e, t -> (t.tag == Expr.CONST || t.tag == Expr.PROJ) && isPrefixOf(ElimNested.NESTED, (Name) t.o0)))
            throw new RuntimeException("invalid declaration '" + n + "', it uses the reserved prefix '" + ElimNested.NESTED + "'");
    }

    private static boolean isPrefixOf(Name prefix, Name n) {
        for (Name p = n; p != null; p = p.prefix) if (p.equals(prefix)) return true;
        return false;
    }

    /**
     * Lean's check_uniform_ind_occs: every syntactic occurrence of a type being declared in a
     * constructor type is applied to the declaration's universe levels and to its parameters.
     * Later phases look at constructor types modulo whnf, which can erase an occurrence.
     */
    static void checkUniformIndOccs(InductiveDecl d) {
        int np = d.numParams;
        Object[] lvls = paramLevels(d);
        HashSet<Name> names = new HashSet<>();
        for (InductiveDecl.Type t : d.types) names.add(t.name);
        for (InductiveDecl.Type t : d.types)
            for (InductiveDecl.Constructor c : t.constructors)
                forEachWithOffset(c.type, (e, offset) -> {
                    Expr fn = appFn(e);
                    if (fn.tag != Expr.CONST || !names.contains((Name) fn.o0)) return true;
                    Expr[] args = appArgs(e);
                    if (args.length > np) return true;   // over-applied: the indices are checked as subterms
                    boolean ok = args.length == np && offset >= np && Expr.levelsEquals(fn.o1, lvls);
                    for (int i = 0; ok && i < np; i++)
                        ok = args[i].tag == Expr.BVAR && args[i].longVal == offset - 1 - i;
                    if (!ok)
                        throw new RuntimeException("invalid occurrence of datatype '" + fn.o0 + "' being declared: it must be "
                            + "applied to the parameters and universe levels of the mutual declaration");
                    return false;
                });
    }

    // ========================================================================
    // Restoring a nested declaration (environment::add_inductive, nnested > 0)
    // ========================================================================

    private static Env restoreNested(Env env, InductiveDecl d, ElimNested.Result res, Env auxEnv, Budget budget) {
        Object[] allNames = new Object[d.types.size()];
        for (int i = 0; i < allNames.length; i++) allNames[i] = d.types.get(i).name;
        // mk_aux_rec_name_map: the auxiliary recursors become <first>.rec_<i>
        ConstantInfo mainInfo = auxEnv.lookupOrThrow(d.types.get(0).name);
        LinkedHashMap<Name, Name> auxRecNameMap = new LinkedHashMap<>();
        for (int i = d.types.size(); i < mainInfo.all.length; i++)
            auxRecNameMap.put(recName((Name) mainInfo.all[i]), recName(d.types.get(0).name).appendAfter(i - d.types.size() + 1));

        Env out = env;
        ArrayList<Name> newRecNames = new ArrayList<>();
        for (InductiveDecl.Type t : d.types) {
            ConstantInfo ind = auxEnv.lookupOrThrow(t.name);
            // only `all` changes; the type is the declaration's own
            out = out.addConstant(ConstantInfo.mkInduct(ind.name, ind.levelParams, ind.type, ind.numParams,
                ind.numIndices, allNames, ind.ctors, ind.numNested, ind.isRec, ind.isReflexive, ind.isUnsafe));
            for (Name ctorName : ind.ctors) {
                ConstantInfo ctor = auxEnv.lookupOrThrow(ctorName);
                out = out.addConstant(ConstantInfo.mkCtor(ctor.name, ctor.levelParams, res.restore(ctor.type, auxEnv, Map.of()),
                    ctor.inductName, ctor.cidx, ctor.numParams, ctor.numFields, ctor.isUnsafe));
            }
            ConstantInfo rec = restoreRecursor(res, auxEnv, auxRecNameMap, allNames, recName(t.name));
            out = out.addConstant(rec);
            newRecNames.add(rec.name);
        }
        for (Name auxRec : auxRecNameMap.keySet()) {
            ConstantInfo rec = restoreRecursor(res, auxEnv, auxRecNameMap, allNames, auxRec);
            out = out.addConstant(rec);
            newRecNames.add(rec.name);
        }

        // The parametric arguments `Ds` of the replaced applications `I Ds` appear nowhere in the
        // auxiliary declaration: check them here, in the final environment (lean4#14577).
        TypeChecker tc = budget.next(out, d.levelParams());
        res.paramsLctx.addTo(tc, 0);
        for (Expr nested : res.aux2nested.values()) tc.check(nested);
        // Re-check everything restore_nested rewrote.
        tc = budget.next(out, d.levelParams());
        for (InductiveDecl.Type t : d.types)
            for (InductiveDecl.Constructor c : t.constructors) tc.check(out.lookupOrThrow(c.name).type);
        for (Name recN : newRecNames) {
            ConstantInfo rec = out.lookupOrThrow(recN);
            TypeChecker rtc = budget.next(out, rec.levelParams);
            rtc.check(rec.type);
            for (ConstantInfo.RecursorRule rule : rec.rules) rtc.check(rule.rhs);
        }
        return out;
    }

    /** process_rec: an auxiliary-block recursor under its restored name, type and rules. */
    private static ConstantInfo restoreRecursor(ElimNested.Result res, Env auxEnv, Map<Name, Name> auxRecNameMap,
                                                Object[] allNames, Name recN) {
        Name newRecName = auxRecNameMap.getOrDefault(recN, recN);
        ConstantInfo rec = auxEnv.lookupOrThrow(recN);
        ConstantInfo.RecursorRule[] rules = new ConstantInfo.RecursorRule[rec.rules.length];
        for (int i = 0; i < rules.length; i++) {
            ConstantInfo.RecursorRule rule = rec.rules[i];
            Name ctor = newRecName.equals(recN) ? rule.ctor : res.restoreConstructorName(auxEnv, rule.ctor);
            rules[i] = new ConstantInfo.RecursorRule(ctor, rule.nfields, res.restore(rule.rhs, auxEnv, auxRecNameMap));
        }
        return ConstantInfo.mkRecursor(newRecName, rec.levelParams, res.restore(rec.type, auxEnv, auxRecNameMap), allNames,
            rec.numParams, rec.numIndices, rec.numMotives, rec.numMinors, rules, rec.isK, rec.isUnsafe);
    }

    // ========================================================================
    // add_inductive_fn
    // ========================================================================

    /** One fuel budget across the checkers of an admission (Lean has no fuel; one budget per declaration). */
    static final class Budget {
        private final long fuel;
        private final byte safety;
        private TypeChecker last;

        Budget(long fuel, boolean unsafe) {
            this.fuel = fuel;
            this.safety = unsafe ? TypeChecker.DEFN_UNSAFE : TypeChecker.DEFN_SAFE;
        }

        TypeChecker next(Env env, Object[] levelParams) {
            TypeChecker tc = new TypeChecker(env, safety, levelParams);
            if (last == null) tc.setFuel(fuel); else tc.continueFuel(last);
            last = tc;
            return tc;
        }
    }

    /** Lean's add_inductive_fn: checks a declaration without nested occurrences and declares its constants. */
    static final class Core {
        private Env env;
        private final Budget budget;
        private final Object[] lparams;
        private final Object[] levels;
        private final int nparams;
        private final boolean isUnsafe;
        private final List<InductiveDecl.Type> indTypes;
        private final int nnested;
        private final int[] nindices;
        private final Expr[] indConsts;
        private final ArrayList<Expr> params = new ArrayList<>();
        private final LocalCtx lctx = new LocalCtx(1);
        private Level resultLevel;
        private boolean isNotZero;
        private Level elimLevel;
        private boolean kTarget;
        private final RecInfo[] recInfos;

        private TypeChecker tc;
        private Object[] tcLevelParams;
        private int tcLocals;

        private static final class RecInfo {
            Expr motive;
            final ArrayList<Expr> minors = new ArrayList<>();
            final ArrayList<Expr> indices = new ArrayList<>();
            Expr major;
        }

        Core(Env env, InductiveDecl d, int nnested, Budget budget) {
            this.env = env;
            this.budget = budget;
            this.lparams = d.levelParams();
            this.levels = paramLevels(d);
            this.nparams = d.numParams;
            this.isUnsafe = d.isUnsafe;
            this.indTypes = d.types;
            this.nnested = nnested;
            this.nindices = new int[indTypes.size()];
            this.indConsts = new Expr[indTypes.size()];
            this.recInfos = new RecInfo[indTypes.size()];
        }

        Env run() {
            checkDuplicatedUnivParams(lparams);
            checkInductiveTypes();
            declareInductiveTypes();
            checkConstructors();
            declareConstructors();
            initElimLevel();
            initKTarget();
            mkRecInfos();
            declareRecursors();
            checkRecursors();
            return env;
        }

        // --- the checker over the current environment and local context (Lean's tc()) ---

        private TypeChecker tc() {
            return tc(lparams);
        }

        private TypeChecker tc(Object[] lps) {
            if (tc == null || tc.getEnv() != env || tcLevelParams != lps) {
                tc = budget.next(env, lps);
                tcLevelParams = lps;
                tcLocals = 0;
            }
            lctx.addTo(tc, tcLocals);
            tcLocals = lctx.size();
            return tc;
        }

        private Expr whnf(Expr e) { return tc().whnfExpr(e); }
        private Expr inferType(Expr e) { return tc().inferType(e); }
        private boolean isDefEq(Expr a, Expr b) { return tc().isDefEq(a, b); }
        private Expr ensureType(Expr e) { return tc().ensureSortExpr(tc().inferType(e)); }

        private Expr mkLocalDecl(Object name, Expr type) {
            return lctx.mkLocalDecl(name, consumeTypeAnnotations(type), BINDER_DEFAULT);
        }

        private Expr mkLocalDeclFor(Expr pi) {
            return lctx.mkLocalDecl(pi.o0, consumeTypeAnnotations((Expr) pi.o1), pi.o3);
        }

        private void checkName(Name n) {
            if (env.lookup(n) != null) throw new RuntimeException("Constant already declared: " + n);
        }

        private void declare(ConstantInfo ci) {
            checkName(ci.name);
            env = env.addConstant(ci);
        }

        /**
         * Lean's check_inductive_types: the types are well formed and closed, share the
         * parameters, and live in equivalent universes. Initializes levels, the result level,
         * the index counts, the type constants and the parameters.
         */
        private void checkInductiveTypes() {
            boolean first = true;
            for (int idx = 0; idx < indTypes.size(); idx++) {
                InductiveDecl.Type indType = indTypes.get(idx);
                Expr type = indType.type;
                checkName(indType.name);
                checkName(recName(indType.name));
                checkNoMVarNoFVar(indType.name, type);
                tc().check(type);
                int i = 0;
                type = whnf(type);
                while (type.tag == Expr.FORALL) {
                    if (i < nparams) {
                        if (first) {
                            Expr param = mkLocalDeclFor(type);
                            params.add(param);
                            type = Reducer.instantiate1((Expr) type.o2, param);
                        } else {
                            if (!isDefEq((Expr) type.o1, paramType(i)))
                                throw new RuntimeException("parameters of all inductive datatypes must match");
                            type = Reducer.instantiate1((Expr) type.o2, params.get(i));
                        }
                        i++;
                    } else {
                        type = Reducer.instantiate1((Expr) type.o2, mkLocalDeclFor(type));
                        nindices[idx]++;
                    }
                    type = whnf(type);
                }
                if (i != nparams)
                    throw new RuntimeException("number of parameters mismatch in inductive datatype declaration");
                Level level = (Level) tc().ensureSortExpr(type).o0;
                if (first) {
                    resultLevel = level;
                    isNotZero = Level.isNeverZero(level);
                } else if (!Level.isEquivalent(level, resultLevel)) {
                    throw new RuntimeException("mutually inductive types must live in the same universe");
                }
                indConsts[idx] = Expr.mkConst(indType.name, levels, levels.length > 0);
                first = false;
            }
        }

        private Expr paramType(int i) {
            return lctx.get(params.get(i)).type;
        }

        /** Lean's is_rec: a type being declared occurs in a constructor field's type. */
        private boolean isRec() {
            for (InductiveDecl.Type t : indTypes)
                for (InductiveDecl.Constructor c : t.constructors)
                    for (Expr e = c.type; e.tag == Expr.FORALL; e = (Expr) e.o2)
                        if (find((Expr) e.o1, x -> isIndOcc(x))) return true;
            return false;
        }

        /** Lean's is_reflexive: a constructor field is a function into a type being declared. */
        private boolean isReflexive() {
            for (InductiveDecl.Type t : indTypes)
                for (InductiveDecl.Constructor c : t.constructors)
                    for (Expr e = c.type; e.tag == Expr.FORALL; e = (Expr) e.o2) {
                        Expr argType = (Expr) e.o1;
                        if (argType.tag == Expr.FORALL && hasIndOcc(argType)) return true;
                    }
            return false;
        }

        private Object[] allNames() {
            Object[] all = new Object[indTypes.size()];
            for (int i = 0; i < all.length; i++) all[i] = indTypes.get(i).name;
            return all;
        }

        /** Lean's declare_inductive_types. */
        private void declareInductiveTypes() {
            boolean rec = isRec();
            boolean reflexive = isReflexive();
            Object[] all = allNames();
            for (int idx = 0; idx < indTypes.size(); idx++) {
                InductiveDecl.Type t = indTypes.get(idx);
                Name[] ctorNames = new Name[t.constructors.size()];
                for (int j = 0; j < ctorNames.length; j++) ctorNames[j] = t.constructors.get(j).name;
                declare(ConstantInfo.mkInduct(t.name, lparams, t.type, nparams, nindices[idx], all, ctorNames,
                                              nnested, rec, reflexive, isUnsafe));
            }
        }

        /** Lean's is_valid_ind_app(t, i): {@code I As is} with the declaration's parameters and no occurrence in the indices. */
        private boolean isValidIndApp(Expr t, int i) {
            Expr I = appFn(t);
            Expr[] args = appArgs(t);
            if (!LeanExprKey.exprEquals(I, indConsts[i]) || args.length != nparams + nindices[i]) return false;
            for (int j = 0; j < nparams; j++) if (!LeanExprKey.exprEquals(params.get(j), args[j])) return false;
            // occurrences in the indices are unsound in general (lean4#2125)
            for (int j = nparams; j < args.length; j++) if (hasIndOcc(args[j])) return false;
            return true;
        }

        private int isValidIndApp(Expr t) {
            for (int i = 0; i < indTypes.size(); i++) if (isValidIndApp(t, i)) return i;
            return -1;
        }

        private boolean isIndOcc(Expr e) {
            if (e.tag != Expr.CONST) return false;
            for (Expr c : indConsts) if (c.o0.equals(e.o0)) return true;
            return false;
        }

        private boolean hasIndOcc(Expr t) {
            return find(t, this::isIndOcc);
        }

        /** Lean's is_rec_argument: the index of the type a (function-valued) field returns, or -1. */
        private int isRecArgument(Expr t) {
            t = whnf(t);
            while (t.tag == Expr.FORALL) t = whnf(Reducer.instantiate1((Expr) t.o2, mkLocalDeclFor(t)));
            return isValidIndApp(t);
        }

        /** Lean's check_positivity. */
        private void checkPositivity(Expr t, Name ctor, int argIdx) {
            t = whnf(t);
            if (!hasIndOcc(t)) return;   // nonrecursive argument
            if (t.tag == Expr.FORALL) {
                if (hasIndOcc((Expr) t.o1))
                    throw new RuntimeException("arg #" + (argIdx + 1) + " of '" + ctor + "' has a non positive occurrence of the datatypes being declared");
                checkPositivity(Reducer.instantiate1((Expr) t.o2, mkLocalDeclFor(t)), ctor, argIdx);
            } else if (isValidIndApp(t) < 0) {
                throw new RuntimeException("arg #" + (argIdx + 1) + " of '" + ctor + "' contains a non valid occurrence of the datatypes being declared");
            }
        }

        /** Lean's check_constructors: well-typed, parameters in place, fields in admissible universes, positive, correct result. */
        private void checkConstructors() {
            for (int idx = 0; idx < indTypes.size(); idx++) {
                HashSet<Name> found = new HashSet<>();
                for (InductiveDecl.Constructor c : indTypes.get(idx).constructors) {
                    Name n = c.name;
                    if (!found.add(n)) throw new RuntimeException("duplicate constructor name '" + n + "'");
                    Expr t = c.type;
                    checkName(n);
                    checkNoMVarNoFVar(n, t);
                    tc().check(t);
                    int i = 0;
                    while (t.tag == Expr.FORALL) {
                        if (i < nparams) {
                            if (!isDefEq((Expr) t.o1, paramType(i)))
                                throw new RuntimeException("arg #" + (i + 1) + " of '" + n + "' does not match inductive datatypes parameters'");
                            t = Reducer.instantiate1((Expr) t.o2, params.get(i));
                        } else {
                            Level s = (Level) ensureType((Expr) t.o1).o0;
                            // the sort is ok if it is <= the datatype's level, or the datatype is a predicate
                            if (!(Level.isGeq(resultLevel, s) || Level.normalizesToZero(resultLevel)))
                                throw new RuntimeException("universe level of type_of(arg #" + (i + 1) + ") of '" + n
                                    + "' is too big for the corresponding inductive datatype");
                            if (!isUnsafe) checkPositivity((Expr) t.o1, n, i);
                            t = Reducer.instantiate1((Expr) t.o2, mkLocalDeclFor(t));
                        }
                        i++;
                    }
                    if (!isValidIndApp(t, idx)) throw new RuntimeException("invalid return type for '" + n + "'");
                }
            }
        }

        /** Lean's declare_constructors. */
        private void declareConstructors() {
            for (InductiveDecl.Type t : indTypes) {
                int cidx = 0;
                for (InductiveDecl.Constructor c : t.constructors) {
                    int arity = 0;
                    for (Expr it = c.type; it.tag == Expr.FORALL; it = (Expr) it.o2) arity++;
                    declare(ConstantInfo.mkCtor(c.name, lparams, c.type, t.name, cidx++, nparams, arity - nparams, isUnsafe));
                }
            }
        }

        /** Lean's elim_only_at_universe_zero: the recursor can only eliminate into Prop. */
        private boolean elimOnlyAtUniverseZero() {
            if (isNotZero) return false;                    // never a predicate
            if (indTypes.size() > 1) return true;           // mutual predicates eliminate into Prop
            List<InductiveDecl.Constructor> intros = indTypes.get(0).constructors;
            if (intros.size() > 1) return true;
            if (intros.isEmpty()) return false;             // empty predicates eliminate anywhere
            // one constructor: every non-Prop field must occur in the result (Coq's non-uniform parameter)
            Expr type = intros.get(0).type;
            int i = 0;
            ArrayList<Expr> toCheck = new ArrayList<>();
            while (type.tag == Expr.FORALL) {
                Expr fvar = mkLocalDeclFor(type);
                if (i >= nparams && !Level.normalizesToZero((Level) ensureType((Expr) type.o1).o0)) toCheck.add(fvar);
                type = Reducer.instantiate1((Expr) type.o2, fvar);
                i++;
            }
            List<Expr> resultArgs = Arrays.asList(appArgs(type));
            for (Expr arg : toCheck) {
                boolean occurs = false;
                for (Expr r : resultArgs) if (LeanExprKey.exprEquals(r, arg)) { occurs = true; break; }
                if (!occurs) return true;
            }
            return false;
        }

        /** Lean's init_elim_level. */
        private void initElimLevel() {
            if (elimOnlyAtUniverseZero()) {
                elimLevel = Level.ZERO_LEVEL;
                return;
            }
            Name u = Name.fromString("u");
            for (int i = 1; Arrays.asList(lparams).contains(u); i++) u = Name.fromString("u").appendAfter(i);
            elimLevel = Level.param(u);
        }

        /** Lean's init_K_target: one predicate, one constructor, no fields. */
        private void initKTarget() {
            kTarget = indTypes.size() == 1 && Level.normalizesToZero(resultLevel)
                && indTypes.get(0).constructors.size() == 1;
            if (!kTarget) return;
            int i = 0;
            for (Expr it = indTypes.get(0).constructors.get(0).type; it.tag == Expr.FORALL; it = (Expr) it.o2, i++)
                if (i >= nparams) { kTarget = false; break; }
        }

        /** Lean's get_I_indices: the type index of a valid application, collecting its indices. */
        private int getIIndices(Expr t, List<Expr> indices) {
            int r = isValidIndApp(t);
            if (r < 0) throw new RuntimeException("invalid inductive application in recursor construction: " + t);
            Expr[] args = appArgs(t);
            for (int i = nparams; i < args.length; i++) indices.add(args[i]);
            return r;
        }

        /** The fields b_u of a constructor over the parameters, and those of them that are recursive, u. */
        private Expr ctorFields(InductiveDecl.Constructor c, List<Expr> bu, List<Expr> u) {
            Expr t = c.type;
            int i = 0;
            while (t.tag == Expr.FORALL) {
                if (i < nparams) {
                    t = Reducer.instantiate1((Expr) t.o2, params.get(i));
                } else {
                    Expr l = mkLocalDeclFor(t);
                    bu.add(l);
                    if (u != null && isRecArgument((Expr) t.o1) >= 0) u.add(l);
                    t = Reducer.instantiate1((Expr) t.o2, l);
                }
                i++;
            }
            return t;
        }

        /** A recursive field {@code u_i : xs → I As is}: opens xs as fresh locals and returns I's index, collecting is. */
        private int recArgTarget(Expr ui, List<Expr> xs, List<Expr> indices) {
            Expr t = whnf(inferType(ui));
            while (t.tag == Expr.FORALL) {
                Expr x = mkLocalDeclFor(t);
                xs.add(x);
                t = whnf(Reducer.instantiate1((Expr) t.o2, x));
            }
            return getIIndices(t, indices);
        }

        /** Lean's mk_rec_infos: motives, indices and major premises, then the minor premises. */
        private void mkRecInfos() {
            for (int dIdx = 0; dIdx < indTypes.size(); dIdx++) {
                RecInfo info = new RecInfo();
                Expr t = whnf(indTypes.get(dIdx).type);
                int i = 0;
                while (t.tag == Expr.FORALL) {
                    if (i < nparams) {
                        t = Reducer.instantiate1((Expr) t.o2, params.get(i));
                    } else {
                        Expr idx = mkLocalDeclFor(t);
                        info.indices.add(idx);
                        t = Reducer.instantiate1((Expr) t.o2, idx);
                    }
                    i++;
                    t = whnf(t);
                }
                info.major = mkLocalDecl(Name.fromString("t"), mkApp(mkApp(indConsts[dIdx], params), info.indices));
                Expr motiveType = lctx.mkPi(info.indices, lctx.mkPi(List.of(info.major), Expr.sort(elimLevel, Level.hasParam(elimLevel))));
                Name motiveName = Name.fromString("motive");
                if (indTypes.size() > 1) motiveName = motiveName.appendAfter(dIdx + 1);
                info.motive = mkLocalDecl(motiveName, motiveType);
                recInfos[dIdx] = info;
            }
            for (int dIdx = 0; dIdx < indTypes.size(); dIdx++) {
                InductiveDecl.Type indType = indTypes.get(dIdx);
                for (InductiveDecl.Constructor c : indType.constructors) {
                    ArrayList<Expr> bu = new ArrayList<>(), u = new ArrayList<>(), v = new ArrayList<>();
                    Expr t = ctorFields(c, bu, u);
                    ArrayList<Expr> itIndices = new ArrayList<>();
                    int itIdx = getIIndices(t, itIndices);
                    Expr introApp = mkApp(mkApp(Expr.mkConst(c.name, levels, levels.length > 0), params), bu);
                    Expr cApp = Expr.app(mkApp(recInfos[itIdx].motive, itIndices), introApp);
                    for (Expr ui : u) {
                        ArrayList<Expr> xs = new ArrayList<>(), ihIndices = new ArrayList<>();
                        int ihIdx = recArgTarget(ui, xs, ihIndices);
                        Expr ihApp = Expr.app(mkApp(recInfos[ihIdx].motive, ihIndices), mkApp(ui, xs));
                        v.add(mkLocalDecl(appendAfter(lctx.get(ui).name, "_ih"), lctx.mkPi(xs, ihApp)));
                    }
                    Expr minorType = lctx.mkPi(bu, lctx.mkPi(v, cApp));
                    recInfos[dIdx].minors.add(mkLocalDecl(c.name.replacePrefix(indType.name, Name.ANONYMOUS_NAME), minorType));
                }
            }
        }

        /** Lean's get_rec_levels. */
        private Object[] recLevels() {
            if (elimLevel.tag != Level.PARAM) return levels;
            Object[] out = new Object[levels.length + 1];
            out[0] = elimLevel;
            System.arraycopy(levels, 0, out, 1, levels.length);
            return out;
        }

        /** Lean's get_rec_lparams. */
        private Object[] recLevelParams() {
            if (elimLevel.tag != Level.PARAM) return lparams;
            Object[] out = new Object[lparams.length + 1];
            out[0] = elimLevel.paramName();
            System.arraycopy(lparams, 0, out, 1, lparams.length);
            return out;
        }

        private ArrayList<Expr> motives() {
            ArrayList<Expr> cs = new ArrayList<>();
            for (RecInfo info : recInfos) cs.add(info.motive);
            return cs;
        }

        private ArrayList<Expr> minors() {
            ArrayList<Expr> ms = new ArrayList<>();
            for (RecInfo info : recInfos) ms.addAll(info.minors);
            return ms;
        }

        /** Lean's mk_rec_rules. */
        private ConstantInfo.RecursorRule[] mkRecRules(int dIdx, List<Expr> cs, List<Expr> minors, int[] minorIdx) {
            Object[] recLvls = recLevels();
            List<InductiveDecl.Constructor> ctors = indTypes.get(dIdx).constructors;
            ConstantInfo.RecursorRule[] rules = new ConstantInfo.RecursorRule[ctors.size()];
            for (int k = 0; k < rules.length; k++) {
                InductiveDecl.Constructor c = ctors.get(k);
                ArrayList<Expr> bu = new ArrayList<>(), u = new ArrayList<>(), v = new ArrayList<>();
                ctorFields(c, bu, u);
                for (Expr ui : u) {
                    ArrayList<Expr> xs = new ArrayList<>(), itIndices = new ArrayList<>();
                    int itIdx = recArgTarget(ui, xs, itIndices);
                    Expr recApp = Expr.mkConst(recName(indTypes.get(itIdx).name), recLvls, hasParam(recLvls));
                    recApp = Expr.app(mkApp(mkApp(mkApp(mkApp(recApp, params), cs), minors), itIndices), mkApp(ui, xs));
                    v.add(lctx.mkLambda(xs, recApp));
                }
                Expr eApp = mkApp(mkApp(minors.get(minorIdx[0]), bu), v);
                Expr rhs = lctx.mkLambda(params, lctx.mkLambda(cs, lctx.mkLambda(minors, lctx.mkLambda(bu, eApp))));
                rules[k] = new ConstantInfo.RecursorRule(c.name, bu.size(), rhs);
                minorIdx[0]++;
            }
            return rules;
        }

        /** Lean's declare_recursors. */
        private void declareRecursors() {
            ArrayList<Expr> cs = motives(), minors = minors();
            Object[] all = allNames();
            int[] minorIdx = {0};
            for (int dIdx = 0; dIdx < indTypes.size(); dIdx++) {
                RecInfo info = recInfos[dIdx];
                Expr cApp = Expr.app(mkApp(info.motive, info.indices), info.major);
                Expr recTy = lctx.mkPi(params, lctx.mkPi(cs, lctx.mkPi(minors, lctx.mkPi(info.indices, lctx.mkPi(List.of(info.major), cApp)))));
                recTy = inferImplicit(recTy);
                ConstantInfo.RecursorRule[] rules = mkRecRules(dIdx, cs, minors, minorIdx);
                declare(ConstantInfo.mkRecursor(recName(indTypes.get(dIdx).name), recLevelParams(), recTy, all,
                    nparams, nindices[dIdx], cs.size(), minors.size(), rules, kTarget, isUnsafe));
            }
        }

        /**
         * Lean's check_recursors: each recursor type is well typed and each computation rule
         * preserves types — the recursor applied to a constructor and its reduct have the same type.
         */
        private void checkRecursors() {
            ArrayList<Expr> cs = motives(), minors = minors();
            Object[] recLps = recLevelParams();
            for (int dIdx = 0; dIdx < indTypes.size(); dIdx++) {
                Name rn = recName(indTypes.get(dIdx).name);
                tc(recLps).check(env.lookupOrThrow(rn).type);
                Expr recPre = mkApp(mkApp(mkApp(Expr.mkConst(rn, recLevels(), hasParam(recLevels())), params), cs), minors);
                for (InductiveDecl.Constructor c : indTypes.get(dIdx).constructors) {
                    ArrayList<Expr> bu = new ArrayList<>();
                    Expr t = ctorFields(c, bu, null);
                    ArrayList<Expr> itIndices = new ArrayList<>();
                    getIIndices(t, itIndices);
                    Expr introApp = mkApp(mkApp(Expr.mkConst(c.name, levels, levels.length > 0), params), bu);
                    Expr lhs = Expr.app(mkApp(recPre, itIndices), introApp);
                    TypeChecker tcheck = tc(recLps);
                    Expr expected = tcheck.inferType(lhs);
                    Expr reduct = tcheck.whnfExpr(lhs);
                    Expr actual = tcheck.inferType(reduct);
                    if (!tcheck.isDefEq(actual, expected))
                        throw new RuntimeException("generated recursor computation rule for '" + c.name + "' is not type-preserving");
                }
            }
        }
    }

    /** Lean's check_duplicated_univ_params. */
    static void checkDuplicatedUnivParams(Object[] lps) {
        HashSet<Object> seen = new HashSet<>();
        for (Object p : lps)
            if (!seen.add(p))
                throw new RuntimeException("failed to add declaration to environment, duplicate universe level parameter: '" + p + "'");
    }

    // ========================================================================
    // Expression utilities (Lean's find_fn, replace_fn, app helpers, infer_implicit)
    // ========================================================================

    static Object[] paramLevels(InductiveDecl d) {
        Object[] out = new Object[d.numLevelParams()];
        for (int i = 0; i < out.length; i++) out[i] = Level.param(d.levelParam(i));
        return out;
    }

    private static boolean hasParam(Object[] lvls) {
        for (Object l : lvls) if (Level.hasParam((Level) l)) return true;
        return false;
    }

    static Expr appFn(Expr e) {
        while (e.tag == Expr.APP) e = (Expr) e.o0;
        return e;
    }

    static Expr[] appArgs(Expr e) {
        int n = 0;
        for (Expr c = e; c.tag == Expr.APP; c = (Expr) c.o0) n++;
        Expr[] args = new Expr[n];
        for (Expr c = e; c.tag == Expr.APP; c = (Expr) c.o0) args[--n] = (Expr) c.o1;
        return args;
    }

    static Expr mkApp(Expr f, Expr[] args, int from, int to) {
        for (int i = from; i < to; i++) f = Expr.app(f, args[i]);
        return f;
    }

    static Expr mkApp(Expr f, List<Expr> args) {
        for (Expr a : args) f = Expr.app(f, a);
        return f;
    }

    static long[] fvarIds(List<Expr> fvars) {
        long[] ids = new long[fvars.size()];
        for (int i = 0; i < ids.length; i++) ids[i] = fvars.get(i).longVal;
        return ids;
    }

    /** Lean's {@code name + name}. */
    static Name concat(Name a, Name b) {
        if (b == null || b.isAnonymous()) return a;
        Name prefix = concat(a, b.prefix);
        return b.isStr() ? Name.mkStr(prefix, b.str) : Name.mkNum(prefix, b.num);
    }

    /** Lean's Name.appendAfter (via modifyBase: a hygienic name keeps its macro scopes). */
    static Object appendAfter(Object n, String suffix) {
        return n instanceof Name ? ((Name) n).appendAfter(suffix) : String.valueOf(n) + suffix;
    }

    /** Lean's consumeTypeAnnotations: strip optParam, autoParam, outParam and semiOutParam. */
    static Expr consumeTypeAnnotations(Expr e) {
        while (true) {
            Expr fn = appFn(e);
            if (fn.tag != Expr.CONST) return e;
            int nargs = appArgs(e).length;
            Object c = fn.o0;
            if ((OPT_PARAM.equals(c) || AUTO_PARAM.equals(c)) && nargs == 2) e = (Expr) ((Expr) e.o0).o1;
            else if ((Name.OUT_PARAM.equals(c) || Name.SEMI_OUT_PARAM.equals(c)) && nargs == 1) e = (Expr) e.o1;
            else return e;
        }
    }

    private static boolean isExplicit(Object binderInfo) {
        return binderInfo == null || BINDER_DEFAULT.equals(binderInfo);
    }

    /** Lean's infer_implicit(t, strict = true): a binder occurring in a later explicit domain becomes implicit. */
    static Expr inferImplicit(Expr t) {
        if (t.tag != Expr.FORALL) return t;
        Expr body = inferImplicit((Expr) t.o2);
        Object bi = t.o3;
        if (isExplicit(bi) && hasLooseBVarsInDomain(body, 0)) bi = BINDER_IMPLICIT;
        return Expr.forall(t.o0, (Expr) t.o1, body, bi);
    }

    /** Lean's has_loose_bvars_in_domain(b, vidx, strict = true), with its transitivity through implicit binders. */
    private static boolean hasLooseBVarsInDomain(Expr b, int vidx) {
        while (b.tag == Expr.FORALL) {
            if (hasLooseBVar((Expr) b.o1, vidx)) {
                if (isExplicit(b.o3)) return true;
                if (hasLooseBVarsInDomain((Expr) b.o2, 0)) return true;
            }
            b = (Expr) b.o2;
            vidx++;
        }
        return false;
    }

    /** Lean's has_loose_bvar(e, i): bvar i occurs free in e. */
    static boolean hasLooseBVar(Expr e, int i) {
        if (e.bvarRange() <= i) return false;
        switch (e.tag) {
            case Expr.BVAR: return e.longVal == i;
            case Expr.APP: return hasLooseBVar((Expr) e.o0, i) || hasLooseBVar((Expr) e.o1, i);
            case Expr.LAM: case Expr.FORALL: return hasLooseBVar((Expr) e.o1, i) || hasLooseBVar((Expr) e.o2, i + 1);
            case Expr.LET: return hasLooseBVar((Expr) e.o1, i) || hasLooseBVar((Expr) e.o2, i) || hasLooseBVar((Expr) e.o3, i + 1);
            case Expr.MDATA: case Expr.PROJ: return hasLooseBVar((Expr) e.o1, i);
            default: return false;
        }
    }

    /** Lean's find: does some subterm satisfy p? Shared subterms are visited once. */
    static boolean find(Expr e, Predicate<Expr> p) {
        IdentityHashMap<Expr, Boolean> seen = new IdentityHashMap<>();
        ArrayList<Expr> todo = new ArrayList<>();
        todo.add(e);
        while (!todo.isEmpty()) {
            Expr x = todo.remove(todo.size() - 1);
            if (seen.put(x, Boolean.TRUE) != null) continue;
            if (p.test(x)) return true;
            pushChildren(x, todo);
        }
        return false;
    }

    private static void pushChildren(Expr x, List<Expr> todo) {
        switch (x.tag) {
            case Expr.APP: todo.add((Expr) x.o1); todo.add((Expr) x.o0); break;
            case Expr.LAM: case Expr.FORALL: todo.add((Expr) x.o2); todo.add((Expr) x.o1); break;
            case Expr.LET: todo.add((Expr) x.o3); todo.add((Expr) x.o2); todo.add((Expr) x.o1); break;
            case Expr.MDATA: case Expr.PROJ: todo.add((Expr) x.o1); break;
            default: break;
        }
    }

    interface OffsetVisitor { boolean visit(Expr e, int offset); }

    /** Lean's for_each with binder offsets: the visitor returns false to skip a subterm's children. */
    static void forEachWithOffset(Expr e, OffsetVisitor f) {
        forEachGo(e, 0, f, new IdentityHashMap<>());
    }

    private static void forEachGo(Expr e, int offset, OffsetVisitor f, IdentityHashMap<Expr, HashSet<Integer>> seen) {
        if (!seen.computeIfAbsent(e, k -> new HashSet<>()).add(offset)) return;
        if (!f.visit(e, offset)) return;
        switch (e.tag) {
            case Expr.APP: forEachGo((Expr) e.o0, offset, f, seen); forEachGo((Expr) e.o1, offset, f, seen); break;
            case Expr.LAM: case Expr.FORALL: forEachGo((Expr) e.o1, offset, f, seen); forEachGo((Expr) e.o2, offset + 1, f, seen); break;
            case Expr.LET: forEachGo((Expr) e.o1, offset, f, seen); forEachGo((Expr) e.o2, offset, f, seen); forEachGo((Expr) e.o3, offset + 1, f, seen); break;
            case Expr.MDATA: case Expr.PROJ: forEachGo((Expr) e.o1, offset, f, seen); break;
            default: break;
        }
    }

    /** Lean's replace: f's answer replaces a subterm (not descended into); null descends. Memoized by identity. */
    static Expr replace(Expr e, Function<Expr, Expr> f) {
        return replaceGo(e, f, new IdentityHashMap<>());
    }

    private static Expr replaceGo(Expr e, Function<Expr, Expr> f, IdentityHashMap<Expr, Expr> cache) {
        Expr cached = cache.get(e);
        if (cached != null) return cached;
        Expr r = f.apply(e);
        if (r == null) {
            switch (e.tag) {
                case Expr.APP: {
                    Expr fn = replaceGo((Expr) e.o0, f, cache), arg = replaceGo((Expr) e.o1, f, cache);
                    r = fn == e.o0 && arg == e.o1 ? e : Expr.app(fn, arg);
                    break;
                }
                case Expr.LAM: case Expr.FORALL: {
                    Expr ty = replaceGo((Expr) e.o1, f, cache), body = replaceGo((Expr) e.o2, f, cache);
                    r = ty == e.o1 && body == e.o2 ? e
                        : e.tag == Expr.LAM ? Expr.lam(e.o0, ty, body, e.o3) : Expr.forall(e.o0, ty, body, e.o3);
                    break;
                }
                case Expr.LET: {
                    Expr ty = replaceGo((Expr) e.o1, f, cache), val = replaceGo((Expr) e.o2, f, cache), body = replaceGo((Expr) e.o3, f, cache);
                    r = ty == e.o1 && val == e.o2 && body == e.o3 ? e : Expr.mkLet(e.o0, ty, val, body);
                    break;
                }
                case Expr.MDATA: {
                    Expr inner = replaceGo((Expr) e.o1, f, cache);
                    r = inner == e.o1 ? e : Expr.mdata(e.o0, inner);
                    break;
                }
                case Expr.PROJ: {
                    Expr inner = replaceGo((Expr) e.o1, f, cache);
                    r = inner == e.o1 ? e : Expr.proj(e.o0, e.longVal, inner);
                    break;
                }
                default: r = e;
            }
        }
        cache.put(e, r);
        return r;
    }
}
