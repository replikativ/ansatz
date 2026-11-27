(ns ansatz.meta.constructions.cases-on
  "Lean/Meta/Constructions/CasesOn.lean and library/constructions/cases_on.cpp,
   mk_cases_on (55f80e10)."
  (:require [ansatz.meta.constructions.util :as u]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(declare mk-cases-on-from-rec)

(defn- mk-fun-unit [ctx type unit]
  (let [[xs _] (u/forall-telescope ctx type)] (u/mk-lambda-fvars ctx xs unit)))

(defn cases-on-via-projs?
  "Lean 4.36 isCasesOnViaProjs: one constructor, no indices, nonrecursive, Prop-valued and large
   eliminating — every field is then a proof, so the projections of the major exist."
  [env n]
  (let [ind (env/lookup env (name/from-string (str n)))
        rec (env/lookup env (name/from-string (str n ".rec")))]
    (boolean
     (and ind rec (.isInduct ind) (= 1 (count (.ctors ind))) (zero? (.numIndices ind)) (not (.isRec ind))
          (u/prop-former? (u/context env) (.type ind))
          (> (count (.levelParams rec)) (count (.levelParams ind)))))))

(defn- mk-cases-on-via-projs
  "Lean 4.36 mkCasesOnViaProjs?: `fun params motive (t : I params) minor => minor t.1 … t.n`.
   `I.casesOn … t minor` built from `I.rec` reduces only when `t` is a constructor application,
   which a proof may never be; the projections compute on any `t`, and proof irrelevance
   identifies them with the fields of `I.mk x₁ … xₙ`."
  [env n target]
  (let [ind (env/lookup! env (name/from-string (str n)))
        rec (env/lookup! env (name/from-string (str n ".rec")))
        ctor (env/lookup! env (first (.ctors ind)))
        ctx (u/context env)
        np (.numParams ind)
        [xs major-type] (u/forall-telescope ctx (.type rec) (+ np 2))
        params (subvec xs 0 np) motive (nth xs np) minor (nth xs (inc np))
        major (u/local-decl ctx (e/forall-name major-type) (e/forall-type major-type) (e/forall-info major-type))
        fields (map #(e/proj (.name ind) % major) (range (.numFields ctor)))
        ys (vec (concat params [motive major minor]))]
    (u/add-definition env ctx target (vec (.levelParams rec)) ys (e/app motive major) (u/app minor fields))))

(defn mk-cases-on
  ([env n] (mk-cases-on env n (str n ".casesOn")))
  ([env n target]
   (if (cases-on-via-projs? env n)
     (mk-cases-on-via-projs env n target)
     (mk-cases-on-from-rec env n target))))

(defn- mk-cases-on-from-rec
  ([env n target]
   (let [ind (env/lookup! env (name/from-string (str n)))
         rec (env/lookup! env (name/from-string (str n ".rec")))
         ctx (u/context env)
         [xs body] (u/forall-telescope ctx (.type rec))
         np (.numParams rec) nm (.numMotives rec) nn (.numMinors rec)
         params (subvec xs 0 np) motives (subvec xs np (+ np nm))
         minors (subvec xs (+ np nm) (+ np nm nn))
         ism (subvec xs (+ np nm nn))
         all (vec (.all rec))
         main (.indexOf all (name/from-string (str n)))
         motive (nth motives main)
         ls (mapv lvl/param (.levelParams rec))
         elim (if (= (count ls) (count (.levelParams ind))) lvl/zero (first ls))
         ;; library/util.cpp mk_unit/mk_unit_mk use PUnit even at level zero.
         unit (u/const' "PUnit" [elim])
         star (u/const' "PUnit.unit" [elim])
         motive-args (mapv #(if (= % motive) % (mk-fun-unit ctx (u/infer-type ctx %) unit)) motives)
         minor-main (vec (mapcat (fn [j]
                                   (repeat (count (.ctors (env/lookup! env (nth all j)))) (= j main)))
                                 (range (count all))))
         processed
         (mapv (fn [i minor]
                 (let [[args t] (u/forall-telescope ctx (u/infer-type ctx minor))
                       is-main (get minor-main i false)
                       info (u/decl ctx minor)
                       classified (mapv (fn [arg]
                                          (let [[ys t] (u/forall-telescope ctx (u/infer-type ctx arg))
                                                h (e/get-app-fn t)
                                                ih? (some #{h} motives)]
                                            {:arg arg :ih? ih?
                                             :param (if (and ih? (not= h motive))
                                                      (u/local-decl ctx (:name (u/decl ctx arg))
                                                                    (u/mk-forall-fvars ctx ys unit)
                                                                    (:info (u/decl ctx arg))) arg)})) args)
                       non-rec (mapv :arg (remove :ih? classified))
                       new-c (when is-main
                               (u/local-decl ctx (:name info) (u/mk-forall-fvars ctx non-rec t) (:info info)))
                       val (if is-main (u/app new-c non-rec) star)]
                   [new-c (u/mk-lambda-fvars ctx (mapv :param classified) val)]))
               (range nn) minors)
         vs (vec (concat params [motive] ism (keep first processed)))
         val (u/app (u/const' (.name rec) ls)
                    (concat params motive-args (map second processed) ism))]
     (u/add-definition env ctx target (vec (.levelParams rec)) vs body val))))
