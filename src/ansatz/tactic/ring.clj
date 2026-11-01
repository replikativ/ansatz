(ns ansatz.tactic.ring
  "Checked polynomial reflection following Lean's Grind/Arith/CommRing.
   Reification uses Lean.Grind.CommRing.Expr, a shared atom context, and the
   upstream eq_normS / Expr.eq_of_toPoly_eq certificates. The kernel computes
   polynomial equality and checks its connection to the original goal."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.config :as config]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.instance :as inst]
            [ansatz.tactic.proof :as proof])
  (:import [ansatz.kernel TypeChecker]))

(defn- c [n & [us]] (e/const' (name/from-string n) (or us [])))
(defn- app [n us & args] (apply e/app* (c n us) args))
(defn- error! [message data]
  (throw (ex-info (str "ring: " message) (assoc data :kind :tactic-error))))
(defn- syntax [constructor & args]
  (apply e/app* (c (str "Lean.Grind.CommRing.Expr." constructor)) args))
(defn- whnf [st expr] (#'tc/cached-whnf st expr))
(defn- defeq? [st a b] (tc/is-def-eq st a b))

(defn- dec-level? [level]
  ;; Lean.Meta.DecLevel.decAux? without metavariable assignment: a carrier may
  ;; have Sort (max (u+1) (v+1)), not just a syntactic successor universe.
  (cond
    (lvl/succ? level) (lvl/succ-pred level)
    (or (lvl/max? level) (lvl/imax? level))
    (let [imax? (lvl/imax? level)
          a (dec-level? (if imax? (lvl/imax-lhs level) (lvl/max-lhs level)))
          b (dec-level? (if imax? (lvl/imax-rhs level) (lvl/max-rhs level)))]
      (when (and a b) (lvl/level-max a b)))
    :else nil))

(defn- find-instance [st type u class-name]
  (let [target (app class-name [u] type)]
    (or (some (fn [[id decl]]
                (when (defeq? st (:type decl) target) (e/fvar id))) (:lctx st))
        (inst/synthesize* st (:env st) (inst/index-for (:env st)) target 0))))

(defn- ring-context [st type]
  (let [sort (whnf st (tc/infer-type st type))
        level (when (e/sort? sort) (lvl/simplify (e/sort-level sort)))
        u (when level (dec-level? level))
        _ (when-not u
            (error! "expected a ring or semiring carrier in Type" {:type type}))
        type-name (when (e/const? type) (str (e/const-name type)))
        ring (if (= type-name "Int") (c "Lean.Grind.instCommRingInt")
                 (when-not (= type-name "Nat")
                   (find-instance st type u "Lean.Grind.CommRing")))
        comm-semi (when-not ring
                    (if (= type-name "Nat") (c "Lean.Grind.instCommSemiringNat")
                        (find-instance st type u "Lean.Grind.CommSemiring")))
        _ (when-not (or ring comm-semi)
            (error! "no Lean.Grind.CommRing or CommSemiring instance" {:type type}))
        ring-inst (when ring (app "Lean.Grind.CommRing.toRing" [u] type ring))
        semiring (if ring
                   (app "Lean.Grind.Ring.toSemiring" [u] type ring-inst)
                   (app "Lean.Grind.CommSemiring.toSemiring" [u] type comm-semi))
        binary (fn [class-name op-name field]
                 (let [op-inst (app field [u] type semiring)
                       hop-inst (app class-name [u] type op-inst)]
                   (app op-name [u u u] type type type hop-inst)))
        add (binary "instHAdd" "HAdd.hAdd" "Lean.Grind.Semiring.toAdd")
        mul (binary "instHMul" "HMul.hMul" "Lean.Grind.Semiring.toMul")
        pow (app "HPow.hPow" [u lvl/zero u] type (c "Nat") type
                 (app "Lean.Grind.Semiring.npow" [u] type semiring))]
    {:type type :u u :instance (or ring comm-semi) :ring? (some? ring)
     :nat? (= type-name "Nat") :int? (= type-name "Int")
     :semiring semiring :add add :mul mul :pow pow
     :sub (when ring
            (app "HSub.hSub" [u u u] type type type
                 (app "instHSub" [u] type (app "Lean.Grind.Ring.toSub" [u] type ring-inst))))
     :neg (when ring
            (app "Neg.neg" [u] type (app "Lean.Grind.Ring.toNeg" [u] type ring-inst)))}))

(defn- reify-pair [st ctx lhs rhs]
  (let [atoms (atom [])
        memo (java.util.IdentityHashMap.)
        atom! (fn [expr]
                (let [xs @atoms
                      i (or (first (keep-indexed #(when (defeq? st %2 expr) %1) xs))
                            (count xs))]
                  (when (= i (count xs)) (swap! atoms conj expr))
                  (syntax "var" (e/lit-nat i))))
        numeral (fn [n]
                  (if (:ring? ctx)
                    (syntax "num" (app "Int.ofNat" [] (e/lit-nat n)))
                    (syntax "natCast" (e/lit-nat n))))
        ofnat (fn [n]
                (app "OfNat.ofNat" [(:u ctx)] (:type ctx) (e/lit-nat n)
                     (app "Lean.Grind.Semiring.ofNat" [(:u ctx)]
                          (:type ctx) (:semiring ctx) (e/lit-nat n))))]
    (letfn [(go [expr]
                (or (.get memo expr)
                    (let [[head args] (e/get-app-fn-args expr)
                          n (count args)
                          head-name (when (e/const? head) (str (e/const-name head)))
                          prefix (when (<= 2 n) (apply e/app* head (take (- n 2) args)))
                          unary (when (pos? n) (apply e/app* head (butlast args)))
                          literal (cond
                                    (and (:nat? ctx) (e/lit-nat? expr)) (e/lit-nat-val expr)
                                    (and (= head-name "OfNat.ofNat") (= n 3))
                                    (let [k (whnf st (nth args 1))]
                                      (when (and (e/lit-nat? k)
                                                 (defeq? st expr (ofnat (e/lit-nat-val k))))
                                        (e/lit-nat-val k)))
                                    (and (:int? ctx) (= head-name "Int.ofNat") (= n 1))
                                    (let [k (whnf st (first args))]
                                      (when (e/lit-nat? k) (e/lit-nat-val k)))
                                    (and (:nat? ctx) (= head-name "Nat.zero")) 0)
                          result
                          (cond
                            (e/let? expr)
                            (go (e/instantiate1 (e/let-body expr) (e/let-value expr)))
                            (= :mdata (e/tag expr)) (go (e/mdata-expr expr))
                            (some? literal) (numeral literal)
                            (and (:nat? ctx) (= head-name "Nat.succ") (= n 1))
                            (syntax "add" (go (first args)) (numeral 1))
                            (and (:int? ctx) (= head-name "Int.negSucc") (= n 1)
                                 (e/lit-nat? (whnf st (first args))))
                            (syntax "num" (app "Int.negSucc" [] (whnf st (first args))))
                            (and prefix (defeq? st prefix (:add ctx)))
                            (syntax "add" (go (nth args (- n 2))) (go (peek args)))
                            (and prefix (defeq? st prefix (:mul ctx)))
                            (syntax "mul" (go (nth args (- n 2))) (go (peek args)))
                            (and prefix (:sub ctx) (defeq? st prefix (:sub ctx)))
                            (syntax "sub" (go (nth args (- n 2))) (go (peek args)))
                            (and unary (:neg ctx) (defeq? st unary (:neg ctx)))
                            (syntax "neg" (go (peek args)))
                            (and prefix (defeq? st prefix (:pow ctx)))
                            (let [k (whnf st (peek args))]
                              (if (e/lit-nat? k)
                                (syntax "pow" (go (nth args (- n 2))) k)
                                (atom! expr)))
                            :else (atom! expr))]
                      (.put memo expr result)
                      result)))]
      (let [a (go lhs) b (go rhs)]
        {:lhs a :rhs b :atoms @atoms}))))

(defn- context-expr [{:keys [type u semiring]} atoms]
  ;; Lean.Data.RArray.ofFn uses absolute midpoint pivots and balanced branches.
  (let [atoms (if (seq atoms) atoms
                  [(app "OfNat.ofNat" [u] type (e/lit-nat 0)
                        (app "Lean.Grind.Semiring.ofNat" [u] type semiring (e/lit-nat 0)))])]
    (letfn [(build [lo hi]
              (if (= (inc lo) hi)
                (app "Lean.RArray.leaf" [u] type (nth atoms lo))
                (let [mid (quot (+ lo hi) 2)]
                  (app "Lean.RArray.branch" [u] type (e/lit-nat mid)
                       (build lo mid) (build mid hi)))))]
      (build 0 (count atoms)))))

(defn- check-term!
  "Check every application argument, including the boolean certificate. inferType alone
   is not a certificate verifier."
  [env lctx type term]
  (let [checker (doto (TypeChecker. env) (.setFuel (long config/*default-fuel*)))]
    (doseq [[id decl] (sort-by key lctx)]
      (.addLocal checker (long id) (str (:name decl)) (:type decl)))
    (let [inferred (.check checker term)]
      (when-not (.isDefEq checker inferred type)
        (error! "normalization certificate does not prove the original goal"
                {:goal type :inferred inferred})))
    term))

(defn prove-eq
  "A kernel-checked proof term of the equality `type` in local context `lctx`, by Lean's
   CommRing/CommSemiring normalization certificate (what `ring1` provides to linarith).
   Throws a :tactic-error when the two sides do not normalize to the same polynomial."
  [env lctx type]
  (let [st (tc/attach-lctx (tc/mk-tc-state env) lctx)
        [head args] (e/get-app-fn-args (whnf st type))]
    (when-not (and (e/const? head) (= "Eq" (str (e/const-name head))) (= 3 (count args)))
      (error! "goal is not an equality" {:goal type}))
    (let [[ty lhs rhs] args]
      (if (= lhs rhs)
        (check-term! env lctx type (app "Eq.refl" (e/const-levels head) ty lhs))
        (let [_ (when-not (env/lookup env (name/from-string "Lean.Grind.CommRing.eq_normS"))
                  (error! "checked Lean polynomial normalization declarations are unavailable"
                          {:required "Lean.Grind.CommRing.eq_normS"}))
              ctx (ring-context st ty)
              {:keys [lhs rhs atoms]} (reify-pair st ctx lhs rhs)
              context (context-expr ctx atoms)
              cert (app "Eq.refl" [(lvl/succ lvl/zero)] (c "Bool") (c "Bool.true"))
              term (app (if (:ring? ctx) "Lean.Grind.CommRing.Expr.eq_of_toPoly_eq"
                            "Lean.Grind.CommRing.eq_normS")
                        [(:u ctx)] ty (:instance ctx) context lhs rhs cert)]
          (try (check-term! env lctx type term)
               (catch Exception ex
                 (throw (ex-info "ring: polynomial normalization could not certify the equality"
                                 {:kind :tactic-error :goal type} ex)))))))))

(defn ring
  "Prove polynomial equalities with Lean's checked normalization certificates.
   Supports Nat, Int, and carriers with Lean.Grind.CommRing/CommSemiring instances.
   Unsupported operations (including Nat subtraction and nonconstant powers)
   remain atoms. No host polynomial comparison is trusted as a proof.

   Like Mathlib's `ring1` there is no definitional pre-check of the two sides: unfolding
   two different polynomials over large literals recurses once per unit of the literal."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (error! "no goals" {}))
        term (prove-eq (:env ps) (:lctx goal) (:type goal))]
    (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term term})
        (proof/record-tactic :ring [] (:id goal)))))
