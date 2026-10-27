(ns ansatz.meta.constructions.util
  "Telescope and declaration operations used by Lean/Meta/Constructions.
   Follows Lean Meta.Basic and library/constructions (55f80e10)."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]))

(defn const' [n ls] (e/const' (name/from-string (str n)) ls))
(defn app [f xs] (reduce e/app f xs))
(defn context [env] (atom (tc/mk-tc-state env)))
(defn set-env! [ctx env]
  ;; A cached Java checker belongs to its original Env as well as its locals.
  (reset! ctx (assoc (tc/mk-tc-state-with-locals env (:lctx @ctx)) :next-id (:next-id @ctx))))
(defn infer-type [ctx x] (tc/infer-type @ctx x))
(defn whnf [ctx x] (red/whnf (:env @ctx) x (:lctx @ctx)))
(defn get-level [ctx t] (e/sort-level (tc/ensure-sort @ctx (infer-type ctx t))))
(defn local-decl
  ([ctx n t] (local-decl ctx n t :default))
  ([ctx n t info]
   (let [id (swap! (:next-id @ctx) inc)]
     (swap! ctx update :lctx assoc id {:tag :local :id id :name n :type t :info info})
     (e/fvar id))))
(defn decl [ctx x] (get (:lctx @ctx) (e/fvar-id x)))
(defn forall-telescope
  ([ctx t] (forall-telescope ctx t nil))
  ([ctx t n]
   (loop [t t xs []]
     (let [t (whnf ctx t)]
       (if (and (e/forall? t) (or (nil? n) (< (count xs) n)))
         (let [x (local-decl ctx (e/forall-name t) (e/forall-type t) (e/forall-info t))]
           (recur (e/instantiate1 (e/forall-body t) x) (conj xs x)))
         [xs t])))))
(defn bind-fvars [ctx binder xs body]
  (reduce (fn [b x]
            (let [{:keys [name type info]} (decl ctx x)]
              (binder name type (e/abstract1 b (e/fvar-id x)) (or info :default))))
          body (reverse xs)))
(defn mk-lambda-fvars [ctx xs body] (bind-fvars ctx e/lam xs body))
(defn mk-forall-fvars [ctx xs body] (bind-fvars ctx e/forall' xs body))
(defn implicit! [ctx xs]
  (doseq [x xs] (swap! ctx assoc-in [:lctx (e/fvar-id x) :info] :implicit)))
(defn instantiate-forall [ctx t xs]
  (reduce (fn [t x] (e/instantiate1 (e/forall-body (whnf ctx t)) x)) t xs))
(defn beta [f xs]
  (reduce (fn [f x] (if (e/lam? f) (e/instantiate1 (e/lam-body f) x) (e/app f x))) f xs))
(defn fold-constants [f init x]
  (loop [pending [x] seen #{} acc init]
    (if-let [x (peek pending)]
      (if (contains? seen x) (recur (pop pending) seen acc)
          (let [pending (pop pending) seen (conj seen x)]
            (case (e/tag x)
              :const (recur pending seen (f acc (e/const-name x)))
              :app (recur (conj pending (e/app-fn x) (e/app-arg x)) seen acc)
              :lam (recur (conj pending (e/lam-type x) (e/lam-body x)) seen acc)
              :forall (recur (conj pending (e/forall-type x) (e/forall-body x)) seen acc)
              :let (recur (conj pending (e/let-type x) (e/let-value x) (e/let-body x)) seen acc)
              :proj (recur (conj pending (e/proj-struct x)) seen acc)
              :mdata (recur (conj pending (e/mdata-expr x)) seen acc)
              (recur pending seen acc)))) acc)))

(defn has-unsafe? [env x]
  (fold-constants (fn [found n]
                    (let [ci (env/lookup! env n)]
                      (or found (.isUnsafe ci) (and (.isDef ci) (pos? (.safety ci)))))) false x))

(defn mk-definition-val-inferring-unsafe [env n lps type value hints]
  ;; Lean/Environment.lean mkDefinitionValInferringUnsafe.
  (env/mk-def (name/from-string (str n)) lps type value :hints hints
              :safety (if (or (has-unsafe? env type) (has-unsafe? env value)) :unsafe :safe)))

(defn mk-thm-or-unsafe-def [env n lps type value]
  ;; Lean/Environment.lean mkThmOrUnsafeDef.
  (if (or (has-unsafe? env type) (has-unsafe? env value))
    (mk-definition-val-inferring-unsafe env n lps type value :opaque)
    (env/mk-thm (name/from-string (str n)) lps type value)))

(defn get-max-height [env x]
  (fold-constants (fn [h n]
                    (let [ci (env/lookup! env n)]
                      (if (and (.isDef ci) (>= (.getHintsCode ci) 0))
                        (max h (.getHintsCode ci)) h))) 0 x))

(defn mk-definition [ctx n lps xs t val]
  (let [val (mk-lambda-fvars ctx xs val)
        type (if t (mk-forall-fvars ctx xs t) (infer-type ctx val))]
    (mk-definition-val-inferring-unsafe (:env @ctx) n lps type val :abbrev)))
(defn add-definition [env ctx n lps xs t val]
  (when-not (identical? env (:env @ctx)) (set-env! ctx env))
  (env/check-constant env (mk-definition ctx n lps xs t val)))
(defn prop-former? [ctx t]
  (let [[_ b] (forall-telescope ctx t)]
    (and (e/sort? b) (lvl/level-zero? (e/sort-level b)))))
(defn is-enum-type? [env info]
  ;; Lean/MonadEnv.lean isEnumType; empty and unsafe types use the core construction.
  (and (zero? (.numParams info)) (zero? (.numIndices info))
       (= 1 (count (.all info))) (zero? (.numNested info))
       (not (.isRec info)) (not (.isUnsafe info)) (seq (.ctors info))
       (not (prop-former? (context env) (.type info)))
       (every? #(zero? (.numFields (env/lookup! env %))) (.ctors info))))

(defn mk-eq [ctx x y]
  (let [t (infer-type ctx x)] (app (const' "Eq" [(get-level ctx t)]) [t x y])))
(defn mk-eq-refl [ctx x]
  (let [t (infer-type ctx x)] (app (const' "Eq.refl" [(get-level ctx t)]) [t x])))
(defn mk-eq-heq [ctx x y]
  (let [tx (infer-type ctx x) ty (infer-type ctx y)]
    (if (tc/is-def-eq @ctx tx ty)
      (mk-eq ctx x y)
      (app (const' "HEq" [(get-level ctx tx)]) [tx x ty y]))))
(defn mk-arrow [ctx a b]
  (mk-forall-fvars ctx [(local-decl ctx "_" a)] b))

(defn replace-fvars [x subst]
  (reduce (fn [x [old new]] (e/instantiate1 (e/abstract1 x (e/fvar-id old)) new)) x subst))
(defn mk-eq-ndrec [ctx a x motive base y eq]
  (let [result (beta motive [y])]
    (app (const' "Eq.ndrec" [(get-level ctx result) (get-level ctx a)])
         [a x motive base y eq])))
