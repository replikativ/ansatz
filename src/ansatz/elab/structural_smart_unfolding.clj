(ns ansatz.elab.structural-smart-unfolding
  "Lean 4.33.1 Elab/PreDefinition/Structural/SmartUnfolding.lean (addSmartUnfoldingDef) and the
   smart-unfolding annotations of Meta/WHNF.lean (markSmartUnfoldingMatch/-Alt).

   A structurally recursive `f` gets `f._sunfold`: its predefinition (recursive calls are `f`
   itself), with every matcher whose alternatives make a recursive call on a pattern variable
   marked `sunfoldMatch` and each alternative without a nested marked matcher marked
   `sunfoldMatchAlt`. Meta unfolding (simp's `unfold?`) reduces exactly the marked matchers and
   fails when one is stuck, so `f best (h :: t)` unfolds one step while a `match best` in an
   argument stays as written. Lean records `f` in the smart-unfolding set
   (hasSmartUnfoldingDecl), which keeps it in simp's unfold set beside its equation theorems
   (Simp.unfoldEvenWithEqns)."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.match.matcher-app :as matcher-app]
            [ansatz.meta.match.matcher-info :as mi]))

;; Lean mkAnnotation: an mdata whose KVMap holds the single entry `kind := true`.
(def ^:private match-kind "sunfoldMatch")
(def ^:private alt-kind "sunfoldMatchAlt")

(defn- annotation [kind expr] (e/mdata {kind true} expr))
(defn- annotation? [kind expr]
  (when (and (e/mdata? expr) (= {kind true} (e/mdata-data expr)))
    (e/mdata-expr expr)))

(defn smart-unfolding-match? [expr] (annotation? match-kind expr))
(defn smart-unfolding-match-alt? [expr] (annotation? alt-kind expr))

(defn smart-unfolding-name
  "Lean mkSmartUnfoldingNameFor."
  [decl-name]
  (name/mk-str (if (instance? ansatz.kernel.Name decl-name) decl-name (name/from-string (str decl-name)))
               "_sunfold"))

(defn- find? [pred expr]
  (let [seen (java.util.IdentityHashMap.)]
    (letfn [(go [x]
                (when (nil? (.put seen x true))
                  (or (pred x)
                      (case (e/tag x)
                        :app (or (go (e/app-fn x)) (go (e/app-arg x)))
                        :lam (or (go (e/lam-type x)) (go (e/lam-body x)))
                        :forall (or (go (e/forall-type x)) (go (e/forall-body x)))
                        :let (or (go (e/let-type x)) (go (e/let-value x)) (go (e/let-body x)))
                        :mdata (go (e/mdata-expr x))
                        :proj (go (e/proj-struct x))
                        nil))))]
      (boolean (go expr)))))

(defn contains-smart-unfolding-match?
  "Does `expr` carry a `sunfoldMatch` annotation? An exported or stored declaration can lose
   mdata payloads; its body then has none, and unfolding must not treat it as annotated."
  [expr]
  (find? #(some? (smart-unfolding-match? %)) expr))

(defn- rec-arg-has-loose-bvars-at?
  "Lean Structural/Basic.lean recArgHasLooseBVarsAt."
  [fn-name rec-pos expr]
  (find? (fn [x]
           (let [[head args] (e/get-app-fn-args x)]
             (and (e/const? head) (= fn-name (e/const-name head))
                  (> (count args) rec-pos)
                  (e/has-loose-bvars? (nth args rec-pos)))))
         expr))

(defn annotate
  "Lean addSmartUnfoldingDefAux.visit over the predefinition `value` of `fn-name`."
  [environment fn-name rec-pos value]
  (let [ctx (u/context environment)]
    (letfn [(visit [x]
              (case (e/tag x)
                :lam (let [l (u/local-decl ctx (e/lam-name x) (e/lam-type x) (e/lam-info x))]
                       (u/mk-lambda-fvars ctx [l] (visit (e/instantiate1 (e/lam-body x) l))))
                :forall (let [l (u/local-decl ctx (e/forall-name x) (e/forall-type x) (e/forall-info x))]
                          (u/mk-forall-fvars ctx [l] (visit (e/instantiate1 (e/forall-body x) l))))
                :let (let [value (visit (e/let-value x))
                           l (u/local-decl ctx (e/let-name x) (e/let-type x))
                           body (visit (e/instantiate1 (e/let-body x) l))]
                       (e/let' (e/let-name x) (e/let-type x) value (e/abstract1 body (e/fvar-id l))))
                :mdata (e/mdata (e/mdata-data x) (visit (e/mdata-expr x)))
                :proj (e/proj (e/proj-type-name x) (e/proj-idx x) (visit (e/proj-struct x)))
                :app (let [process-app (fn []
                                         (let [[head args] (e/get-app-fn-args x)]
                                           (u/app (visit head) (mapv visit args))))
                           app (matcher-app/match-matcher-app? environment x)]
                       (if (or (nil? app) (not (rec-arg-has-loose-bvars-at? fn-name rec-pos x)))
                         (process-app)
                         (let [alts (mapv (fn [alt n]
                                            (let [[xs body] (matcher-app/lambda-telescope ctx alt n)
                                                  body (visit body)
                                                  body (if (contains-smart-unfolding-match? body)
                                                         body
                                                         (annotation alt-kind body))]
                                              (u/mk-lambda-fvars ctx xs body)))
                                          (:alternatives app)
                                          (mi/alt-num-params (:matcher-info app)))]
                           (annotation match-kind
                                       (matcher-app/to-expr (assoc app :alternatives alts))))))
                x))]
      (visit value))))

(defn structural-rec-arg-pos
  "Lean Structural.getStructuralRecArgPos? for definitions elaborated here."
  [environment decl-name]
  (get (env/get-extension environment :structural-rec-arg-pos {}) (name/->string decl-name)))

(defn add-smart-unfolding-def
  "Lean addSmartUnfoldingDef: add `fn-name._sunfold` (type `type`, value the annotated
   `predefinition`, in which recursive calls are the constant `fn-name`), tag `fn-name` in the
   smart-unfolding set and record its structural argument position. Returns the new env."
  [environment fn-name level-params type predefinition rec-pos]
  (let [value (annotate environment fn-name rec-pos predefinition)
        aux (env/mk-def (smart-unfolding-name fn-name) level-params type value)]
    (-> (env/check-constant environment aux)
        (env/update-extension :smart-unfolding-defs #{} conj (name/->string fn-name))
        (env/update-extension :structural-rec-arg-pos {} assoc (name/->string fn-name) rec-pos))))
