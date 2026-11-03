;; Lean 4 v4.33.1 (55f80e10a3): Elab/Inductive.lean elabCtors;
;; Elab/MutualInductive.lean elabHeaders, withInductiveLocalDecls, elabInductiveViews.
(ns ansatz.elab.inductive
  "Surface inductive headers and constructors, elaborated before kernel construction."
  (:require [clojure.walk :as walk]
            [ansatz.kernel.expr :as e]
            [ansatz.surface.elaborate :as term]))

(defn- surface-form [form]
  ;; Preserve the older inductive spelling of arrows and Nat `le`, and its
  ;; string-valued programmatic type input. All terms use the common elaborator.
  (walk/postwalk
    (fn [x]
      (if (seq? x)
        (cond
          (and (= 'Type (first x)) (= 2 (count x)))
          (symbol (str "Type.{" (second x) "}"))
          (= '-> (first x)) (cons '=> (rest x))
          (and (= 'le (first x)) (= 3 (count x))) (cons '<= (rest x))
          (= '(nil) x) nil
          :else x)
        x))
    (if (string? form) (read-string form) form)))

(defn- telescope [type syms]
  (loop [type type syms syms acc []]
    (if (empty? syms)
      [acc type]
      (recur (e/forall-body type) (rest syms)
             (conj acc {:name (str (first syms)) :sym (first syms)
                        :compiled-type (e/forall-type type)})))))

(defn elab-headers [environment param-pairs index-pairs result-level]
  (let [pairs (into param-pairs index-pairs)
        form (list 'forall (vec (mapcat (fn [[s t]] [s (surface-form t)]) pairs))
                   (e/sort' result-level))
        type (term/elaborate-in-context environment {} form nil {:type-position true})
        [params rest-type] (telescope type (map first param-pairs))
        [indices _] (telescope rest-type (map first index-pairs))
        ;; Constructor parameter occurrences are implicit, as in Lean's
        ;; withExplicitToImplicit. The family local retains the entire header.
        header (reduce (fn [body p]
                         (e/forall' (:name p) (:compiled-type p) body :implicit))
                       rest-type (reverse params))]
    {:params params :indices indices :type header}))

(defn- open-params [type params]
  (loop [type type ps params lctx {} ids []]
    (if (empty? ps)
      {:lctx lctx :ids ids}
      (let [id (inc (count ids)) p (first ps)]
        (recur (e/instantiate1 (e/forall-body type) (e/fvar id)) (rest ps)
               (assoc lctx id {:name (:name p) :type (e/forall-type type) :tag :local})
               (conj ids id))))))

(defn- check-param-occs
  "Lean elabCtors.checkParamOccs: unify and canonicalize every recursive parameter."
  [est expr family-fvar params]
  (letfn [(visit [expr]
            (let [[head args] (e/get-app-fn-args expr)]
              (if (= head family-fvar)
                (do
                  (doseq [[param arg] (map vector params args)]
                    (when-not (term/unify-subterms! est param arg)
                      (throw (ex-info "Mismatched inductive type parameter"
                                      {:parameter param :argument arg}))))
                  (when (< (count args) (count params))
                    (throw (ex-info "Missing inductive type parameter" {:expression expr})))
                  (reduce e/app head (concat params (drop (count params) args))))
                (case (e/tag expr)
                  :app (e/app (visit (e/app-fn expr)) (visit (e/app-arg expr)))
                  :forall (e/forall' (e/forall-name expr) (visit (e/forall-type expr))
                                    (visit (e/forall-body expr)) (e/forall-info expr))
                  :lam (e/lam (e/lam-name expr) (visit (e/lam-type expr))
                              (visit (e/lam-body expr)) (e/lam-info expr))
                  :let (e/let' (e/let-name expr) (visit (e/let-type expr))
                               (visit (e/let-value expr)) (visit (e/let-body expr)))
                  :mdata (e/mdata (e/mdata-data expr) (visit (e/mdata-expr expr)))
                  :proj (e/proj (e/proj-type-name expr) (e/proj-idx expr)
                                (visit (e/proj-struct expr)))
                  expr))))]
    (visit expr)))

(defn elab-ctors [environment family header ctors-spec self-const]
  (let [{:keys [params type]} header
        {:keys [lctx ids]} (open-params type params)
        family-id (inc (count ids))
        lctx (assoc lctx family-id {:name family :type type :tag :local})
        n-indices (count (:indices header))]
    (mapv
      (fn [i [cname fields-spec return-indices]]
        (when-not (= n-indices (count return-indices))
          (throw (ex-info "Constructor result must supply every family index"
                          {:constructor cname :expected n-indices :indices return-indices})))
        (let [field-pairs (vec (partition 2 fields-spec))
              ;; Default results refer to the original locals even when a field
              ;; shadows a header name (Lean uses mkAppN indFVar params).
              result (apply list (e/fvar family-id)
                            (concat (map e/fvar ids) (map surface-form return-indices)))
              form (list 'forall
                         (vec (mapcat (fn [[s t]] [s (surface-form t)]) field-pairs)) result)
              ;; One elaboration shares metavariables across the whole telescope;
              ;; strict finalization synthesizes instances and instantiates holes.
              type (term/elaborate-in-context
                     environment lctx form nil
                     {:type-position true
                      :post-elab #(check-param-occs %1 %2 (e/fvar family-id) (mapv e/fvar ids))})
              type (e/instantiate1 (e/abstract1 type family-id) self-const)
              type (e/abstract-many type ids)
              [fields result] (telescope type (map first field-pairs))
              [head args] (e/get-app-fn-args result)
              n-fields (count fields)]
          (when-not (and (= head self-const)
                         (= (count args) (+ (count params) n-indices))
                         (= (take (count params) args)
                            (map #(e/bvar (+ n-fields (- (count params) % 1)))
                                 (range (count params)))))
            (throw (ex-info "Invalid constructor result or parameter occurrence" {:constructor cname})))
          {:name (if (nil? cname) "nil" (str cname)) :sym cname :idx i
           :full-name (str family "." (if (nil? cname) "nil" cname))
           :fields (mapv #(-> % (assoc :type (:compiled-type %)) (dissoc :compiled-type)) fields)
           :compiled-return-indices (vec (drop (count params) args))}))
      (range) ctors-spec)))

(defn elab-inductive [environment family param-pairs index-pairs ctors-spec result-level self-const]
  (let [header (elab-headers environment param-pairs index-pairs result-level)]
    (assoc header :ctors (elab-ctors environment family header ctors-spec self-const))))
