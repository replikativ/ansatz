(ns ansatz.malli
  "The gradual dependently-typed surface for Clojurians: malli schemas as a/defn signatures.

   This namespace loads ONLY when metosin/malli is on the classpath (ansatz core does not
   depend on it; the a/defn macro probes for it via requiring-resolve — the optionality seam).

   The porting story is a one-token diff. Given ordinary instrumented Clojure:

     (defn add2 [x y] (+ x y))
     (m/=> add2 [:=> [:cat :int :int] :int])

   change `defn` to `a/defn` and the SAME schema becomes the kernel signature:

     (a/defn add2 [x y] (+ x y))     ;; params/ret read from the m/=> registry,
                                     ;; body kernel-verified, runtime compiled

   Design: schemas translate to SURFACE TYPE FORMS ('Nat, '(List Nat)) — not kernel
   exprs — so the single elaborator (elab-signature) does everything downstream.
   Refinement bounds ([:int {:min 1}] → Subtype hypotheses for termination) and
   [:map] → record structures are the next slices; unsupported schema shapes throw
   honestly rather than lifting approximately."
  (:require [malli.core :as m]))

(defn schema-form->type-form
  "Translate one malli schema FORM (vector data / keyword) to an ansatz surface type form.
   Throws (honest, with the offending form) on shapes not yet supported."
  [f]
  (let [f (if (m/schema? f) (m/form f) f)]
    (cond
      ;; scalars — v1 maps malli ints to Nat (the embedding's arithmetic default; negative
      ;; ints are caught by malli's own runtime conformance until Int lands here)
      (contains? #{:int 'int? 'integer? :nat-int 'nat-int? 'pos-int? :double} f)
      (if (= f :double)
        (throw (ex-info "ansatz.malli: :double not yet supported (Float pending)" {:form f}))
        'Nat)
      (contains? #{:boolean 'boolean?} f) 'Bool
      (contains? #{:string 'string?} f) 'String
      (keyword? f) (throw (ex-info (str "ansatz.malli: unsupported scalar schema " f) {:form f}))
      (symbol? f) (throw (ex-info (str "ansatz.malli: unsupported predicate schema " f) {:form f}))

      (vector? f)
      (let [[h & args] f
            ;; strip an optional props map
            [props args] (if (map? (first args)) [(first args) (rest args)] [nil args])]
        (case h
          (:sequential :vector :set) (list 'List (schema-form->type-form (first args)))
          :maybe (list 'Option (schema-form->type-form (first args)))
          :int (if (or (nil? props) (= props {:min 0}))
                 'Nat
                 (throw (ex-info "ansatz.malli: refinement bounds land with Subtype support"
                                 {:form f :props props})))
          :map (throw (ex-info "ansatz.malli: [:map …] → record structures land next" {:form f}))
          (throw (ex-info (str "ansatz.malli: unsupported schema " h) {:form f}))))

      :else (throw (ex-info "ansatz.malli: unsupported schema form" {:form f})))))

(defn fn-schema->signature
  "[:=> [:cat A B …] R] → {:param-types [formA formB …] :ret-type formR}."
  [schema]
  (let [f (if (m/schema? schema) (m/form schema) schema)]
    (when (and (vector? f) (= :=> (first f)) (vector? (second f)) (= :cat (first (second f))))
      {:param-types (mapv schema-form->type-form (rest (second f)))
       :ret-type (schema-form->type-form (nth f 2))})))

(defn signature-for
  "Look up the malli function schema for `fn-name` in `ns-sym` (the m/=> registry, then
   :malli/schema metadata on the name symbol) and translate it. Returns
   {:param-types […] :ret-type …} or nil; nil means 'no schema registered' (the caller
   falls through), a THROW means 'schema present but untranslatable' (honest error)."
  [ns-sym fn-name arity]
  (let [from-meta (:malli/schema (meta fn-name))
        from-reg (get-in (m/function-schemas) [ns-sym (symbol (name fn-name)) :schema])
        schema (or from-meta from-reg)]
    (when schema
      (let [sig (fn-schema->signature schema)]
        (when-not sig
          (throw (ex-info "ansatz.malli: only [:=> [:cat …] ret] function schemas are supported"
                          {:fn fn-name :schema (if (m/schema? schema) (m/form schema) schema)})))
        (when (not= arity (count (:param-types sig)))
          (throw (ex-info "ansatz.malli: schema arity does not match the parameter vector"
                          {:fn fn-name :schema-arity (count (:param-types sig)) :arity arity})))
        sig))))
