;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; CIC kernel for Clojure — Environment and Declaration types.
;; Thin wrapper over Java ConstantInfo and Env classes.

(ns cic.kernel.env
  "The kernel environment: a mutable HashMap from Name to ConstantInfo.
   Uses Java classes for fast lookup and compact storage.

   ConstantInfo variants:
     :axiom, :def, :thm, :opaque, :quot, :induct, :ctor, :recursor"
  (:import [cic.kernel ConstantInfo ConstantInfo$RecursorRule Env Name]))

;; ============================================================
;; Tag keyword mapping
;; ============================================================

(def ^:private tag-kws
  [:axiom :def :thm :opaque :quot :induct :ctor :recursor])

(defn ci-tag [^ConstantInfo ci] (nth tag-kws (.tag ci)))

;; ============================================================
;; Declaration constructors
;; ============================================================

(defn mk-axiom [name level-params type & {:keys [unsafe?] :or {unsafe? false}}]
  (ConstantInfo/mkAxiom name (into-array Object level-params) type (boolean unsafe?)))

(defn mk-def [name level-params type value & {:keys [hints safety all]
                                               :or {hints :opaque safety :safe all nil}}]
  (let [h (cond
            (= hints :opaque) ConstantInfo/HINTS_OPAQUE
            (= hints :abbrev) ConstantInfo/HINTS_ABBREV
            (map? hints) (:regular hints)
            :else ConstantInfo/HINTS_OPAQUE)
        s (case safety :safe (byte 0) :unsafe (byte 1) :partial (byte 2) (byte 0))]
    (ConstantInfo/mkDef name (into-array Object level-params) type value
                        (int h) s (into-array Object (or all [name])))))

(defn mk-thm [name level-params type value & {:keys [all]}]
  (ConstantInfo/mkThm name (into-array Object level-params) type value
                      (into-array Object (or all [name]))))

(defn mk-opaque [name level-params type value & {:keys [all unsafe?] :or {unsafe? false}}]
  (ConstantInfo/mkOpaque name (into-array Object level-params) type value
                         (into-array Object (or all [name])) (boolean unsafe?)))

(defn mk-quot [name level-params type kind]
  (ConstantInfo/mkQuot name (into-array Object level-params) type kind))

(defn mk-induct [name level-params type & {:keys [num-params num-indices all ctors
                                                    num-nested rec? reflexive? unsafe?]
                                             :or {num-params 0 num-indices 0 num-nested 0
                                                  rec? false reflexive? false unsafe? false}}]
  (ConstantInfo/mkInduct name (into-array Object level-params) type
                         (int num-params) (int num-indices)
                         (into-array Object (or all [name]))
                         (into-array Name (or ctors []))
                         (int num-nested)
                         (boolean rec?) (boolean reflexive?) (boolean unsafe?)))

(defn mk-ctor [name level-params type induct cidx num-params num-fields & {:keys [unsafe?] :or {unsafe? false}}]
  (ConstantInfo/mkCtor name (into-array Object level-params) type
                       induct (int cidx) (int num-params) (int num-fields) (boolean unsafe?)))

(defn mk-recursor [name level-params type & {:keys [all num-params num-indices num-motives
                                                     num-minors rules k? unsafe?]
                                               :or {num-params 0 num-indices 0 num-motives 1
                                                    num-minors 0 rules [] k? false unsafe? false}}]
  (ConstantInfo/mkRecursor name (into-array Object level-params) type
                           (into-array Object (or all [name]))
                           (int num-params) (int num-indices)
                           (int num-motives) (int num-minors)
                           (into-array ConstantInfo$RecursorRule rules)
                           (boolean k?) (boolean unsafe?)))

(defn mk-recursor-rule [ctor nfields rhs]
  (ConstantInfo$RecursorRule. ctor (int nfields) rhs))

;; ============================================================
;; Environment
;; ============================================================

(defn empty-env
  "Create an empty kernel environment."
  []
  (Env.))

(defn add-constant
  "Add a constant to the environment. Throws if already present."
  [^Env env ^ConstantInfo ci]
  (.addConstant env ci)
  env)

(defn lookup
  "Look up a constant by name. Returns nil if not found."
  [^Env env name]
  (.lookup env name))

(defn lookup!
  "Look up a constant by name. Throws if not found."
  [^Env env name]
  (.lookupOrThrow env name))

;; --- ConstantInfo accessors ---

(defn ci-name ^Name [^ConstantInfo ci] (.name ci))
(defn ci-type [^ConstantInfo ci] (.type ci))
(defn ci-level-params [^ConstantInfo ci] (vec (.levelParams ci)))
(defn ci-value [^ConstantInfo ci] (.value ci))

(defn get-value
  "Get the definition value of a constant (for delta reduction).
   Returns nil for axioms, inductives, constructors, and opaques/thms."
  [^ConstantInfo ci]
  (.getValue ci))

(defn get-reducibility-hints
  "Get reducibility hints for delta reduction ordering."
  [^ConstantInfo ci]
  (case (.tag ci)
    1 (let [h (.hints ci)]  ;; DEF
        (cond
          (= h ConstantInfo/HINTS_OPAQUE) :opaque
          (= h ConstantInfo/HINTS_ABBREV) :abbrev
          :else {:regular h}))
    2 :opaque  ;; THM
    3 :opaque  ;; OPAQUE
    nil))

(defn def? [^ConstantInfo ci] (.isDef ci))
(defn thm? [^ConstantInfo ci] (.isThm ci))
(defn axiom? [^ConstantInfo ci] (.isAxiom ci))
(defn induct? [^ConstantInfo ci] (.isInduct ci))
(defn ctor? [^ConstantInfo ci] (.isCtor ci))
(defn recursor? [^ConstantInfo ci] (.isRecursor ci))
(defn quot? [^ConstantInfo ci] (.isQuot ci))

(defn enable-quot
  "Enable quotient type support in the environment."
  [^Env env]
  (.enableQuot env)
  env)

(defn quot-enabled? [^Env env]
  (.isQuotEnabled env))
