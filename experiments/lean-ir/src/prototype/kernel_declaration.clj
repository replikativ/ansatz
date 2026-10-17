(ns prototype.kernel-declaration
  "Closed source Declaration checking projections. Original guest roots survive
   unchanged; no publication, async frontend update or executable installation.
   Expression metadata erasure/normalization is inherited from kernel-bridge.
   Inductive/quotient source projections are descriptive, NOT admissions: their
   generated ConstantInfo families still require complete kernel generation."
  (:require [prototype.machine :as m] [prototype.native-scalar :as native]
            [prototype.scalar :as scalar] [prototype.kernel-bridge :as bridge]
            [prototype.imported-kernel :as imported])
  (:import [ansatz.kernel ConstantInfo Env TypeChecker RawInductiveGenerator RawInductiveGenerator$Source
             RawInductiveGenerator$Type RawInductiveGenerator$Constructor RawNestedInductiveGenerator Name Level]))

(defn- fail [message data] (throw (ex-info message data)))
(defn- tag [value]
  (cond (native/native-scalar? value) (native/payload value)
        (instance? prototype.machine.Tag value) (:tag value)
        (integer? value) value))
(defn- ctor! [world value expected fields bytes]
  (when-not (m/ref? value) (fail "Expected source declaration constructor" {:value value}))
  (let [node (m/node world value)]
    (when-not (and (= expected (:tag node)) (bridge/constructor-layout? node fields bytes))
      (fail "Invalid source declaration constructor layout" {:value value :expected [expected fields bytes]})) node))
(defn- list-values [world value]
  (loop [value value seen #{} out []]
    (if (= 0 (tag value)) out
      (do (when (contains? seen value) (fail "Cyclic source declaration list" {}))
          (let [[head tail] (:fields (ctor! world value 1 2 0))]
            (recur tail (conj seen value) (conj out head)))))))
(defn- definition [world value]
  ;; A throwaway persistent projection view supplies ConstantInfo.defnInfo's
  ;; wrapper around the exact original DefinitionVal. No guest owner is consumed
  ;; and this temporary world is never returned, cached or published.
  (let [[view wrapper] (m/allocate world :ctor 1 [value])]
    (imported/project-constant view wrapper)))
(defn- names [world value]
  (vec (:value (bridge/project-with-stats world :names value))))

(defn- canonical-level! [world value]
  (loop [todo [[value (bridge/project-level world value)]]]
    (when (seq todo)
      (let [[raw ^Level projected] (peek todo) todo (pop todo)
            kind (if (m/ref? raw) (:tag (m/node world raw)) (tag raw))]
        (when-not (= kind (.tag projected))
          (fail "Source inductive noncanonical universe provenance is not implemented"
                {:runtime-limit :source-inductive-provenance}))
        (let [children (case kind
                         0 []
                         1 [[(first (:fields (ctor! world raw 1 1 8))) (.o0 projected)]]
                         (2 3) (let [[a b] (:fields (ctor! world raw kind 2 8))]
                                 [[a (.o0 projected)] [b (.o1 projected)]])
                         4 (let [[name] (:fields (ctor! world raw 4 1 8))]
                             (when-not (= (bridge/project-name world name) (.o0 projected))
                               (fail "Source inductive reordered universe provenance is not implemented"
                                     {:runtime-limit :source-inductive-provenance})) [])
                         (fail "Unresolved source inductive universe variable" {}))]
          (recur (into todo children)))))))

(defn- raw-inductive-preflight! [world declaration]
  (let [[parameters num-params types] (:fields (ctor! world declaration 6 3 1))
        parameters (names world parameters)
        np (native/nat-value {:ref? m/ref? :node m/node} world num-params)
        _ (when (> np Integer/MAX_VALUE) (fail "Source inductive parameter count exceeds Java range" {}))
        types (list-values world types)
        family (set (map #(bridge/project-name world (first (:fields (ctor! world % 0 3 0)))) types))
        roots (mapcat (fn [type]
                        (let [[_ expression constructors] (:fields (ctor! world type 0 3 0))]
                          (cons [expression false]
                            (map #(vector (second (:fields (ctor! world % 0 2 0))) true)
                                 (list-values world constructors))))) types)
        app (fn [value]
              (loop [head value arguments []]
                (let [node (m/node world head)]
                  (if (= 5 (:tag node))
                    (let [[f x] (:fields (ctor! world head 5 2 8))]
                      (recur f (conj arguments x)))
                    [head (vec (reverse arguments))]))))]
    ;; Do this BEFORE the lossy checking projection: native checks the raw
    ;; universe PARAM constructors, not normalized max/imax equivalents.
    (doseq [[root uniform?] roots]
      (loop [todo [[root 0]] seen #{}]
        (when (seq todo)
          (let [[value depth :as key] (peek todo) todo (pop todo)]
            (if (contains? seen key) (recur todo seen)
              (let [node (m/node world value) kind (:tag node)
                    _ (when (contains? #{8 10} kind)
                        (fail "Source inductive let/metadata provenance is not implemented"
                              {:runtime-limit :source-inductive-provenance}))
                    _ (when (contains? #{1 2} kind) (fail "Unresolved source inductive expression variable" {}))
                    [head arguments] (app value)
                    head-node (m/node world head)
                    const? (= 4 (:tag head-node))
                    [name levels] (when const? (:fields (ctor! world head 4 2 8)))
                    _ (case kind
                        3 (canonical-level! world (first (:fields (ctor! world value 3 1 8))))
                        4 (doseq [level (list-values world levels)] (canonical-level! world level))
                        nil)
                    family? (and uniform? const? (contains? family (bridge/project-name world name)))
                    uniform-prefix? (and family? (<= (count arguments) np))
                    _ (when uniform-prefix?
                        (let [levels (list-values world levels)]
                          (when-not (and (= np (count arguments)) (<= np depth)
                                         (= (count levels) (count parameters))
                                         (every? true?
                                           (map (fn [level parameter]
                                                  (let [[name] (:fields (ctor! world level 4 1 8))]
                                                    (= parameter (bridge/project-name world name)))) levels parameters)))
                            (fail "Nonuniform raw source inductive universes/parameters" {}))
                          (doseq [[i argument] (map-indexed vector arguments)]
                            (let [[idx] (:fields (ctor! world argument 0 1 8))
                                  idx (native/nat-value {:ref? m/ref? :node m/node} world idx)]
                              (when-not (= idx (- depth 1 i))
                                (fail "Nonuniform raw source inductive parameter" {}))))))
                    children (if uniform-prefix? []
                               (case kind
                                 5 (mapv #(vector % depth) (:fields (ctor! world value 5 2 8)))
                                 (6 7) (let [[_ type body] (:fields (ctor! world value kind 3 9))]
                                         [[type depth] [body (inc depth)]])
                                 11 (let [[_ _ body] (:fields (ctor! world value 11 3 8))] [[body depth]])
                                 []))]
                (recur (into todo children) (conj seen key))))))))))

(defn project-declaration
  "Borrow and strictly project pinned source Declaration layouts. Supported
   checking kinds are :definition, :theorem, :opaque and :mutual-definitions. Descriptive
   :inductive/:quotient results cannot be admitted by this namespace yet."
  [world declaration]
  (let [kind (if (m/ref? declaration) (:tag (m/node world declaration)) (tag declaration))
        result
        (case kind
          (1 2 3) (do (ctor! world declaration kind 1 0)
                    {:kind ({1 :definition 2 :theorem 3 :opaque} kind)
                     :constants [(imported/project-constant world declaration)]})
          5 (let [[definitions] (:fields (ctor! world declaration 5 1 0))]
              {:kind :mutual-definitions
               :constants (mapv #(definition world %) (list-values world definitions))})
          4 (if (m/ref? declaration)
              (fail "Quotient declaration must use the pinned scalar constructor" {})
              {:kind :quotient})
          6 (let [_ (raw-inductive-preflight! world declaration)
                  node (ctor! world declaration 6 3 1)
                  [parameters num-params types] (:fields node)
                  unsafe-byte (scalar/read-bytes (:layout node) (:scalar-bytes node)
                                {:index 3 :offset 0 :type "uint8" :region :scalar})
                  _ (when-not (contains? #{0 1} unsafe-byte) (fail "Invalid source inductive safety flag" {}))
                  n (native/nat-value {:ref? m/ref? :node m/node} world num-params)
                  _ (when (> n Integer/MAX_VALUE) (fail "Source inductive parameter count exceeds Java range" {}))]
              {:kind :inductive :level-params (names world parameters) :num-params (int n)
               :unsafe? (= 1 unsafe-byte)
               :types
               (mapv (fn [type]
                       (let [[name expression ctors] (:fields (ctor! world type 0 3 0))]
                         {:name (bridge/project-name world name) :guest-name name :guest-type expression
                          :type (bridge/project-expr world expression)
                          :constructors
                          (mapv (fn [ctor]
                                  (let [[name expression] (:fields (ctor! world ctor 0 2 0))]
                                    {:name (bridge/project-name world name) :guest-name name :guest-type expression
                                     :type (bridge/project-expr world expression)}))
                                (list-values world ctors))})) (list-values world types))})
          (fail "Unsupported source declaration checking projection" {:tag kind}))]
    (assoc result :world world :guest-declaration declaration)))

(defn admit
  "Strictly admit definitions, theorem, safe opaque, or explicitly authorized unsafe/partial
   mutual definitions to a NEW Java Env. :allow-unsafe? authorizes non-safe definitions;
   unsafe opaque checking is deliberately unsupported pending native safety
   parity review. Safe mutual blocks are rejected, as in pinned Lean.

   :checker-fuel is a host resource limit, not native heartbeat equivalence.
   Mutual universe parameters must match in order (pinned environment.cpp:224);
   this adapter checks that condition before the existing Java group checker.
   Original guest declaration/world are returned unchanged on success."
  ([world env declaration] (admit world env declaration {}))
  ([world ^Env env declaration {:keys [allow-unsafe? checker-fuel]
                                :or {checker-fuel 1000000}}]
   (when-not (and (instance? Env env) (integer? checker-fuel) (<= 1 checker-fuel Long/MAX_VALUE))
     (fail "Invalid source declaration checking environment/fuel" {}))
   (let [{:keys [kind constants] :as projected} (project-declaration world declaration)
         ^ConstantInfo first-constant (first constants)
         next-env
         (case kind
           :definition
           (let [safety (.safety first-constant)]
             (when (and (not= 0 safety) (not allow-unsafe?))
               (fail "Unsafe/partial definition admission requires explicit host policy" {}))
             (case safety
               0 (TypeChecker/checkConstant env first-constant (long checker-fuel))
               1 (TypeChecker/checkMutualDefinitions env constants (long checker-fuel))
               2 (let [safe-checking-view
                       (ConstantInfo/mkDefWithHints (.name first-constant) (.levelParams first-constant)
                         (.type first-constant) (.value first-constant) (.getHintsCode first-constant)
                         (byte 0) (.all first-constant))]
                   ;; Pinned add_definition checks a PARTIAL single declaration
                   ;; in safe mode WITHOUT preadding it. Only metadata differs;
                   ;; fully check the identical type/body, then publish original.
                   (TypeChecker/checkConstant env safe-checking-view (long checker-fuel))
                   (.addConstant env first-constant))))
           :theorem (TypeChecker/checkConstant env first-constant (long checker-fuel))
           :opaque (do
                     (when (.isUnsafe first-constant)
                       (fail "Unsafe source opaque admission is not implemented" {:runtime-limit :unsafe-opaque}))
                     (TypeChecker/checkConstant env first-constant (long checker-fuel)))
           :mutual-definitions
           (do
             (when-not (seq constants) (fail "Invalid empty mutual definition" {}))
             (let [safety (.safety first-constant)
                   level-params (vec (.levelParams first-constant))
                   names (mapv #(.name ^ConstantInfo %) constants)]
               (when (= 0 safety) (fail "Mutual definitions must be unsafe or partial" {}))
               (when-not allow-unsafe? (fail "Mutual unsafe/partial admission requires explicit host policy" {}))
               (when-not (= (count names) (count (set names))) (fail "Duplicate mutual declaration name" {}))
               (doseq [^ConstantInfo constant constants]
                 (when-not (= safety (.safety constant)) (fail "Mutual definitions must have the same safety annotation" {}))
                 (when-not (= level-params (vec (.levelParams constant)))
                   (fail "Mutual definitions must have the same universe level parameters" {})))
               (TypeChecker/checkMutualDefinitions env constants (long checker-fuel))))
           (:inductive :quotient)
           (fail "Source declaration requires complete generated constant family admission"
                 {:kind kind :runtime-limit :source-kernel-generation}))]
     (assoc projected :env next-env :constant (when (= 1 (count constants)) first-constant)))))


(defn generate-inductive
  "Generate a complete checked safe source family. Ordinary/indexed/mutual
   generation is the default; :allow-nested? explicitly enables the bounded
   unary-container profile. No guest publication or association occurs here.
   Original type roots are recorded for exact guest provenance reuse."
  ([world env declaration] (generate-inductive world env declaration {}))
  ([world ^Env env declaration {:keys [checker-fuel allow-nested?] :or {checker-fuel 1000000}}]
   (when-not (and (integer? checker-fuel) (<= 1 checker-fuel Long/MAX_VALUE))
     (fail "Invalid source inductive checking fuel" {}))
   (let [{:keys [kind level-params num-params types unsafe?] :as projected}
         (project-declaration world declaration)]
     (when-not (= kind :inductive) (fail "Expected source inductive declaration" {}))
     (let [input (RawInductiveGenerator$Source.
                   (into-array Name level-params) num-params
                   (into-array RawInductiveGenerator$Type
                     (map (fn [{:keys [name type constructors]}]
                            (RawInductiveGenerator$Type. name type
                              (into-array RawInductiveGenerator$Constructor
                                (map (fn [{:keys [name type]}] (RawInductiveGenerator$Constructor. name type)) constructors)))) types))
                   unsafe?)
           nested? (RawNestedInductiveGenerator/hasNestedSource input (long checker-fuel))
           _ (when (and nested? (not allow-nested?))
               (fail "Source nested inductive generation requires explicit bounded-profile policy"
                     {:runtime-limit :source-nested-inductive}))
           result (if nested? (RawNestedInductiveGenerator/generate env input (long checker-fuel))
                              (RawInductiveGenerator/generate env input (long checker-fuel)))
           originals (java.util.IdentityHashMap.)]
       (doseq [type types node (cons type (:constructors type))]
         (.put originals (:type node) (:guest-type node)))
       (assoc projected :env (.env result) :constants (vec (.constants result)) :nested? nested? :original-expressions originals)))))
