(ns prototype.imported-kernel
  "Strict checking projection of transported ModuleData ConstantInfo objects.
   Original guest roots and metadata stay intact. No native imported constants
   become trusted merely because finalizeImport accepted their serialized maps.
   Axioms remain explicit assumptions. Unsupported duplicate subsumption fails."
  (:require [prototype.machine :as m] [prototype.kernel-bridge :as bridge]
            [prototype.scalar :as scalar] [prototype.native-scalar :as native]
            [prototype.native-heap :as heap] [prototype.module-store]
            [ansatz.kernel.env :as env] [ansatz.kernel.expr :as expr] [ansatz.kernel.level :as level] [clojure.set :as set])
  (:import [ansatz.kernel ConstantInfo ConstantInfo$RecursorRule Expr Name Env TypeChecker]))

(def ^:private ops {:ref? m/ref? :node m/node})
(defn- fail [message data] (throw (ex-info message data)))
(defn- ctor! [world value tag fields bytes]
  (when-not (m/ref? value) (fail "Expected imported kernel constructor" {:value value}))
  (let [node (m/node world value)]
    (when-not (and (= tag (:tag node)) (bridge/constructor-layout? node fields bytes))
      (fail "Invalid imported kernel constructor layout" {:value value :expected [tag fields bytes]})) node))
(defn- field-byte [node i]
  (scalar/read-bytes (:layout node) (:scalar-bytes node)
                    {:index (count (:fields node)) :offset i :type "uint8" :region :scalar}))
(defn- flag [node i]
  (case (field-byte node i) 0 false 1 true (fail "Invalid imported kernel Bool" {})))
(defn- index! [world value]
  (let [n (native/nat-value ops world value)]
    (when (> n Integer/MAX_VALUE) (fail "Imported kernel Nat exceeds Java index range" {:value n})) (int n)))
(defn- nil?* [value]
  (cond (instance? prototype.machine.Tag value) (= 0 (:tag value))
        (native/native-scalar? value) (= 0 (native/payload value))
        :else (= 0 value)))
(defn- list-values [world value]
  (loop [value value seen #{} out []]
    (if (nil?* value) out
      (do (when (contains? seen value) (fail "Cyclic imported kernel list" {}))
          (let [[head tail] (:fields (ctor! world value 1 2 0))]
            (recur tail (conj seen value) (conj out head)))))))
(defn- names [world value] (vec (:value (bridge/project-with-stats world :names value))))
(defn- base [world value] (:value (bridge/project-with-stats world :constant-val value)))

(defn- constant-name-reference
  "Validate the ConstantInfo envelope and borrow its Name reference."
  [world value]
  (let [tag (:tag (m/node world value))
        [payload] (:fields (ctor! world value tag 1 0))
        [objects bytes] (case tag 0 [1 1] 1 [4 1] 2 [3 0] 3 [3 1]
                         4 [1 1] 5 [6 3] 6 [5 1] 7 [7 2]
                         (fail "Unsupported imported ConstantInfo variant" {:tag tag}))
        [constant] (:fields (ctor! world payload 0 objects bytes))
        [name] (:fields (ctor! world constant 0 3 0))]
    name))


(defn- constant-name [world value]
  (bridge/project-name world (constant-name-reference world value)))

(defn project-constant-name
  "Borrow only a validated ConstantInfo name under explicit Name limits.
   No type/body projection, Java ConstantInfo creation, checking or authority."
  [world value limits]
  (bridge/project-name-bounded world (constant-name-reference world value) limits))

(defn- immutable-projection-sources [world]
  ;; Store validates a closed graph: every reference belongs to that same source.
  ;; Require a singleton at certification AND reuse: another source could shadow
  ;; any descendant ID even if the CI root itself resolves to the expected Store.
  ;; Arbitrary NativeSource implementations and eager heap nodes never qualify.
  (let [sources (:native-imports world)]
    (if (and (= 1 (count sources)) (instance? prototype.module_store.Store (first sources)))
      [(first sources)] [])))

(defn- reusable-projection-sources [world certificate]
  (let [current (immutable-projection-sources world)
        source (first current)]
    (if (and source (false? @(:closed source)) (= 1 (count (:projection-sources certificate)))
             (identical? source (first (:projection-sources certificate)))
             (not-any? #(heap/contains-id? source %) (keys (:heap world))))
      current [])))

(defn- project-constant* [world value projector]
  (let [wrapper (when (m/ref? value) (m/node world value)) tag (:tag wrapper)
        [payload] (:fields (ctor! world value tag 1 0))
        [objects bytes] (case tag 0 [1 1] 1 [4 1] 2 [3 0] 3 [3 1]
                         4 [1 1] 5 [6 3] 6 [5 1] 7 [7 2]
                         (fail "Unsupported imported ConstantInfo variant" {:tag tag}))
        node (ctor! world payload 0 objects bytes)
        [constant a b c d e f] (:fields node)
        project #(-> (bridge/project-with-stats world %1 %2 projector) :value)
        {:keys [name params type]} (project :constant-val constant)
        params (object-array params)
        expr #(bridge/project-expr world % projector)
        n #(index! world %)
        names #(vec (project :names %))
        ns #(object-array (names %))]
    (case tag
      0 (ConstantInfo/mkAxiom name params type (flag node 0))
      1 (ConstantInfo/mkDefWithHints name params type (expr a)
            (long (project :hints b))
            (byte (case (field-byte node 0) 0 1 1 0 2 2 (fail "Invalid DefinitionSafety" {}))) (ns c))
      2 (ConstantInfo/mkThm name params type (expr a) (ns b))
      3 (ConstantInfo/mkOpaque name params type (expr a) (ns b) (flag node 0))
      4 (let [kind (field-byte node 0)
              _ (when-not (< kind 4) (fail "Invalid QuotKind" {}))
              kind (nth [:type :ctor :lift :ind] kind)
              expected (get {"Quot" :type "Quot.mk" :ctor "Quot.lift" :lift "Quot.ind" :ind} (str name))]
          (when-not (= expected kind) (fail "Imported quotient name/kind mismatch" {:name name :kind kind}))
          (ConstantInfo/mkQuot name params type kind))
      5 (ConstantInfo/mkInduct name params type (n a) (n b) (ns c)
            (into-array Name (names d)) (n e) (flag node 0) (flag node 2) (flag node 1))
      6 (ConstantInfo/mkCtor name params type (bridge/project-name world a projector) (n b) (n c) (n d) (flag node 0))
      7 (ConstantInfo/mkRecursor name params type (ns a) (n b) (n c) (n d) (n e)
            (into-array ConstantInfo$RecursorRule
              (map (fn [rule]
                     (let [[constructor fields rhs] (:fields (ctor! world rule 0 3 0))]
                       (ConstantInfo$RecursorRule. (bridge/project-name world constructor projector) (n fields) (expr rhs))))
                   (list-values world f))) (flag node 0) (flag node 1)))))

(defn project-constant
  "Borrow an actual guest ConstantInfo and produce its checking projection.
   An explicit projector shares immutable Java subgraphs only in its exact world.
   Full UInt32 reducibility heights use the exact Java hint API. No admission."
  ([world value] (project-constant* world value (bridge/make-projector world)))
  ([world value projector] (project-constant* world value projector)))

(defn- array-values [world value]
  (when-not (and (m/ref? value) (= :array (:kind (m/node world value))))
    (fail "Expected imported kernel array" {:value value})) (:fields (m/node world value)))

(defn module-constants
  "Borrow one selected ModuleData; validate parallel constNames/constants arrays."
  [world data]
  (let [[_ name-array constant-array _ _] (:fields (ctor! world data 0 5 1))
        names (array-values world name-array) constants (array-values world constant-array)]
    (when-not (= (count names) (count constants)) (fail "ModuleData constant/name count mismatch" {}))
    (mapv (fn [name value]
            (let [ci (project-constant world value) projected (bridge/project-name world name)]
              (when-not (= projected (.name ^ConstantInfo ci)) (fail "ModuleData constant/name mismatch" {}))
              {:constant ci :guest value})) names constants)))

(defn- expression-dependencies [root]
  (loop [pending (if root [root] []) seen (java.util.IdentityHashMap.) out #{}]
    (if (empty? pending) out
      (let [^Expr e (peek pending) pending (pop pending)]
        (if (.containsKey seen e) (recur pending seen out)
          (let [_ (.put seen e true)
                children (case (.tag e)
                           3 [(.o0 e) (.o1 e)] (4 5) [(.o1 e) (.o2 e)]
                           6 [(.o1 e) (.o2 e) (.o3 e)] 9 [(.o1 e)] 10 [(.o1 e)] [])
                out (case (.tag e) 2 (conj out (.o0 e))
                      7 (conj out (Name/mkStr Name/ANONYMOUS_NAME "Nat"))
                      8 (conj out (Name/mkStr Name/ANONYMOUS_NAME "String"))
                      10 (conj out (.o0 e)) out)]
            (recur (into pending children) seen out)))))))
(defn- dependencies [^ConstantInfo ci]
  (cond->
    (reduce set/union (set/union (expression-dependencies (.type ci)) (expression-dependencies (.value ci)))
            (when (.isRecursor ci) (map #(expression-dependencies (.rhs ^ConstantInfo$RecursorRule %)) (.rules ci))))
    ;; Native add_quot validates the already checked Eq family first, even
    ;; though Quot's own type does not explicitly mention Eq.
    (.isQuot ci) (conj (Name/mkStr Name/ANONYMOUS_NAME "Eq"))))

(defn- validate-quot-bootstrap [^Env checked]
  (let [eq-name (Name/mkStr Name/ANONYMOUS_NAME "Eq")
        ^ConstantInfo eq (.lookup checked eq-name)]
    (when-not (and eq (.isInduct eq) (= 1 (count (.levelParams eq))) (= 1 (count (.ctors eq))))
      (fail "Imported quotient bootstrap requires canonical checked Eq family" {}))
    (let [u (level/param (first (.levelParams eq)))
          expected (expr/forall' "α" (expr/sort' u)
                     (expr/forall' "a" (expr/bvar 0)
                       (expr/forall' "b" (expr/bvar 1) (expr/sort' level/zero) :default) :default) :implicit)
          ^ConstantInfo refl (.lookup checked (first (.ctors eq)))
          _ (when-not (and refl (.isCtor refl) (= eq-name (.inductName refl)) (= 1 (count (.levelParams refl))))
              (fail "Imported quotient bootstrap requires canonical checked Eq constructor" {}))
          v (level/param (first (.levelParams refl)))
          expected-refl (expr/forall' "α" (expr/sort' v)
                          (expr/forall' "a" (expr/bvar 0)
                            (expr/app* (expr/const' eq-name [v]) (expr/bvar 1) (expr/bvar 0) (expr/bvar 0)) :default) :implicit)
          tc (TypeChecker. checked)]
      ;; Binder names are not part of the checking projection's semantics.
      (when-not (and (.isDefEq tc (.type eq) expected) (.isDefEq tc (.type refl) expected-refl))
        (fail "Imported quotient bootstrap has noncanonical Eq or constructor type" {})))))

(defn- groups [entries]
  (let [by-name (into {} (map (fn [{:keys [^ConstantInfo constant] :as entry}] [(.name constant) entry])) entries)
        by-ci (into {} (map (fn [[name entry]] [name (:constant entry)])) by-name)
        member-key (fn [^ConstantInfo ci]
                     (cond (.isInduct ci) [:inductive (vec (.all ci))]
                           (.isCtor ci) (let [^ConstantInfo ind (get by-ci (.inductName ci))]
                                          (when-not (and ind (.isInduct ind)) (fail "Missing imported inductive parent" {:name (.name ci)}))
                                          [:inductive (vec (.all ind))])
                           (.isRecursor ci) [:inductive (vec (.all ci))]
                           (and (.isDef ci) (not= 0 (.safety ci))) [:mutual (set (.all ci))]
                           :else [:single (.name ci)]))]
    (mapv (fn [[key members]]
            (let [names (set (map #(.name ^ConstantInfo %) members))]
              (when (= :mutual (first key))
                (when-not (= names (second key)) (fail "Incomplete imported unsafe/partial mutual definition group" {:group key}))
                ;; This is a complete imported block, not independent additions.
                ;; Preserve the native ordered universe-header contract before
                ;; calling even an older resident Java checker.
                (let [params (vec (.levelParams ^ConstantInfo (first members)))]
                  (when-not (every? #(= params (vec (.levelParams ^ConstantInfo %))) members)
                    (fail "Imported mutual definition group must have the same ordered universe level parameters" {:group key}))))
              (when (= :inductive (first key))
                (let [inds (filter #(.isInduct ^ConstantInfo %) members)
                      ctors (filter #(.isCtor ^ConstantInfo %) members)
                      recursors (filter #(.isRecursor ^ConstantInfo %) members)]
                  (when-not (= (set (second key)) (set (map #(.name ^ConstantInfo %) inds)))
                    (fail "Incomplete imported inductive group" {:group key}))
                  (when-not (= (set (mapcat #(seq (.ctors ^ConstantInfo %)) inds)) (set (map #(.name ^ConstantInfo %) ctors)))
                    (fail "Incomplete imported constructor group" {:group key}))
                  ;; Native ordinary inductive admission emits one .rec for each
                  ;; member. Nested lowering has additional recursors and keeps
                  ;; its existing separately checked profile.
                  (when (every? #(zero? (.numNested ^ConstantInfo %)) inds)
                    (when-not (= (set (map #(Name/mkStr (.name ^ConstantInfo %) "rec") inds))
                                 (set (map #(.name ^ConstantInfo %) recursors)))
                      (fail "Incomplete or extra imported ordinary recursor group" {:group key})))))
              {:key key :members members :names names :dependencies (set/difference (reduce set/union #{} (map dependencies members)) names)}))
          (group-by member-key (map :constant entries)))))

(defn- project-entries [world values certificate]
  ;; A separate call frame bounds the large memo's lifetime to projection, before
  ;; constructing dependency graphs or running kernel checking. No result value
  ;; contains this context; only the shared immutable Java values escape.
  (let [projector (bridge/make-projector world)
        reusable-sources (when certificate (reusable-projection-sources world certificate))
        source (first reusable-sources)]
    (mapv (fn [guest]
            (let [name (when (and source (m/ref? guest) (heap/contains-id? source (:id guest)))
                         (constant-name world guest))
                  same-ref? (and name (= guest (get (:constants certificate) name)))
                  cached (when same-ref? (get (:projected certificate) name))]
              (when (and same-ref?
                         (not (and (instance? ConstantInfo cached)
                                   (= name (.name ^ConstantInfo cached))
                                   (identical? cached (.lookup ^Env (:env certificate) name)))))
                (fail "Trusted projection certificate differs from its checked Java environment" {:name name}))
              {:guest guest :constant (if same-ref? cached (project-constant world guest projector))})) values)))

(defn- checking-plan [groups names]
  ;; Build-only group/name/dependency containers remain in this frame. Checking
  ;; retains only member refs, reverse edges, degrees, ready keys and a count.
  (let [by-key (into {} (map #(vector (:key %) %) groups))
        name->group (into {} (mapcat (fn [group] (map #(vector % (:key group)) (:names group))) groups))
        missing (set/difference (reduce set/union #{} (map :dependencies groups)) (set names))]
    (when (seq missing) (fail "Unresolved imported kernel dependencies" {:missing missing}))
    (let [blockers (into {} (map (fn [group] [(:key group) (set (map name->group (:dependencies group)))]) groups))
          dependents (persistent!
                       (reduce-kv (fn [out key dependencies]
                                    (reduce (fn [out dependency]
                                              (assoc! out dependency (conj (get out dependency []) key)))
                                            out dependencies))
                                  (transient {}) blockers))
          initial-degrees (into {} (map (fn [[key deps]] [key (count deps)]) blockers))
          initial-ready (mapv :key (filter #(zero? (get initial-degrees (:key %))) groups))]
      {:members-by-key (into {} (map (fn [[key group]] [key (:members group)])) by-key)
       :dependents dependents :degrees initial-degrees :ready initial-ready
       :group-count (count groups)})))

(defn verify-constants
  "Strictly check borrowed ConstantInfo refs, independent of serialized order.
   :allow-axioms? must explicitly authorize declared assumptions; the three exact
   compiler markers have their own opt-in. Unsafe/partial declarations require
   :allow-unsafe? (the kernel still checks their safety and bodies).
   Optional :projection-certificate is an explicitly trusted host certificate
   returned by this verifier, under the same authority contract as associate-checked.
   It may reuse immutable Java projections ONLY for exact old CI references in
   the identical singleton open module_store.Store, with no local source-range
   shadows. Replaced sources/refs and local objects project normally. This is
   not a Java Env seed: every constant is strictly checked from a fresh Env with
   the current policy. No world changes occur until the whole result is checked."
  ([world values] (verify-constants world values {}))
  ([world values {:keys [allow-axioms? allow-compiler-markers? allow-unsafe? fuel projection-certificate]
                  :or {fuel 20000000}}]
   (when-not (and (integer? fuel) (<= 1 fuel Long/MAX_VALUE)) (fail "Invalid imported checker fuel" {}))
   (when (and projection-certificate
              (not (and (instance? Env (:env projection-certificate))
                        (map? (:constants projection-certificate))
                        (map? (:projected projection-certificate)))))
     (fail "Invalid trusted projection certificate" {}))
   (let [entries (project-entries world values projection-certificate)
         names (map #(.name ^ConstantInfo (:constant %)) entries)]
     (when-not (= (count names) (count (set names))) (fail "Duplicate imported constant; native subsumption is not supported" {}))
     (let [quotients (filter #(.isQuot ^ConstantInfo (:constant %)) entries)]
       (when (and (seq quotients) (not= #{"Quot" "Quot.mk" "Quot.lift" "Quot.ind"}
                                       (set (map #(str (.name ^ConstantInfo (:constant %))) quotients))))
         (fail "Imported quotient bootstrap requires all four canonical primitives" {})))
     (doseq [{:keys [guest ^ConstantInfo constant]} entries]
       (when (and (.isAxiom constant) (not (and allow-compiler-markers? (bridge/compiler-marker-declaration? world guest))) (not allow-axioms?))
         (fail "Imported axiom admission requires explicit host policy" {:name (.name constant)}))
       (when (and (or (.isUnsafe constant) (and (.isDef constant) (not= 0 (.safety constant))))
                  (not (and allow-compiler-markers? (bridge/compiler-marker-declaration? world guest))) (not allow-unsafe?))
         (fail "Imported unsafe/partial admission requires explicit host policy" {:name (.name constant)})))
     (let [{:keys [members-by-key dependents degrees ready group-count]}
           (checking-plan (groups entries) names)]
         (loop [queue ready cursor 0 degrees degrees ^Env checked (Env.) order []]
           (if (= cursor (count queue))
             (do
               (when-not (= group-count cursor)
                 (fail "Unsupported recursive imported kernel dependency group"
                       {:remaining (- group-count cursor)}))
               (let [actual (set (map #(.name ^ConstantInfo %) (.allConstants checked)))]
                 (when-not (= (set names) actual)
                   (fail "Kernel generated constants absent from imported environment" {:extra (set/difference actual (set names))}))
                 {:env checked :projection-sources (immutable-projection-sources world)
                  :constants (into {} (map (fn [{:keys [guest ^ConstantInfo constant]}] [(.name constant) guest])) entries)
                  :projected (into {} (map (fn [{:keys [^ConstantInfo constant]}] [(.name constant) constant])) entries)
                  :order order :axioms (set (map #(.name ^ConstantInfo (:constant %)) (filter #(.isAxiom ^ConstantInfo (:constant %)) entries)))}))
             (let [key (nth queue cursor) members (get members-by-key key)
                   checked (case (first key)
                             :single (let [^ConstantInfo ci (first members)]
                                       (when (.isQuot ci) (validate-quot-bootstrap checked))
                                       (TypeChecker/checkConstant checked ci (long fuel)))
                             :mutual (TypeChecker/checkMutualDefinitions checked members (long fuel))
                             :inductive (let [ind-map (into {} (map #(vector (.name ^ConstantInfo %) %) (filter #(.isInduct ^ConstantInfo %) members)))
                                              inds (mapv ind-map (second key)) first-ind ^ConstantInfo (first inds)]
                                          (env/check-inductive-bundle checked
                                            (env/mk-inductive-bundle (vec (.levelParams first-ind)) (.numParams first-ind) (.isUnsafe first-ind)
                                              inds (filterv #(.isCtor ^ConstantInfo %) members) (filterv #(.isRecursor ^ConstantInfo %) members)) fuel)))
                   [degrees queue] (reduce (fn [[degrees queue] dependent]
                                             (let [degree (dec (get degrees dependent))]
                                               [(assoc degrees dependent degree) (if (zero? degree) (conj queue dependent) queue)]))
                                           [degrees queue] (get dependents key))]
               (recur queue (inc cursor) degrees checked (conj order key)))))))))

(defn verify-module-data
  "Check the actual selected main ModuleData roots (in import order). This does
   not select public/private visibility or implement Lean's subsumesInfo merge;
   callers must pass exactly the roots selected by guest finalizeImport.
   Identical repeated CI references are shared; other duplicate names fail."
  ([world data] (verify-module-data world data {}))
  ([world data options]
   (let [entries (mapcat (fn [data]
                           (let [[_ name-array constant-array _ _] (:fields (ctor! world data 0 5 1))
                                 names (array-values world name-array)
                                 constants (array-values world constant-array)]
                             (when-not (= (count names) (count constants))
                               (fail "ModuleData constant/name count mismatch" {}))
                             (map (fn [name guest]
                                    (let [name (bridge/project-name world name)]
                                      (when-not (= name (constant-name world guest))
                                        (fail "ModuleData constant/name mismatch" {}))
                                      {:name name :guest guest})) names constants))) data)
         values (loop [remaining (seq entries) seen {} out []]
                  (if-not remaining out
                    (let [{:keys [guest name]} (first remaining)]
                      (if-let [previous (get seen name)]
                        (if (= guest previous) (recur (next remaining) seen out)
                          (fail "Imported duplicate subsumption is not supported" {:name name}))
                        (recur (next remaining) (assoc seen name guest) (conj out guest))))))]
     (assoc (verify-constants world values options) :module-data (vec data)))))

(defn- constant-shape [^ConstantInfo ci]
  ;; vec may retain a Java array's backing storage. Copy array elements so a
  ;; previously captured shape cannot change with public ConstantInfo arrays.
  (let [common [(.tag ci) (.name ci) (mapv identity (.levelParams ci)) (.type ci)]]
    (into common
      (case (.tag ci)
        0 [(.isUnsafe ci)]
        1 [(.value ci) (.getHintsCode ci) (.safety ci) (mapv identity (.all ci))]
        2 [(.value ci) (mapv identity (.all ci))]
        3 [(.value ci) (mapv identity (.all ci)) (.isUnsafe ci)]
        4 [(.quotKind ci)]
        5 [(.numParams ci) (.numIndices ci) (mapv identity (.all ci)) (mapv identity (.ctors ci)) (.numNested ci) (.isRec ci) (.isReflexive ci) (.isUnsafe ci)]
        6 [(.inductName ci) (.cidx ci) (.numParams ci) (.numFields ci) (.isUnsafe ci)]
        7 [(mapv identity (.all ci)) (.numParams ci) (.numIndices ci) (.numMotives ci) (.numMinors ci)
           (mapv (fn [^ConstantInfo$RecursorRule rule] [(.ctor rule) (.nfields rule) (.rhs rule)]) (.rules ci)) (.isK ci) (.isUnsafe ci)]))))

(defn checking-shape
  "Complete immutable Java ConstantInfo checking shape, including metadata,
   binder annotations, safety and generated recursor rules. No guest caches."
  [constant]
  (constant-shape constant))

(defn associate-checked
  "Anchor an already checked import to an EXACT matching guest environment.
   Helpers :root/:constants/:quot-init? borrow guest Environment and return owned
   Kernel.Environment / Array ConstantInfo / Bool respectively. The constants
   helper must enumerate the precise checked kernel map, not elaborator extras.
   Optional :constant-map returns an owned exact map root and enables later
   header-only associations with the same map identity and quotient flag.
   World-local anchors prevent RC-based unique reuse and survive immutable forks.
   This function does not admit a root merely because it is nonempty."
  [context world environment helpers certificate]
  (doseq [key [:root :constants :quot-init?]]
    (when-not (vector? (get helpers key)) (fail "Missing imported kernel guest helper" {:helper key})))
  (let [[world root] ((:invoke context) world (:root helpers) [environment])
        _ (when-not (m/ref? root) (fail "Imported kernel root must be a guest reference" {}))
        _ (when (contains? (:kernel-environments world) (:id root)) (fail "Imported kernel root already anchored" {}))
        [world values] ((:invoke context) world (:constants helpers) [environment])
        constants (array-values world values)
        reusable-sources (reusable-projection-sources world certificate)
        actual (reduce (fn [out value]
                         (let [source (some #(when (and (m/ref? value) (heap/contains-id? % (:id value))) %) reusable-sources)
                               name (when source (constant-name world value))
                               same-ref? (and source (= value (get (:constants certificate) name)))
                               ^ConstantInfo ci (if same-ref?
                                                  (get (:projected certificate) name)
                                                  (project-constant world value))
                               name (.name ci)]
                           (when (contains? out name) (fail "Duplicate checked guest environment constant" {:name name}))
                           (let [checked (get (:projected certificate) name)]
                             (when-not (and checked (or (identical? ci checked)
                                                    (= (constant-shape ci) (constant-shape checked))))
                               (fail "Guest imported constant differs from its checked projection" {:name name})))
                           (assoc out name value))) {} constants)
        _ (when-not (= actual (:constants certificate))
            (fail "Guest imported kernel environment differs from checked constants" {:expected (count (:constants certificate)) :actual (count actual)}))
        [world quot?] ((:invoke context) world (:quot-init? helpers) [environment])
        quot? (native/nat-value ops world quot?)
        _ (when-not (contains? #{0 1} quot?) (fail "Invalid guest quotient initialization flag" {}))
        _ (when-not (= (= 1 quot?) (.isQuotEnabled ^Env (:env certificate)))
            (fail "Guest imported quotient state differs from checked kernel" {}))
        world (m/release world values 1)
        [world witness] (if-let [helper (:constant-map helpers)]
                          (do
                            (when-not (vector? helper) (fail "Invalid constant-map helper" {}))
                            (let [[world constants] ((:invoke context) world helper [environment])]
                              (when-not (m/ref? constants) (fail "Imported constant map must be a guest reference" {}))
                              (m/node world constants)
                              [world {:constant-map constants :quot-init? (= 1 quot?)}]))
                          [world nil])]
    ;; Keep both helper-returned owners when a map witness was requested.
    (assoc-in world [:kernel-environments (:id root)]
              (merge {:anchor root :env (:env certificate)} witness))))
