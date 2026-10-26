(ns prototype.import-ir
  (:require [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.scalar :as scalar]
            [prototype.typed-ir :as typed]
            [prototype.walk :as walk]
            [prototype.machine :as m]))

(defn name-label [[op parent part]]
  (case op "anonymous" "" (let [p (name-label parent)] (str p (when (seq p) ".") part))))

(defn operand [a]
  (cond (= a "erased") [:imm m/erased]
        (:var a) [:var (get-in a [:var :id :idx])]
        :else (m/fail "Unknown imported operand" {:operand a})))

(defn layout! [i]
  (when-not (and (map? i) (every? #(and (integer? %) (<= 0 % 1048576)) (map i [:size :usize :ssize]))
                 (< (:size i) 256) (< (+ (* 8 (:usize i)) (:ssize i)) 1024))
    (m/fail "Invalid constructor layout" {:layout i})))

(defn type! [ty]
  (typed/type! ty))

(defn expression
  ([e] (expression e nil))
  ([e target-type]
   (let [[op data] (first e)]
     (case op
       :ctor (do (layout! (:i data))
                 (when-not (= (count (:ys data)) (get-in data [:i :size]))
                   (m/fail "Constructor field count mismatch" {:constructor data}))
                 (let [{:keys [size usize ssize cidx]} (:i data) fields (mapv operand (:ys data))]
                   (if (pos? (+ usize ssize))
                     [:scalar-ctor cidx fields {:objects size :usize usize :ssize ssize}]
                     [:ctor cidx fields])))
       :proj [:project [:var (get-in data [:x :idx])] (:i data)]
       :uproj [:scalar-get [:var (get-in data [:x :idx])] {:index (:i data) :offset 0 :type "usize" :region :usize}]
       :sproj (do (scalar/width target-type)
                  [:scalar-get [:var (get-in data [:x :idx])]
                   {:index (:n data) :offset (:offset data) :type target-type :region :scalar}])
       :box (do (scalar/width (:ty data)) [:box (:ty data) [:var (get-in data [:x :idx])]])
       :unbox (do (scalar/width target-type) [:unbox target-type [:var (get-in data [:x :idx])]])
       :isShared [:shared? [:var (get-in data [:x :idx])]]
       :fap [:invoke [:direct (:c data)] (mapv operand (:ys data))]
       :pap [:closure (:c data) (mapv operand (:ys data))]
       :ap [:invoke [:closure [:var (get-in data [:x :idx])]] (mapv operand (:ys data))]
       :lit [:literal (or (get-in data [:v :num :v]) (get-in data [:v :str :v]))]
       (m/fail "Unsupported imported expression" {:expression e})))))

(declare body)
(defn alternative [[op a b]]
  (case op "ctor" [(:cidx a) (body b)] "default" [:default (body a)]
        (m/fail "Unknown alternative" {:op op})))

(defn- body-children [[op a b c d e f]]
  (case op
    "vdecl" [d]
    "jdecl" [c d]
    "case" (mapv (fn [[op a b]]
                   (case op "ctor" b "default" a
                         (m/fail "Unknown alternative" {:op op}))) d)
    "del" [b]
    "setTag" [c]
    ("inc" "dec") [e]
    ("set" "uset") [d]
    "sset" [f]
    ("jmp" "ret" "unreachable") []
    (m/fail "Unsupported imported instruction" {:op op})))

(defn- lowered-body [cache [op a b c d e f]]
  (let [lowered (fn [node] (.get ^java.util.IdentityHashMap cache node))]
    (case op
      "vdecl" (let [_ (type! b) x (:idx a) expr (expression c b) continuation (lowered d)]
                (if (= :invoke (first expr))
                  (if (= continuation [:return [:var x]])
                    [:tail (second expr) (nth expr 2)]
                    [:call x (second expr) (nth expr 2) continuation])
                  [:let x expr continuation]))
      "jdecl" [:join (:idx a) (mapv #(get-in % [:x :idx]) b) (lowered c) (lowered d)]
      "jmp" [:jump (:idx a) (mapv operand b)]
      "case" [:case [:var (:idx b)]
              (mapv (fn [[op a b]]
                      (case op "ctor" [(:cidx a) (lowered b)]
                            "default" [:default (lowered a)])) d)]
      "ret" [:return (operand a)]
      "unreachable" [:unreachable]
      "del" [:del [:var (:idx a)] (lowered b)]
      "setTag" [:set-tag [:var (:idx a)] b (lowered c)]
      "inc" (cond-> [:inc [:var (:idx a)] b (lowered e)] d (conj true))
      "dec" (cond-> [:dec [:var (:idx a)] b (lowered e)] d (conj true))
      "set" [:set [:var (:idx a)] b (operand c) (lowered d)]
      "uset" [:scalar-set [:var (:idx a)] {:index b :offset 0 :type "usize" :region :usize} [:var (:idx c)] (lowered d)]
      "sset" (do (scalar/width e)
                 [:scalar-set [:var (:idx a)] {:index b :offset c :type e :region :scalar} [:var (:idx d)] (lowered f)])
      (m/fail "Unsupported imported instruction" {:op op}))))

(defn body
  "Lower arbitrarily deep FnBody trees with identity-keyed postorder work.
   Raw JSON nodes must never be structurally hashed during traversal."
  [root]
  (let [cache (java.util.IdentityHashMap.)
        pending (java.util.ArrayDeque.)]
    (.addLast pending (object-array [root false]))
    (while (not (.isEmpty pending))
      (let [entry ^objects (.removeLast pending)
            node (aget entry 0)]
        (when-not (.containsKey cache node)
          (if (aget entry 1)
            (.put cache node (lowered-body cache node))
            (do
              (.addLast pending (object-array [node true]))
              (doseq [child (rseq (body-children node))]
                (when-not (.containsKey cache child)
                  (.addLast pending (object-array [child false])))))))))
    (.get cache root)))

(defn validate-manifest! [manifest]
  (when-not (and (= "lean-ir-probe/1" (:schema manifest)) (= "4.33.1" (:leanVersion manifest)))
    (m/fail "Unsupported producer" {:manifest manifest}))
  ;; Historical object-only fixtures predate explicit platform metadata. The
  ;; scalar representation is intentionally the tested x86-64 profile only.
  (when-let [profile (:runtimeProfile manifest)]
    (when-not (and (= 64 (:wordBits profile)) (string? (:target profile))
                   (= "x86_64-unknown-linux-gnu" (:target profile)))
      (m/fail "Unsupported runtime profile" {:profile profile})))
  manifest)

(defn- rows [path]
  (let [rows (mapv #(json/read-str % :key-fn keyword :bigdec false) (str/split-lines (slurp path)))]
    (validate-manifest! (first rows))
    rows))

(defn lower-declaration [row]
  (let [f (get-in row [:ir :fdecl])]
    (when-not f (m/fail "Missing body or extern" {:name (:name row)}))
    (type! (:type f))
    (doseq [p (:xs f)] (type! (:ty p)))
    (let [role (get-in row [:runtime :role])
          initialized? (= "initialized" role)]
      (when (and initialized? (nil? (get-in row [:runtime :initializer])))
        (m/fail "Initialized global has no initializer" {:name (:name row)}))
      [(:f f) (with-meta (cond-> {:params (mapv #(get-in % [:x :idx]) (:xs f))
                                  :body (if initialized? [:read-global (:f f)] (body (:body f)))}
                           initialized? (assoc :runtime-initializer (get-in row [:runtime :initializer]) :result-type (:type f))
                           (contains? #{"closed" "ground" "value"} role) (assoc :global-role role))
                {:runtime-param-types (mapv :ty (:xs f))})])))

(defn lower-typed-declaration
  "Opt-in typed facts for one selected producer declaration. Ordinary lowering
   and bundle installation retain their original function shape and metadata."
  [row]
  (let [facts (typed/companion (get-in row [:ir :fdecl]))
        [name function] (lower-declaration row)]
    [name (assoc function :typed-ir facts)]))

(defn- check-function-profile! [manifests row function]
  ;; The raw lowering function is also used by static audits. Executable bundle
  ;; loading additionally requires explicit ABI provenance for the new scalar
  ;; forms. Conservatively reject mixed legacy/profiled catalogues here.
  (let [decl (or (get-in row [:ir :fdecl]) (get-in row [:ir :extern]))
        sensitive? (or (some #{"uint32" "uint64" "usize"} (cons (:type decl) (map :ty (:xs decl))))
                       (some #(and (vector? %) (contains? #{:scalar-ctor :scalar-get :scalar-set :box :unbox} (first %)))
                             (walk/forms (:body function))))]
    (when sensitive?
      (when (or (empty? manifests) (some #(nil? (:runtimeProfile %)) manifests))
        (m/fail "Scalar execution requires explicit runtime profile" {:name (:name row)}))
      (doseq [manifest manifests] (validate-manifest! manifest)))))

(defn- wrap-globals
  ([functions] (wrap-globals functions {}))
  ([functions existing]
   (let [all-functions (merge existing functions)]
     (reduce-kv
      (fn [result name function]
        (if (or (:global-role function) (:runtime-initializer function))
          (let [target ["str" name "_ansatz_global_initializer"]]
            (when (contains? all-functions target) (m/fail "Global initializer name collision" {:name name}))
            (when (seq (:params function)) (m/fail "Global has parameters" {:name name}))
            (if-let [initializer (:runtime-initializer function)]
              (let [callee (get all-functions initializer)
                    params (:params callee)]
                (when-not (contains? #{[] ["void"] ["erased"]} (:runtime-param-types (meta callee)))
                  (m/fail "Module initializer must accept only an erased world" {:name name}))
                (when-not (and callee (<= (count params) 1))
                  (m/fail "Unsupported module initializer signature" {:name name :initializer initializer}))
                (-> result
                    (assoc target {:params [] :body [:begin-init name initializer (mapv (constantly [:imm m/erased]) params) (:result-type function)]})
                    (assoc name (assoc function :init-target target))))
              (-> result (assoc target (dissoc function :global-role))
                  (assoc name {:params [] :body [:global name target]}))))
          (assoc result name function))) existing functions))))

(defn load-bundle [path]
  (let [rows (rows path)]
    (wrap-globals (into {} (map (fn [row]
                                  (let [[name function :as pair] (lower-declaration row)]
                                    (check-function-profile! [(first rows)] row function) pair)) (rest rows))))))

(defn reconcile-declarations
  "A source-local row may restore nonserialized closed/ground metadata only
  when its actual IR and dependency edges agree with imported artifacts."
  [old row]
  (when-not (= (select-keys old [:kind :ir :dependencies :redirect])
               (select-keys row [:kind :ir :dependencies :redirect]))
    (m/fail "Conflicting declaration" {:name (:name row) :source-artifact-drift true}))
  (cond
    (and (:sourceLocal old) (not (:sourceLocal row))) old
    (and (:sourceLocal row) (not (:sourceLocal old))) row
    (= (:runtime old) (:runtime row)) row
    :else (m/fail "Conflicting declaration" {:name (:name row) :runtime-metadata true})))

(defn index-bundles [paths]
  ;; JSON decoding is still eager. This is a raw declaration catalogue, not
  ;; admission of every indexed body to the executable subset.
  (reduce (fn [catalogue path]
            (let [rows (rows path)]
              (reduce (fn [catalogue row]
                        (let [name (:name row)]
                          (when-not name (m/fail "Missing declaration name" {:path path}))
                          (let [row (if-let [old (get-in catalogue [:declarations name])]
                                      (reconcile-declarations old row) row)]
                            (assoc-in catalogue [:declarations name] row))))
                      (update catalogue :manifests conj (first rows)) (rest rows))))
          {:manifests [] :declarations {}} paths))

(defn- static-targets-tree
  "Static executable edges at instruction/rvalue positions only. Literal data
   is never executable merely because it contains :direct or :closure vectors."
  [root]
  (let [add-target (fn [targets name]
                     (when (nil? name) (m/fail "Malformed static executable dependency" {}))
                     (conj targets name))]
    (loop [pending [root] targets #{}]
      (if (empty? pending) targets
          (let [[op a b c d] (peek pending) pending (pop pending)]
            (case op
              :let (recur (conj pending c) (cond-> targets (= :closure (first b)) (add-target (second b))))
              :call (recur (conj pending d) (cond-> targets (= :direct (first b)) (add-target (second b))))
              :tail (recur pending (cond-> targets (= :direct (first a)) (add-target (second a))))
              :join (recur (conj pending d c) targets)
              :case (recur (into pending (map second b)) targets)
              (:inc :dec :set-tag) (recur (conj pending c) targets)
              :del (recur (conj pending b) targets)
              (:set :scalar-set :host) (recur (conj pending d) targets)
              :suspend (recur (conj pending b) targets)
              (:global :begin-init) (recur pending (add-target targets b))
              (:return :jump :publish-global :unreachable :read-global :publish-io-global :trap)
              (recur pending targets)))))))

(def ^:private frozen-target-scalar-classes
  #{java.lang.Long java.lang.Integer java.lang.Short java.lang.Byte
    java.math.BigInteger clojure.lang.BigInt})
(defn- frozen-target? [root]
  ;; Canonical Lean Name spines need no temporary traversal stack. Unknown
  ;; names fall back without sequencing/hashing their potentially mutable data.
  (loop [value root]
    (cond
      (or (string? value) (keyword? value)
          (contains? frozen-target-scalar-classes (class value))) true
      (= clojure.lang.PersistentVector (class value))
      (let [tag (nth value 0 nil)]
        (and (string? tag)
             (case tag
               "anonymous" (= 1 (count value))
               "str" (and (= 3 (count value)) (string? (nth value 2))
                          (recur (nth value 1)))
               "num" (and (= 3 (count value))
                          (or (string? (nth value 2))
                              (contains? frozen-target-scalar-classes (class (nth value 2))))
                          (recur (nth value 1)))
               false)))
      :else false)))

(defn- canonical-target [targets container expected-op]
  (if-not (= clojure.lang.PersistentVector (class container)) ::fallback
    (if (= expected-op (nth container 0 nil))
      (let [target (nth container 1 nil)]
        (if (frozen-target? target) (conj targets target) ::fallback))
      targets)))

(defn- static-targets-canonical [root]
  ;; The stack and identity table are private to this call. No exotic container
  ;; is sequenced/hashed; callers discard this probe and use the old scanner.
  (let [pending (java.util.ArrayList.)]
    (.add pending root)
    (loop [targets #{} seen nil]
      (if (.isEmpty pending) targets
        (let [node (.remove pending (int (dec (.size pending))))]
          (if-not (and (= clojure.lang.PersistentVector (class node))
                       (keyword? (nth node 0 nil))) ::fallback
            (if (and seen (.containsKey ^java.util.IdentityHashMap seen node))
              (recur targets seen)
              (let [[op a b c d] node
                    seen (or seen (when (contains? #{:join :case} op) (java.util.IdentityHashMap.)))]
                (when seen (.put ^java.util.IdentityHashMap seen node true))
                (case op
                  :let (let [next (canonical-target targets b :closure)]
                         (if (= ::fallback next) ::fallback
                           (do (.add pending c) (recur next seen))))
                  :call (let [next (canonical-target targets b :direct)]
                          (if (= ::fallback next) ::fallback
                            (do (.add pending d) (recur next seen))))
                  :tail (let [next (canonical-target targets a :direct)]
                          (if (= ::fallback next) ::fallback (recur next seen)))
                  :join (do (.add pending d) (.add pending c) (recur targets seen))
                  :case (if (and (= clojure.lang.PersistentVector (class b))
                                 (every? #(and (= clojure.lang.PersistentVector (class %))
                                               (<= 2 (count %))) b))
                          (do (doseq [arm b] (.add pending (nth arm 1))) (recur targets seen)) ::fallback)
                  (:inc :dec :set-tag) (do (.add pending c) (recur targets seen))
                  :del (do (.add pending b) (recur targets seen))
                  (:set :scalar-set :host) (do (.add pending d) (recur targets seen))
                  :suspend (do (.add pending b) (recur targets seen))
                  (:global :begin-init) (if (frozen-target? b) (recur (conj targets b) seen) ::fallback)
                  (:return :jump :publish-global :unreachable :read-global :publish-io-global :trap)
                  (recur targets seen)
                  ::fallback)))))))))

(defn- static-targets-shared
  "Static executable edges. Private scratch state detects actual instruction
   sharing before probing a canonical immutable DAG. Exotic containers retain
   their original sequencing; literal data is never executable code."
  [root]
  (let [pending (java.util.ArrayList.)
        add-target (fn [targets name]
                     (when (nil? name) (m/fail "Malformed static executable dependency" {}))
                     (conj targets name))]
    (.add pending root)
    (loop [targets #{} seen nil probe? true]
      (if (.isEmpty pending) targets
        (let [node (.remove pending (int (dec (.size pending))))]
          (if (and seen (= clojure.lang.PersistentVector (class node))
                   (.containsKey ^java.util.IdentityHashMap seen node))
            (let [result (static-targets-canonical root)]
              (if (= ::fallback result)
                ;; Resume at this exact node, without replaying earlier exotic
                ;; reads. ArrayList accepts nil just as the original stack did.
                (do (.add pending node) (recur targets nil false))
                result))
            (let [[op a b c d] node]
              (when (and seen (= clojure.lang.PersistentVector (class node)))
                (.put ^java.util.IdentityHashMap seen node true))
              (case op
                :let (do (.add pending c) (recur (cond-> targets (= :closure (first b)) (add-target (second b))) seen probe?))
                :call (do (.add pending d) (recur (cond-> targets (= :direct (first b)) (add-target (second b))) seen probe?))
                :tail (recur (cond-> targets (= :direct (first a)) (add-target (second a))) seen probe?)
                :join (do (.add pending d) (.add pending c)
                          (recur targets (or seen (when probe? (java.util.IdentityHashMap.))) probe?))
                :case (do (if (= clojure.lang.PersistentVector (class b))
                            (doseq [arm b] (.add pending (second arm)))
                            ;; Preserve map's legacy chunk-rest behavior for
                            ;; exotic arm sequences rather than doseq's next.
                            (doseq [child (into [] (map second b))] (.add pending child)))
                          (recur targets (or seen (when probe? (java.util.IdentityHashMap.))) probe?))
                (:inc :dec :set-tag) (do (.add pending c) (recur targets seen probe?))
                :del (do (.add pending b) (recur targets seen probe?))
                (:set :scalar-set :host) (do (.add pending d) (recur targets seen probe?))
                :suspend (do (.add pending b) (recur targets seen probe?))
                (:global :begin-init) (recur (add-target targets b) seen probe?)
                (:return :jump :publish-global :unreachable :read-global :publish-io-global :trap)
                (recur targets seen probe?)))))))))

(def ^:private terminal-static-ops
  #{:tail :global :begin-init :return :jump :publish-global :unreachable
    :read-global :publish-io-global :trap})
(defn static-targets
  "Static executable edges with per-call canonical-DAG identity traversal.
   Nonbranching leaves and exotic containers preserve legacy semantics; literal
   payloads are never interpreted as executable edges."
  [root]
  (let [op (when (= clojure.lang.PersistentVector (class root)) (nth root 0 nil))]
    (if (and (keyword? op) (contains? terminal-static-ops op))
      (static-targets-tree root)
      (static-targets-shared root))))

(defn load-closure
  "Link a trusted catalogue's selected closure. :existing-functions preserves
  already-linked bodies and stops dependency traversal at those names. Only new
  globals receive wrappers; this links code and does not execute initializers.
  Dynamic untrusted compiler bundles require program-install admission instead."
  ([catalogue roots] (load-closure catalogue roots lower-declaration))
  ([catalogue roots lower]
   (load-closure catalogue roots lower {}))
  ([catalogue roots lower {:keys [existing-functions] :or {existing-functions {}}}]
   (loop [pending (vec roots) functions {}]
     (if (empty? pending)
       (wrap-globals functions existing-functions)
       (let [name (peek pending) pending (pop pending)]
         (if (or (contains? functions name) (contains? existing-functions name)) (recur pending functions)
             (let [row (or (if-let [read-declaration (:read-declaration catalogue)]
                             (read-declaration name)
                             (get-in catalogue [:declarations name]))
                           (m/fail "Missing declaration dependency" {:name name}))
                   [actual function] (lower row)]
               (when-not (= name actual) (m/fail "Declaration name mismatch" {:name name :actual actual}))
               (check-function-profile! (:manifests catalogue) row function)
            ;; Derive dependencies from the admitted body, rather than trusting
            ;; optional producer dependency metadata.
               (recur (into pending (cond-> (into (static-targets (:body function)) (:runtime-dependencies function))
                                      (:runtime-initializer function) (conj (:runtime-initializer function)))) (assoc functions name function)))))))))
