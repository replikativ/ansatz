(ns prototype.typed-tail
  "Optional Pattern preparation for bounded pure scalar tail regions. No executor."
  (:require [pattern.nanopass.dialect :refer [def-dialect => valid?]]
            [pattern.nanopass.pass :refer [defpass]]
            [pattern.r3.core :refer [rule]]
            [pattern.r3.combinators :refer [rule-list]]
            [prototype.typed-blocks :as blocks]
            [prototype.typed-ir :as typed]
            [prototype.runtime-abi :as abi]
            [prototype.machine :as m]
            [prototype.fingerprint :as fingerprint]))

(def ^:private scalar-types #{"uint8" "uint16" "uint32" "uint64" "usize"})
(def ^:private nat-types #{"tagged" "tobject"})
(def ^:private value-types (into scalar-types nat-types))
(def ^:private base-budgets #{:max-functions :max-instructions :max-blocks :max-work :max-registers})
(def ^:private budget-fields (into base-budgets #{:max-params :max-emission :max-constants :max-chunk-cost}))
(defn- bounded-natural? [x] (and (integer? x) (<= 0 x Integer/MAX_VALUE)))
(defn- origin? [x] (and (vector? x) (= 2 (count x)) (vector? (first x)) (bounded-natural? (second x))))
(defn- operands? [xs] (and (vector? xs) (every? #(and (vector? %) (= 2 (count %)) (= :var (first %)) (bounded-natural? (second %))) xs)))
(defn- alternatives? [xs] (and (vector? xs) (every? #(and (vector? %) (= 2 (count %)) (or (= :default (first %)) (bounded-natural? (first %))) (bounded-natural? (second %))) xs)))
(defn- operation? [x] (contains? #{:add :sub :eq} x))
(defn- carrier? [x] (contains? #{:long :unsigned-bigint :literal :propagate} x))
(defn- lane? [x] (contains? #{:long-bits :nonnegative-long} x))
(defn- rc-operation? [x] (contains? #{:inc :dec} x))
(defn- rc-count? [x] (and (integer? x) (<= 0 x Integer/MAX_VALUE)))

(def-dialect TypedTailOp
  (terminals [o origin?] [i bounded-natural?] [t value-types] [st scalar-types] [nt nat-types] [n integer?] [f vector?]
             [as operands?] [alts alternatives?] [operation operation?] [c carrier?]
             [rc rc-operation?] [count rc-count?] [check boolean?] [persistent boolean?])
  (Operation [s :enforce]
    [:literal ?o ?i ?st ?n]
    [:nat-literal ?o ?i ?nt ?n]
    [:intrinsic ?o ?i ?t :unsigned64 ?operation ?f ?as ?c]
    [:intrinsic ?o ?i ?t :nat ?operation ?f ?as :long]
    [:rc ?o ?rc ?i ?count ?check ?persistent ?t]
    [:case ?o ?as ?alts]
    [:tail ?o ?f ?as]
    [:tail-intrinsic ?o ?t :unsigned64 ?operation ?f ?as ?c]
    [:tail-intrinsic ?o ?t :nat ?operation ?f ?as :long]
    [:return ?o ?as])
  (entry Operation))

(def-dialect RepresentedTailOp
  (terminals [o origin?] [i bounded-natural?] [t value-types] [st scalar-types] [nt nat-types] [n integer?] [f vector?]
             [as operands?] [alts alternatives?] [operation operation?] [c carrier?]
             [rc rc-operation?] [count rc-count?] [check boolean?] [persistent boolean?] [l lane?])
  (Operation [s :enforce]
    [:literal ?o ?i [:repr ?st :long-bits] ?n [:carrier :literal]]
    [:literal ?o ?i [:repr ?nt :nonnegative-long] ?n [:carrier :literal]]
    [:intrinsic ?o ?i [:repr ?t :long-bits] :unsigned64 ?operation ?f ?as [:carrier ?c]]
    [:intrinsic ?o ?i [:repr ?t ?l] :nat ?operation ?f ?as [:carrier :long]]
    [:rc ?o ?rc ?i ?count ?check ?persistent [:repr ?t ?l] [:proof :nonreference]]
    [:case ?o ?as ?alts :long-bits]
    [:tail ?o ?f ?as :simultaneous-carriers]
    [:tail-intrinsic ?o [:repr ?t :long-bits] :unsigned64 ?operation ?f ?as [:carrier ?c]]
    [:tail-intrinsic ?o [:repr ?t ?l] :nat ?operation ?f ?as [:carrier :long]]
    [:return ?o ?as [:carrier :propagate]])
  (entry Operation))

(defpass lower-operation (=> TypedTailOp RepresentedTailOp)
  (rule-list [
  (rule '[:literal ?o ?i ?st ?n] [:literal o i [:repr st :long-bits] n [:carrier :literal]])
  (rule '[:nat-literal ?o ?i ?nt ?n] [:literal o i [:repr nt :nonnegative-long] n [:carrier :literal]])
  (rule '[:intrinsic ?o ?i ?t :unsigned64 ?operation ?f ?as ?c]
        [:intrinsic o i [:repr t :long-bits] :unsigned64 operation f as [:carrier c]])
  (rule '[:intrinsic ?o ?i ?t :nat ?operation ?f ?as :long]
        [:intrinsic o i [:repr t (if (nat-types t) :nonnegative-long :long-bits)] :nat operation f as [:carrier :long]])
  (rule '[:rc ?o ?rc ?i ?count ?check ?persistent ?t]
        [:rc o rc i count check persistent [:repr t (if (nat-types t) :nonnegative-long :long-bits)] [:proof :nonreference]])
  (rule '[:case ?o ?as ?alts] [:case o as alts :long-bits])
  (rule '[:tail ?o ?f ?as] [:tail o f as :simultaneous-carriers])
  (rule '[:tail-intrinsic ?o ?t :unsigned64 ?operation ?f ?as ?c]
        [:tail-intrinsic o [:repr t :long-bits] :unsigned64 operation f as [:carrier c]])
  (rule '[:tail-intrinsic ?o ?t :nat ?operation ?f ?as :long]
        [:tail-intrinsic o [:repr t (if (nat-types t) :nonnegative-long :long-bits)] :nat operation f as [:carrier :long]])
  (rule '[:return ?o ?as] [:return o as [:carrier :propagate]])]))

(defn- invalid! [message data] (m/fail message (assoc data :typed-tail-validation true)))
(defn- fallback! [reason data] (throw (ex-info "Typed tail fallback" (assoc data ::fallback reason))))
(defn- require! [ok message data] (when-not ok (invalid! message data)))

(defn lower-operation!
  "Grammar pass only. Scoped typing and actual ABI proofs are separate M2/selection checks."
  [operation]
  (require! (valid? TypedTailOp operation) "Outside TypedTailOp grammar" {})
  (let [out (lower-operation operation)]
    (require! (valid? RepresentedTailOp out) "Outside RepresentedTailOp grammar" {})
    out))

(defn descriptor-signatures [descriptors]
  (require! (and (map? descriptors) (<= (count descriptors) 64)) "Selected descriptor budget" {})
  (reduce-kv (fn [out name descriptor]
               (let [d (abi/validate-scalar-description! descriptor)]
                 (require! (= name (:name d)) "Descriptor name mismatch" {})
                 (assoc out (:name d) {:params (:params d) :result-type (:result-type d)
                                      :generation (:semantic-generation d) :extern (:extern d)}))) {} descriptors))

(defn- ordinary-leaf? [x]
  (or (nil? x) (boolean? x) (string? x) (keyword? x)
      (contains? #{Long Integer Short Byte clojure.lang.BigInt java.math.BigInteger} (class x))))

(defn- pure-data!
  "Validate and charge finite standard data before any generic fingerprint walks.
   Identity memo bounds DAGs; opaque values and metadata owners cannot enter plans."
  [root spend!]
  (let [seen (java.util.IdentityHashMap.) pending (java.util.ArrayDeque.)]
    (.addLast pending root)
    (while (not (.isEmpty pending))
      (let [x (.removeLast pending)]
        (when-not (.containsKey seen x)
          (.put seen x true) (spend! :work 1)
          (when (or (and (= clojure.lang.BigInt (class x))
                         (> (.bitLength (.toBigInteger ^clojure.lang.BigInt x)) 4096))
                    (and (= java.math.BigInteger (class x))
                         (> (.bitLength ^java.math.BigInteger x) 4096)))
            (fallback! :numeric-data-budget {}))
          (cond
            (ordinary-leaf? x) nil
            (and (contains? #{clojure.lang.PersistentArrayMap clojure.lang.PersistentHashMap
                              clojure.lang.PersistentVector clojure.lang.PersistentHashSet} (class x))
                 (nil? (meta x)))
            (do (spend! :work (count x))
                (doseq [child (if (map? x) (mapcat identity x) x)]
                  ;; ArrayDeque cannot hold nil.
                  (when (some? child) (.addLast pending child))))
            :else (fallback! :opaque-code-data {})))))))

(defn- same-body? [expected actual spend!]
  (let [pairs (java.util.ArrayDeque.) seen (java.util.IdentityHashMap.)]
    (.addLast pairs [expected actual])
    (loop []
      (if (.isEmpty pairs) true
          (let [[a b] (.removeLast pairs)]
            (spend! :work 1)
            (cond
              (identical? a b) (recur)
              (and (= clojure.lang.PersistentVector (class a)) (= clojure.lang.PersistentVector (class b)))
              (if-not (= (count a) (count b)) false
                  (let [right (or (.get seen a) (java.util.IdentityHashMap.))]
                    (when-not (.containsKey right b)
                      (.put seen a right) (.put right b true)
                      (spend! :work (count a))
                      (doseq [i (range (count a))] (.addLast pairs [(nth a i) (nth b i)])))
                    (recur)))
              (and (ordinary-leaf? a) (ordinary-leaf? b) (= (class a) (class b)) (= a b)) (recur)
              :else false))))))

(defn- wrapper-shape [d]
  (let [params (mapv :id (:params d)) dest (inc (reduce max 0 params))]
    {:params params :runtime-extern (:extern d)
     :body [:let dest [:runtime (:extern d) (mapv #(vector :var %) params)] [:return [:var dest]]]}))

(defn- nat-function? [f descriptors]
  (or (some nat-types (cons (:result-type f) (map :type (:params f))))
      (some (fn [{:keys [ops terminator]}]
              (or (some #(nat-types (:type %)) ops)
                  (= :nat (get-in descriptors [(second (:target terminator)) :domain])))) (:blocks f))))

(defn- check-nat-constants!
  "Run before source comparison/fingerprinting; never decimalize a rejected Nat
   literal. M2 has already bounded the number of block visits."
  [name f spend!]
  (doseq [{:keys [ops]} (:blocks f) {:keys [op type value count]} ops]
    (spend! :work 1)
    (when (and (= :literal op) (= "object" type))
      (fallback! :unsupported-value-representation {:name name :type type}))
    (when (and (= :literal op) (nat-types type))
      (when-not (and (= Long (class value)) (<= 0 (long value)))
        (fallback! :unsupported-nat-literal {:name name :type type})))
    (when (and (contains? #{:inc :dec} op) (not (rc-count? count)))
      (fallback! :unsupported-rc-count {:name name}))))

(defn- value-representation! [type proof]
  (cond
    (scalar-types type) {:ir-type type :domain :unsigned-integer :lane :long-bits :proof proof}
    (nat-types type) {:ir-type type :domain :nat-integer :lane :nonnegative-long :proof proof}
    :else (fallback! :unsupported-value-representation {:type type})))

(defn- function-representations!
  "One table per function. An entry refinement is a required invocation guard,
   never a logical Nat assertion inferred from an IR object type."
  [name f nat? demand! spend!]
  (let [representations (atom (into {} (map (fn [{:keys [id type]}]
                                             [id (value-representation!
                                                  type (if (nat-types type)
                                                         {:kind :entry-guard :carrier :long :range [0 Long/MAX_VALUE]}
                                                         {:kind :entry-guard :carriers [:long :bigint]}))])) (:params f)))
        operand! (fn [operand]
                   (or (get @representations (second operand))
                       (fallback! :missing-value-representation {:name name})))
        call! (fn [target args]
                (let [d (demand! (second target))]
                  (when (= :nat (:domain d))
                    (doseq [arg args]
                      (when-not (= :nonnegative-long (:lane (operand! arg)))
                        (fallback! :nat-operand-representation {:name name}))))
                  d))]
    (doseq [{:keys [ops terminator]} (:blocks f)]
      (spend! :work 1)
      (doseq [{:keys [op id type value count]} ops]
        (case op
          :literal (swap! representations assoc id
                          (value-representation! type {:kind :literal :carrier (if (nat-types type) :long :literal) :value value
                                                       :class (.getName (class value))}))
          (:inc :dec) (do (when-not nat? (fallback! :unsupported-rc {:op op :name name}))
                         (when-not (rc-count? count) (fallback! :unsupported-rc-count {:name name}))
                         (operand! [:var id]))
          (fallback! :unsupported-operation {:op op :name name})))
      (when (= :call (:op terminator))
        (let [d (call! (:target terminator) (:args terminator))
              semantic (abi/scalar-operation (:extern d))]
          (swap! representations assoc (:dest terminator)
                 (value-representation! (:result-type d)
                                        {:kind :intrinsic :domain (:domain d) :extern (:extern d)
                                         :carrier (:result-carrier semantic)
                                         :condition (:result-condition semantic)})))))
    @representations))

(defn- check-tail-representations! [functions spend!]
  (doseq [[name f] functions block (:blocks f)
          :when (= :tail (first (:typed-operation block)))
          :let [[_ _ target args] (:typed-operation block)
                source-representations (:representations f)
                target-function (get functions target)]
          [arg parameter] (map vector args (:params target-function))]
    (spend! :work 1)
    (when (nat-types (:type parameter))
      (when-not (= :nonnegative-long (get-in source-representations [(second arg) :lane]))
        (fallback! :nat-tail-representation {:name name :target target})))))

(defn- actual-dependency! [runtime-functions name expected kind spend!]
  (let [actual (get runtime-functions name)]
    (when-not (and actual (= (:params expected) (:params actual))
                   (= (:runtime-extern expected) (:runtime-extern actual))
                   (every? #{:params :body :runtime-extern :typed-ir} (keys actual))
                   (same-body? (:body expected) (:body actual) spend!))
      (fallback! :runtime-code-mismatch {:name name :kind kind}))
    ;; Keep canonical pure facts, never arbitrary attrs or catalogue ownership.
    (assoc (into {} (select-keys expected [:params :body :runtime-extern])) :kind kind)))

(defn- graph-costs [function-name function budgets spend!]
  (let [bs (:blocks function) pending (java.util.ArrayDeque.) states (byte-array (count bs))
        order (java.util.ArrayList.)]
    (.addLast pending [(:entry function) false])
    (while (not (.isEmpty pending))
      (let [[id exit?] (.removeLast pending)]
        (require! (and (bounded-natural? id) (< id (count bs))) "Invalid represented block reference" {})
        (if exit?
          (when-not (= 2 (aget states id)) (aset-byte states id (byte 2)) (.add order id))
          (case (aget states id)
            2 nil
            1 (fallback! :intrafunction-cycle {:name function-name})
            0 (do (spend! :work 1) (aset-byte states id (byte 1))
                  (.addLast pending [id true])
                  (doseq [child (rseq (:successors (nth bs id)))] (.addLast pending [child false])))))))
    (let [costs (object-array (count bs)) emission (object-array (count bs))]
      (doseq [id order]
        (let [b (nth bs id) successors (:successors b)
              cost (+ (:cost b) (reduce max 0 (map #(aget costs %) successors)))
              expanded (+ 1 (reduce + 0 (map #(aget emission %) successors)))]
          (when (> cost (:max-chunk-cost budgets)) (fallback! :chunk-cost-budget {:name function-name}))
          (when (> expanded (:max-emission budgets)) (fallback! :emission-budget {:name function-name}))
          (aset costs id cost) (aset emission id expanded)))
      {:max-cost (aget costs (:entry function)) :expanded-operations (aget emission (:entry function))})))

(defn- components [graph]
  ;; Function budget is at most 16; DFS depth is explicitly bounded by that cap.
  (let [seen (atom #{}) order (atom [])]
    (letfn [(visit [n] (when-not (contains? @seen n)
                        (swap! seen conj n) (doseq [child (get graph n)] (visit child)) (swap! order conj n)))]
      (doseq [name (keys graph)] (visit name)))
    (let [reverse-graph (reduce-kv (fn [g from tos] (reduce #(update %1 %2 (fnil conj []) from) g tos)) {} graph)
          seen (atom #{})]
      (letfn [(collect [n result]
                (if (contains? @seen n) result
                    (do (swap! seen conj n) (reduce #(collect %2 %1) (conj result n) (get reverse-graph n)))))]
        (into [] (keep (fn [n] (when-not (contains? @seen n) (collect n [])))) (rseq @order))))))

(defn prepare-region
  "Bounded M2 -> Pattern represented graph preparation. No executor or admission.
   Runtime code and selected typed declarations must describe the same source."
  [runtime-functions selected-typed-functions roots descriptors profile budgets]
  (try
    (require! (and (map? budgets) (= budget-fields (set (keys budgets)))
                   (every? #(and (integer? %) (pos? %) (<= % Integer/MAX_VALUE)) (vals budgets))
                   (<= (:max-functions budgets) 16) (<= (:max-params budgets) 16))
              "Invalid tail preparation budgets" {})
    (let [signatures (descriptor-signatures descriptors)
          prepared (blocks/prepare-unit selected-typed-functions roots profile signatures (select-keys budgets base-budgets))]
      (if-not (= :ready (:status prepared)) prepared
        (let [unit (:unit prepared) counts (atom {:work (get-in unit [:counts :max-work] 0) :constants 0})
              spend! (fn [kind amount]
                       (let [n (get (swap! counts update kind (fnil + 0) amount) kind)
                             limit (get budgets (case kind :work :max-work :constants :max-constants))]
                         (when (> n limit) (fallback! :budget {:budget kind :limit limit}))))
              dependencies (atom {}) demanded (atom {}) typed-keys (atom {})
              demand! (fn [name]
                        (or (get @demanded name)
                            (let [d (some-> (get descriptors name) abi/validate-scalar-description!)]
                              (when-not d (fallback! :non-intrinsic-call {:name name}))
                              (when-not (= profile (:profile d)) (fallback! :descriptor-profile-mismatch {:name name}))
                              (swap! dependencies assoc name (actual-dependency! runtime-functions name (wrapper-shape d) :extern spend!))
                              (swap! demanded assoc name d) d)))
              _ (pure-data! roots spend!)
              _ (pure-data! profile spend!)
              _ (pure-data! budgets spend!)
              prepared-fs
              (reduce-kv
               (fn [out name f]
                 (let [original (get selected-typed-functions name)
                       nat? (boolean (nat-function? f descriptors))]
                   (pure-data! name spend!)
                   (when (> (count (:params f)) (:max-params budgets)) (fallback! :parameter-budget {:name name}))
                   (when-not (every? value-types (cons (:result-type f) (map :type (:params f))))
                     (fallback! :non-scalar-signature {:name name}))
                   (check-nat-constants! name f spend!)
                   (pure-data! (into {} (dissoc original :typed-ir)) spend!)
                   (pure-data! (:typed-ir original) spend!)
                   (swap! dependencies assoc name (actual-dependency! runtime-functions name original :source spend!))
                   (let [key (typed/typed-code-key original profile)]
                     (when (seq (second key)) (fallback! :opaque-code-key {:name name}))
                     (swap! typed-keys assoc name key))
                   (let [representations (function-representations! name f nat? demand! spend!)
                         represented
                         (mapv
                          (fn [{:keys [id pc ops terminator scope]}]
                            (spend! :work 1) (spend! :constants 1)
                            (let [origin [name pc] op (:op terminator)
                                  [form successors cost trace carrier]
                                  (case op
                                    :next (let [{:keys [id type value count check persistent] operation :op} (first ops)]
                                            (case operation
                                              :literal [[(if (nat-types type) :nat-literal :literal) origin id type value]
                                                        [(:block terminator)] 1
                                                        [{:space :canonical :function name :pc pc :event :literal}]
                                                        {:kind :literal :value value :class (.getName (class value))}]
                                              (:inc :dec) [[:rc origin operation id count check persistent type]
                                                           [(:block terminator)] 1
                                                           [{:space :canonical :function name :pc pc :event operation}] nil]
                                              (fallback! :unsupported-operation {:op operation :name name})))
                                    :call (let [target (second (:target terminator)) d (demand! target)
                                                semantic (abi/scalar-operation (:extern d))]
                                            [[:intrinsic origin (:dest terminator) (:result-type d) (:domain d) (:operation d) target (:args terminator) (:result-carrier semantic)]
                                             [(:block terminator)] 3
                                             [{:space :canonical :function name :pc pc :event :call :frame-peak 1}
                                              {:space :runtime-wrapper :function target :pc 0 :event :runtime}
                                              {:space :runtime-wrapper :function target :pc 1 :event :return}]
                                             {:kind (:result-carrier semantic)}])
                                    :case [[:case origin [(:value terminator)] (mapv (fn [[tag edge]] [tag (:block edge)]) (:alternatives terminator))]
                                           (mapv (comp :block second) (:alternatives terminator)) 1
                                           [{:space :canonical :function name :pc pc :event :case}] nil]
                                    :tail (let [target (second (:target terminator)) args (:args terminator)]
                                            (if (contains? (:functions unit) target)
                                              [[:tail origin target args] [] 1
                                               [{:space :canonical :function name :pc pc :event :tail :frame-peak 0}]
                                               {:kind :propagate}]
                                              (let [d (demand! target) semantic (abi/scalar-operation (:extern d))]
                                                (when (= :nat (:domain d))
                                                  (doseq [arg args]
                                                    (when-not (= :nonnegative-long (get-in representations [(second arg) :lane]))
                                                      (fallback! :nat-operand-representation {:name name}))))
                                                [[:tail-intrinsic origin (:result-type d) (:domain d) (:operation d) target args (:result-carrier semantic)] [] 3
                                                 [{:space :canonical :function name :pc pc :event :tail :frame-peak 0}
                                                  {:space :runtime-wrapper :function target :pc 0 :event :runtime}
                                                  {:space :runtime-wrapper :function target :pc 1 :event :return}]
                                                 {:kind (:result-carrier semantic)}])))
                                    :return [[:return origin [(:value terminator)]] [] 1
                                             [{:space :canonical :function name :pc pc :event :return}] {:kind :propagate}]
                                    (fallback! :unsupported-control {:op op :name name}))]
                              {:id id :pc pc :debug-scope scope :typed-operation form
                               :operation (lower-operation! form) :successors successors :cost cost
                               :trace trace :carrier carrier :logical-frame-peak (if (= op :call) 1 0)})) (:blocks f))
                         result {:params (:params f) :result-type (:result-type f) :entry (:entry f)
                                 :entry-pc (:entry-pc f) :origins (:origins f)
                                 :canonical-instructions (:instructions f) :blocks represented}
                         result (assoc result ::representations representations ::nat? nat?)]
                     (assoc out name (merge result (graph-costs name result budgets spend!)))))) {} (:functions unit))
              nat-unit? (boolean (some ::nat? (vals prepared-fs)))
              fs (update-vals prepared-fs
                              (fn [f]
                                (cond-> (dissoc f ::representations ::nat?)
                                  nat-unit? (assoc :representations (::representations f)))))
              tail-graph (update-vals fs (fn [f] (into [] (keep #(when (= :tail (first (:typed-operation %))) (nth (:typed-operation %) 2))) (:blocks f))))
              _ (when nat-unit? (check-tail-representations! fs spend!))
              region {:schema (if nat-unit? "lean-represented-tail/2" "lean-represented-tail/1") :profile profile :roots roots
                      :preparation-generation (if nat-unit? "typed-tail/2" "typed-tail/1")
                      :pattern-commit "6d0242ee589d88b336f7dd6f820efa993d2b6f3b"
                      :functions fs :tail-graph tail-graph :components (components tail-graph)
                      :descriptors @demanded :dependencies @dependencies :typed-code-keys @typed-keys
                      :budgets budgets :counts @counts}]
          ;; Typed source keys bind full code; do not tree-hash repeated scope
          ;; maps or the shared executable graph a second time.
          (let [key-data (-> region
                             (dissoc :counts)
                             (update :dependencies #(update-vals % (fn [d] (if (= :source (:kind d)) (dissoc d :body) d))))
                             (update :functions
                                     #(update-vals % (fn [f]
                                                       (-> f
                                                           (dissoc :canonical-instructions)
                                                           (update :blocks (fn [bs] (mapv (fn [b] (dissoc b :debug-scope)) bs))))))))]
            {:status :ready :region (assoc region :key (fingerprint/uncached-key key-data))}))))
    (catch clojure.lang.ExceptionInfo e
      (if-let [reason (::fallback (ex-data e))]
        {:status :fallback :reason reason :details (dissoc (ex-data e) ::fallback)}
        (throw e)))))
