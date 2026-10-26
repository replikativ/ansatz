(ns prototype.typed-blocks
  "Bounded, demand-only control-flow preparation. This is data, not execution or
   source admission. Inputs must be paired lower-typed-declaration results."
  (:require [prototype.machine :as m]
            [prototype.fingerprint :as fingerprint]
            [prototype.typed-ir :as typed]))

(def ^:private integer-types #{"uint8" "uint16" "uint32" "uint64" "usize"})
(def ^:private profile-fields
  #{:schema :producer-commit :phase :word-bits :layout :abi-generation :target})

(defn- invalid! [message data] (m/fail message (assoc data :typed-block-validation true)))
(defn- fallback! [reason data] (throw (ex-info "Typed block fallback" (assoc data ::fallback reason))))
(defn- require! [condition message data] (when-not condition (invalid! message data)))

(defn- profile! [p]
  (require! (and (map? p) (= profile-fields (set (keys p)))
                 (= "lean-block-profile/1" (:schema p))
                 (string? (:producer-commit p)) (re-matches #"[0-9a-f]{40}" (:producer-commit p))
                 (string? (:abi-generation p)) (seq (:abi-generation p)))
            "Invalid typed block profile" {})
  (when-not (= [:expanded-rc 64 :lean-64 :jvm]
               (mapv p [:phase :word-bits :layout :target]))
    (fallback! :unsupported-profile {}))
  p)

(defn- charge! [counts budgets k]
  (let [n (get (swap! counts update k (fnil inc 0)) k)]
    (when (> n (get budgets k)) (fallback! :budget {:budget k :limit (get budgets k)}))))

(def ^:dynamic *work!* (fn [_] nil))
(def ^:dynamic *max-registers* 0)

(defn- plain-map? [x]
  (contains? #{clojure.lang.PersistentArrayMap clojure.lang.PersistentHashMap} (class x)))

(defn- name! [name]
  (loop [n name]
    (*work!* 1)
    (require! (= clojure.lang.PersistentVector (class n)) "Invalid canonical name" {})
    (case (first n)
      "anonymous" (require! (= 1 (count n)) "Invalid canonical name" {})
      "str" (do (require! (and (= 3 (count n)) (string? (nth n 2))) "Invalid canonical name" {}) (recur (second n)))
      "num" (do (require! (and (= 3 (count n))
                                 (or (and (integer? (nth n 2)) (<= 0 (nth n 2)))
                                     (and (string? (nth n 2)) (re-matches #"0|[1-9][0-9]*" (nth n 2)))))
                            "Invalid canonical name" {}) (recur (second n)))
      (invalid! "Invalid canonical name" {}))))

(defn- parameters! [ps]
  (require! (= clojure.lang.PersistentVector (class ps)) "Invalid block parameters" {})
  (*work!* (count ps))
  (doseq [{:keys [id type borrow] :as p} ps]
    (require! (and (plain-map? p) (= #{:id :type :borrow} (set (keys p)))
                   (integer? id) (<= 0 id Integer/MAX_VALUE) (boolean? borrow))
              "Invalid block parameter" {})
    (when (>= id *max-registers*) (fallback! :register-budget {:id id}))
    (typed/type! type))
  (require! (= (count ps) (count (set (map :id ps)))) "Duplicate block parameter" {})
  ps)

(defn- signature! [f]
  (let [c (:typed-ir f) s (:signature c)]
    (when-not c (fallback! :missing-companion {}))
    (require! (and (= "lean-typed-companion/1" (:schema c)) (= :producer-ir (:node-space c))
                   (vector? (:nodes c))) "Invalid typed companion" {})
    (let [[digest guards :as key] (:source-key c)]
      (require! (and (= clojure.lang.PersistentVector (class key)) (= 2 (count key))
                     (string? digest) (re-matches #"[0-9a-f]{64}" digest)
                     (= clojure.lang.PersistentHashSet (class guards)) (empty? guards))
                "Invalid typed source key" {}))
    (*work!* (count (:nodes c)))
    (parameters! (:params s)) (typed/type! (:result-type s))
    (require! (= (:params f) (mapv :id (:params s))) "Typed parameter mismatch" {})
    s))

(defn- instruction! [node]
  (require! (and (= clojure.lang.PersistentVector (class node)) (seq node))
            "Invalid canonical instruction container" {})
  (when-not (contains? #{:let :call :tail :return :join :jump :case} (first node))
    (fallback! :unsupported-instruction {:op (first node)}))
  (require! (and (= clojure.lang.PersistentVector (class node))
                 (= (get {:let 4 :call 5 :tail 3 :return 2 :join 5 :jump 3 :case 3} (first node)) (count node)))
            "Malformed canonical instruction" {:op (first node)})
  (when (= :case (first node))
    (let [alts (nth node 2)]
      (require! (= clojure.lang.PersistentVector (class alts)) "Invalid canonical alternatives" {})
      (*work!* (count alts))
      (doseq [alt alts]
        (require! (and (= clojure.lang.PersistentVector (class alt)) (= 2 (count alt))
                       (or (= :default (first alt))
                           (and (integer? (first alt)) (<= 0 (first alt) Integer/MAX_VALUE))))
                  "Invalid canonical alternative" {}))))
  node)

(defn- children [[op _ _ _ _ :as node]]
  (case op
    :let [(nth node 3)] :call [(nth node 4)]
    :join [(nth node 3) (nth node 4)]
    :case (mapv second (nth node 2))
    (:tail :return :jump) []
    (fallback! :unsupported-instruction {:op op})))

(defn- skeleton [[op a b c :as node]]
  (case op
    :let [:let a b nil] :call [:call a b c nil]
    :join [:join a b nil nil]
    :case [:case a (mapv (fn [[tag _]] [tag nil]) b)]
    node))

(defn- restore [form children]
  (case (first form)
    :let (assoc form 3 (first children))
    :call (assoc form 4 (first children))
    :join (assoc form 3 (first children) 4 (second children))
    :case (assoc form 2 (mapv (fn [[tag _] body] [tag body]) (nth form 2) children))
    form))

(defn legacy-body
  "Reconstruct the canonical executable body from a prepared function's table.
   No execution, typed facts or block scheduling participate in reconstruction."
  [function]
  (let [table (:instructions function) cache (object-array (count table))
        pending (java.util.ArrayDeque.)]
    (.addLast pending [(:entry-pc function) false])
    (while (not (.isEmpty pending))
      (let [[pc done?] (.removeLast pending) {:keys [form children]} (nth table pc)]
        (when (nil? (aget cache pc))
          (if done?
            (aset cache pc (restore form (mapv #(aget cache %) children)))
            (do (.addLast pending [pc true])
                (doseq [child (rseq children)]
                  (when (nil? (aget cache child)) (.addLast pending [child false]))))))))
    (aget cache (:entry-pc function))))

(defn- operand-type! [env operand]
  (require! (and (vector? operand) (= 2 (count operand))) "Invalid typed operand shape" {})
  (let [[op id] operand]
   (case op
    :var (do (when-not (and (integer? id) (<= 0 id Integer/MAX_VALUE))
               (invalid! "Invalid local index" {:id id}))
             (or (get env id) (invalid! "Unknown typed local" {:id id})))
    :imm (if (= id m/erased) "erased" (fallback! :unsupported-immediate {:operand operand}))
    (invalid! "Invalid typed operand" {}))))

(defn- compatible! [actual expected]
  ;; Lean's checker intentionally leaves some representation compatibility to
  ;; compiler invariants. Stronger unavailable proofs disable optimization.
  (when-not (= actual expected)
    (fallback! :type-compatibility {:actual actual :expected expected})))

(defn- args! [env args params]
  (require! (vector? args) "Invalid argument vector" {})
  (*work!* (count args))
  (require! (= (count args) (count params)) "Typed call or jump arity mismatch" {})
  (doseq [[a p] (map vector args params)] (compatible! (operand-type! env a) (:type p))))

(defn- fact! [nodes id]
  (require! (and (integer? id) (<= 0 id) (< id (count nodes))) "Invalid producer node reference" {:id id})
  (nth nodes id))

(defn- prepare-function [name f resolve-signature counts budgets]
  (let [signature (signature! f) companion (:typed-ir f) nodes (:nodes companion)
        pcs (java.util.IdentityHashMap.) instructions (java.util.ArrayList.)
        blocks (java.util.ArrayList.) pending (java.util.ArrayDeque.)
        marked (atom #{}) origins (atom {}) calls (atom #{})
        mark! (fn [id]
                (require! (and (integer? id) (<= 0 id Integer/MAX_VALUE)) "Invalid binder index" {:id id})
                (when (>= id *max-registers*) (fallback! :register-budget {:id id}))
                (require! (not (contains? @marked id)) "Duplicate variable or join index" {:id id})
                (swap! marked conj id))
        pc! (fn [node]
              (if (.containsKey pcs node) (.get pcs node)
                  (do (charge! counts budgets :max-instructions)
                      (let [id (.size instructions)] (.put pcs node id) (.add instructions nil) id))))
        enqueue! (fn [node producer env joins]
                   (charge! counts budgets :max-blocks)
                   (let [id (.size blocks) pc (pc! node)]
                     (.add blocks nil) (.addLast pending [id pc node producer env joins]) id))
        env (into {} (map (juxt :id :type)) (:params signature))]
    (when (or (:global-role f) (:runtime-initializer f)) (fallback! :global-function {}))
    (doseq [p (:params signature)] (mark! (:id p)))
    (let [entry (enqueue! (:body f) (:root companion) env {})]
      (while (not (.isEmpty pending))
        (let [[bid pc node producer env joins] (.removeFirst pending)
              _ (instruction! node)
              [op a b c d] node fact (fact! nodes producer)
              cs (:children fact)
              _ (require! (vector? cs) "Invalid typed node children" {})
              _ (when (contains? #{:vdecl :case} (:op fact)) (typed/type! (:type fact)))
              _ (*work!* 1) kids (children node)
              child-pcs (mapv pc! kids)
              base {:id bid :pc pc :params {:kind :canonical-registers :types env} :scope env :ops []}
              align! (fn [expected n]
                       (require! (and (= expected (:op fact)) (= n (count cs)))
                                 "Typed companion/body mismatch" {:pc pc :producer producer}))
              edge! (fn [i next-env next-joins]
                      (enqueue! (nth kids i) (nth cs i) next-env next-joins))
              direct! (fn [target args result]
                        (require! (and (vector? target) (= 2 (count target))) "Invalid direct target shape" {})
                        (when-not (= :direct (first target)) (fallback! :indirect-call {}))
                        (let [callee (second target) s (resolve-signature callee)]
                          (swap! calls conj callee)
                          (args! env args (:params s))
                          (compatible! (:result-type s) result)))
              block
              (case op
                :let (do (align! :vdecl 1)
                         (require! (= a (:id fact)) "Typed binder mismatch" {:pc pc})
                         (when-not (and (vector? b) (= 2 (count b)) (= :literal (first b)) (integer? (second b))
                                        (not (neg? (second b))) (contains? integer-types (:type fact)))
                           (fallback! :unsupported-literal {:type (:type fact)}))
                         (let [width (get {"uint8" 8 "uint16" 16 "uint32" 32 "uint64" 64 "usize" 64} (:type fact))]
                           (when (>= (bigint (second b)) (bigint (.shiftLeft java.math.BigInteger/ONE width)))
                             (fallback! :literal-range {:type (:type fact)})))
                         (mark! a)
                         (assoc base :ops [{:pc pc :op :literal :id a :type (:type fact) :value (second b)}]
                                :terminator {:op :next :args {:kind :identity-registers} :block (edge! 0 (assoc env a (:type fact)) joins)}))
                :call (do (align! :vdecl 1)
                          (require! (= a (:id fact)) "Typed call binder mismatch" {:pc pc})
                          (direct! b c (:type fact)) (mark! a)
                          (assoc base :terminator {:op :call :pc pc :dest a :type (:type fact)
                                                   :target b :args c :continuation-args {:kind :call-result :dest a :preserve :identity-registers} :block (edge! 0 (assoc env a (:type fact)) joins)}))
                :tail (do (align! :vdecl 1)
                          (let [ret (fact! nodes (first cs))]
                            (require! (and (= :ret (:op ret)) (empty? (:children ret)))
                                      "Typed tail origin mismatch" {:pc pc})
                            (mark! (:id fact))
                            (compatible! (:type fact) (:result-type signature))
                            (direct! a b (:type fact))
                            (swap! origins assoc pc {:producer-node-ids [producer (first cs)]}))
                          (assoc base :terminator {:op :tail :pc pc :target a :args b}))
                :return (do (align! :ret 0)
                            (compatible! (operand-type! env a) (:result-type signature))
                            (assoc base :terminator {:op :return :pc pc :value a}))
                :case (do (align! :case (count b))
                          (require! (= a [:var (:scrutinee-id fact)]) "Typed case scrutinee mismatch" {:pc pc})
                          (compatible! (operand-type! env a) (:type fact))
                          (when-not (contains? #{"uint8" "uint16" "uint32"} (:type fact)) (fallback! :non-scalar-case {}))
                          (let [tags (mapv first b)]
                            (when-not (and (= (count tags) (count (set tags)))
                                           (or (not (some #{:default} tags)) (= :default (peek tags))))
                              (fallback! :unsupported-case-profile {})))
                          (require! (= (mapv first b) (:alternatives fact)) "Typed case alternatives mismatch" {:pc pc})
                          (assoc base :terminator {:op :case :pc pc :value a
                                                   :alternatives (mapv (fn [i [tag _]] [tag {:block (edge! i env joins) :args {:kind :identity-registers}}]) (range) b)}))
                :join (do (align! :jdecl 2)
                          (parameters! (:params fact))
                          (require! (and (= a (:join-id fact)) (= b (mapv :id (:params fact))))
                                    "Typed join mismatch" {:pc pc})
                          (mark! a)
                          (doseq [p (:params fact)] (mark! (:id p)))
                          (let [body (edge! 0 (into env (map (juxt :id :type)) (:params fact)) joins)
                                descriptor {:params (:params fact) :captures env :block body}
                                next (edge! 1 env (assoc joins a descriptor))]
                            (assoc base :terminator {:op :join :pc pc :join-id a :join descriptor :args {:kind :identity-registers} :block next})))
                :jump (do (align! :jmp 0)
                          (require! (= a (:join-id fact)) "Typed jump mismatch" {:pc pc})
                          (let [join (or (get joins a) (invalid! "Unknown typed join" {:id a}))]
                            (args! env b (:params join))
                            (assoc base :terminator {:op :jump :pc pc :join-id a :args b
                                                     :block (:block join) :captures (:captures join)
                                                     :transfer :simultaneous}))))]
          (when-not (.get instructions pc)
            (.set instructions pc {:pc pc :form (skeleton node) :children child-pcs}))
          (when-not (contains? @origins pc) (swap! origins assoc pc {:producer-node-ids [producer]}))
          (.set blocks bid block)))
      {:name name :params (:params signature) :result-type (:result-type signature)
       :entry entry :entry-pc (.get pcs (:body f)) :blocks (vec blocks)
       :instructions (vec instructions) :source-key (:source-key companion) :origins @origins :calls @calls})))

(defn prepare-unit
  "Prepare only rooted reachable selected code. Unsupported optimization returns
   fallback; invalid supplied structure/scope/arity throws. Registry entries have
   {:params typed-params :result-type IRType :generation string :extern string}. No functions,
   runtime values, Source or World may occur in descriptors."
  [selected-functions roots profile intrinsics budgets]
  (try
    (profile! profile)
    (require! (and (map? budgets) (= #{:max-functions :max-instructions :max-blocks :max-work :max-registers} (set (keys budgets)))
                   (every? #(and (integer? %) (pos? %) (<= % Integer/MAX_VALUE)) (vals budgets)))
              "Invalid typed preparation budgets" {})
    (require! (and (map? selected-functions) (map? intrinsics) (vector? roots)) "Invalid typed unit inputs" {})
    (require! (plain-map? profile) "Invalid profile container" {})
    (let [counts (atom {}) signatures (atom {}) demanded (atom {})
          work! (fn [n] (when (> (:max-work (swap! counts update :max-work (fnil + 0) n)) (:max-work budgets))
                         (fallback! :budget {:budget :max-work :limit (:max-work budgets)})))
          resolve-signature
          (fn [name]
            (name! name)
            (or (get @signatures name)
                (let [_ (charge! counts budgets :max-functions)
                      s (if-let [f (get selected-functions name)]
                          (signature! f)
                          (if-let [s (get intrinsics name)]
                            (do (require! (and (plain-map? s) (= #{:params :result-type :generation :extern} (set (keys s)))
                                               (string? (:extern s))
                                               (string? (:generation s)) (seq (:generation s))
                                               (seq (:extern s))) "Invalid intrinsic descriptor" {})
                                (parameters! (:params s)) (typed/type! (:result-type s))
                                (swap! demanded assoc name s) s)
                            (fallback! :missing-callee {:name name})))]
                  (swap! signatures assoc name s) s)))]
      (binding [*work!* work! *max-registers* (:max-registers budgets)]
       (work! (count roots))
       (doseq [root roots] (name! root))
       (loop [pending (vec (distinct roots)) functions {}]
        (if (empty? pending)
          {:status :ready :unit {:schema "lean-blocks/1" :profile profile
                                :profile-key (fingerprint/uncached-key profile) :roots roots
                                :functions functions :intrinsics @demanded :counts @counts}}
          (let [name (peek pending) pending (pop pending)]
            (if (contains? functions name) (recur pending functions)
                (let [f (or (get selected-functions name) (fallback! :missing-root {:name name}))]
                  (resolve-signature name)
                  (let [prepared (prepare-function name f resolve-signature counts budgets)
                        calls (:calls prepared)]
                    (recur (into pending (filter #(contains? selected-functions %) calls))
                           (assoc functions name (dissoc prepared :calls)))))))))))
    (catch clojure.lang.ExceptionInfo e
      (if-let [reason (::fallback (ex-data e))]
        {:status :fallback :reason reason :details (dissoc (ex-data e) ::fallback)}
        (throw e)))))
