(ns ansatz.export.evidence-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.export.evidence :as evidence]
            [ansatz.export.storage :as storage]
            [org.replikativ.persistent-sorted-set :as pss]
            [ansatz.kernel.constant-info :as constant-info]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Name Level Expr ConstantInfo Env]
           [java.nio ByteBuffer]))

(def limits
  {:declarations 8 :shell-items 256 :expr-nodes 64 :expr-edges 128 :expr-depth 32
   :raw-bytes 4096 :name-nodes 64 :name-chars 256 :name-depth 32
   :level-nodes 64 :level-depth 32 :level-visits 4096})

(defn raw [size write!]
  (let [bb (ByteBuffer/allocate size)] (write! bb) (.array bb)))
(def sort-raw (raw 5 #(doto ^ByteBuffer % (.put (byte 1)) (.putInt 0))))
(defn app-raw [f x]
  (raw 9 #(doto ^ByteBuffer % (.put (byte 3)) (.putInt f) (.putInt x))))
(defn mdata-raw [child]
  (raw 5 #(doto ^ByteBuffer % (.put (byte 9)) (.putInt child))))
(defn const-raw [id]
  (raw 7 #(doto ^ByteBuffer % (.put (byte 2)) (.putInt id) (.putShort (short 0)))))
(def declaration-name (name/from-string "Evidence.thm"))
(def shell {:tag 2 :name declaration-name :lps [] :all [declaration-name]
            :type-id 0 :value-id 1})

(defn fixture
  ([] (fixture {0 sort-raw 1 (app-raw 0 0)}))
  ([exprs]
   (let [reads (atom [])]
     {:reads reads
      :sources {:shell (fn [n] (swap! reads conj [:shell n]) (when (= n declaration-name) shell))
                :expr (fn [id] (swap! reads conj [:expr id]) (get exprs id))
                :name (fn [id] (swap! reads conj [:name id]) (when (= id 0) declaration-name))
                :level (fn [id] (swap! reads conj [:level id]) (when (= id 0) Level/ZERO_LEVEL))}})))

(defn materialize [sources bounds]
  (evidence/materialize [declaration-name] sources bounds storage/resolve-ci-shell))

(deftest requested-complete-proof-has-isolated-cache-and-retains-dag-sharing
  (let [{:keys [sources reads]} (fixture)
        a (materialize sources limits)
        b (materialize sources limits)
        ^ConstantInfo ci (get (:constants a) declaration-name)]
    (is (constant-info/complete? ci))
    (is (= 2 (get-in a [:usage :expr-nodes])))
    (is (= 2 (get-in a [:usage :expr-edges])))
    (is (= 2 (get-in a [:usage :expr-depth])))
    (is (= 14 (get-in a [:usage :raw-bytes])))
    (is (identical? (.o0 ^Expr (.value ci)) (.type ci)))
    (is (identical? (.o1 ^Expr (.value ci)) (.type ci)))
    (is (not (identical? ci (get (:constants b) declaration-name))))
    (is (not (identical? (.type ci) (.type ^ConstantInfo (get (:constants b) declaration-name)))))
    (is (= 0 (.-storeId ^Expr (.type ci))))
    (is (= 1 (.-storeId ^Expr (.value ci))))
    (set! (.-storeId ^Expr (.type ci)) 99)
    (is (= 0 (.-storeId ^Expr (.type ^ConstantInfo (get (:constants b) declaration-name)))))
    (is (= 2 (count (filter #{[:expr 0]} @reads))))
    (is (= 2 (count (filter #{[:expr 1]} @reads))))))

(deftest shared-level-DAGs-have-a-separate-expanded-walk-budget
  (let [{:keys [sources]} (fixture)
        u (Level/param (name/from-string "u"))
        v (Level/param (name/from-string "v"))
        w (Level/param (name/from-string "w"))
        ;; Real normalized constructors retain overlapping DAGs here. hasParam
        ;; can short-circuit, but hasMVar revisits every shared subtree. Keep
        ;; distinct nodes/depth inside their budgets while expanded work exceeds
        ;; its independent limit. No private constructors/reflection are used.
        shared (first (nth (iterate (fn [[a b]]
                                      [(Level/max (Level/succ a) (Level/succ b))
                                       (Level/imax a w)]) [u v]) 15))
        limited (assoc sources :level (constantly shared))
        error (try (materialize limited limits) nil
                   (catch clojure.lang.ExceptionInfo cause cause))]
    (is (= :level-visits (:limit (ex-data error))))
    ;; A shallow overlapping DAG remains valid. Its tree has five visits even
    ;; though only four distinct nodes are retained; account for two predicates.
    (let [child (Level/max u v)
          shallow (Level/imax child u)
          actual (materialize (assoc sources :level (constantly shallow)) limits)]
      (is (= 4 (get-in actual [:usage :level-nodes])))
      (is (= 10 (get-in actual [:usage :level-visits])))
      (is (constant-info/complete? (get (:constants actual) declaration-name))))))

(deftest each-explicit-evidence-bound-is-enforced
  (let [{:keys [sources]} (fixture)
        usage (:usage (materialize sources limits))
        exact (merge limits (into {} (map (fn [[key used]] [key (max 1 used)])) usage))]
    (is (constant-info/complete? (get (:constants (materialize sources exact)) declaration-name)))
    (doseq [[key used] usage :when (> used 1)]
      (testing (str key)
        (is (thrown? clojure.lang.ExceptionInfo (materialize sources (assoc exact key (dec used)))))))
    (doseq [bad [(dissoc limits :raw-bytes) (assoc limits :unknown 5)
                 (assoc limits :raw-bytes 0) (assoc limits :raw-bytes 1.5)
                 (assoc limits :expr-depth 257) (assoc limits :raw-bytes 9223372036854775808N)]]
      (is (thrown? clojure.lang.ExceptionInfo (materialize sources bad))))))

(deftest request-scope-is-exact-and-no-unrequested-declaration-is-read
  (let [{:keys [sources reads]} (fixture)]
    (is (thrown? clojure.lang.ExceptionInfo
                 (evidence/materialize [declaration-name declaration-name] sources limits storage/resolve-ci-shell)))
    (is (empty? @reads))
    (is (thrown? clojure.lang.ExceptionInfo
                 (evidence/materialize [declaration-name] sources (assoc limits :declarations 0) storage/resolve-ci-shell)))
    (is (empty? @reads))
    (materialize sources limits)
    (is (= [[:shell declaration-name]] (filter #(= :shell (first %)) @reads)))))

(deftest requested-names-pass-depth-budget-before-hashing-or-backend-lookup
  (let [{:keys [sources reads]} (fixture)
        deep-name (reduce (fn [prefix _] (Name/mkStr prefix "part")) Name/ANONYMOUS_NAME (range 40))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"depth exceeded"
                          (evidence/materialize [deep-name deep-name] sources
                                                (assoc limits :name-depth 16) storage/resolve-ci-shell)))
    (is (empty? @reads))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"depth exceeded"
                          (materialize (assoc sources :shell (fn [_] (assoc shell :name deep-name)))
                                       (assoc limits :name-depth 16))))))

(deftest full-bodies-are-required-and-all-roots-validated-before-ci-construction
  (doseq [exprs [{0 sort-raw}
                 {0 sort-raw 1 (mdata-raw 1)}
                 {0 sort-raw 1 (mdata-raw 2) 2 (mdata-raw 1)}
                 {0 sort-raw 1 (app-raw 0 -1)}
                 {0 sort-raw 1 (byte-array [(byte 127)])}
                 {0 sort-raw 1 (byte-array [(byte 3)])}
                 {0 sort-raw 1 (byte-array [1 0 0 0 0 0])}
                 {0 sort-raw 1 (byte-array [8 0 0 0 1 (unchecked-byte 255)])}]]
    (let [{:keys [sources]} (fixture exprs) constructed (atom 0)]
      (is (thrown? Exception
                   (evidence/materialize [declaration-name] sources limits
                                         (fn [& args] (swap! constructed inc)
                                           (apply storage/resolve-ci-shell args)))))
      (is (zero? @constructed)))))

(deftest shell-presence-does-not-turn-missing-metadata-into-empty-arrays
  (doseq [bad [(dissoc shell :all) (assoc shell :all nil) (dissoc shell :lps)
               (assoc shell :lps nil) (assoc shell :all [123])
               {:tag 7 :name declaration-name :lps [] :type-id 0 :all []
                :num-params 0 :num-indices 0 :num-motives 1 :num-minors 0
                :rules [{:ctor declaration-name :nfields 0}] :is-k false :is-unsafe false}]]
    (let [{:keys [sources]} (fixture) constructed (atom 0)]
      (is (thrown? clojure.lang.ExceptionInfo
                   (evidence/materialize [declaration-name] (assoc sources :shell (constantly bad)) limits
                                         (fn [& args] (swap! constructed inc)
                                           (apply storage/resolve-ci-shell args)))))
      (is (zero? @constructed)))))

(deftest shared-subdag-and-deep-paths-are-counted-without-expansion
  (let [exprs (into {0 sort-raw} (for [i (range 1 12)] [i (app-raw (dec i) (dec i))]))
        {:keys [sources reads]} (fixture exprs)
        sources (assoc sources :shell (fn [_] (assoc shell :value-id 11)))
        result (materialize sources limits)]
    (is (= 12 (get-in result [:usage :expr-nodes])))
    (is (= 22 (get-in result [:usage :expr-edges])))
    (is (= 12 (get-in result [:usage :expr-depth])))
    (is (= 12 (count (filter #(= :expr (first %)) @reads))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (materialize sources (assoc limits :expr-depth 11))))))

(deftest level-and-name-payloads-are-bounded-before-expr-construction
  (let [{:keys [sources]} (fixture {0 sort-raw 1 (const-raw 0)})
        long-name (name/from-string "one.two.three.four")
        nested-level (reduce (fn [l _] (Level/succ l)) Level/ZERO_LEVEL (range 8))]
    (is (thrown? clojure.lang.ExceptionInfo
                 (materialize (assoc sources :name (constantly long-name)) (assoc limits :name-depth 4))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (materialize (assoc sources :name (constantly long-name)) (assoc limits :name-chars 5))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (materialize (assoc sources :level (constantly nested-level)) (assoc limits :level-depth 8))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (materialize (assoc sources :level (constantly nested-level)) (assoc limits :level-nodes 8))))))

(deftest local-overlay-and-external-view-identity-are-distinct
  (let [nm declaration-name
        local (ConstantInfo/mkAxiom nm (object-array []) (Expr/sort Level/ZERO_LEVEL false) false)
        a (fn [_] local) b (fn [_] nil) visible (constantly true)
        base (.withExternalLookup (Env.) a 1)
        overlay (.addOrReplaceConstant base local)]
    (is (nil? (.lookupLocal base nm)))
    (is (identical? local (.lookupLocal overlay nm)))
    (is (.sameExternalView base overlay))
    (is (not (.sameExternalView base (.withExternalLookup base b 1))))
    (is (not (.sameExternalView base (.withExternalLookupFiltered base a 1 visible))))))

(defn tree [cmp entries]
  (into (pss/sorted-set* {:cmp cmp}) entries))

(defn with-captured-branch [options f]
  (let [head (atom {:env-root :old-env :exprs-root :old-exprs :names-root :old-names
                    :levels-root :old-levels :dag-storage? true :env-count 1})
        reads (atom [])
        trees {:old-env (tree storage/name-cmp [[declaration-name shell]])
               :old-exprs (tree storage/id-cmp [[0 sort-raw] [1 (app-raw 0 0)]])
               :old-names (tree storage/id-cmp [[0 declaration-name]])
               :old-levels (tree storage/id-cmp [[0 Level/ZERO_LEVEL]])}]
    ;; Real branch-loader/PSS lookup/resolution, only backend IO is modeled.
    (with-redefs [storage/store-get (fn [_ key] (swap! reads conj key) @head)
                  pss/restore-by (fn [_ root _]
                                   (or (get trees root)
                                       (throw (AssertionError. "must retain old captured roots"))))
                  storage/open-store (fn [& _] (throw (AssertionError. "must not open a store")))
                  storage/close-store (fn [& _] (throw (AssertionError. "store is borrowed")))]
      (let [loaded (apply storage/load-env {:store :model :storage :model} "main"
                          (mapcat identity options))]
        (f loaded head reads)))))

(deftest captured-roots-survive-head-change-without-polluting-defs-only-view
  (with-captured-branch
    {:value-policy :defs-only}
    (fn [^Env loaded head reads]
      (let [^ConstantInfo thin (.lookup loaded declaration-name)]
        (is (nil? (.value thin)))
        (reset! head {:env-root :new-env :exprs-root :new-exprs :names-root :new-names
                      :levels-root :new-levels :dag-storage? true :env-count 1})
        (let [full (get (:constants (storage/full-ci-evidence loaded [declaration-name] limits))
                        declaration-name)]
          (is (constant-info/complete? full))
          (is (identical? thin (.lookup loaded declaration-name)))
          (is (nil? (.value ^ConstantInfo (.lookup loaded declaration-name))))
          (is (= [[:branches "main"]] @reads)))))))

(deftest evidence-refuses-local-shadows-copied-view-and-hidden-names
  (with-captured-branch
    {:value-policy :defs-only}
    (fn [^Env loaded _ _]
      (let [local (ConstantInfo/mkThm declaration-name (object-array [])
                                      (Expr/sort Level/ZERO_LEVEL false) nil (object-array []))
            shadow (.addOrReplaceConstant loaded local)
            replaced (.withExternalLookup loaded (constantly nil) 0)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"local declaration"
                              (storage/full-ci-evidence shadow [declaration-name] limits)))
        (is (identical? local (.lookup shadow declaration-name)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"external Env view"
                              (storage/full-ci-evidence replaced [declaration-name] limits))))))
  (with-captured-branch
    {:value-policy :defs-only :visible? (constantly false)}
    (fn [loaded _ _]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not visible"
                            (storage/full-ci-evidence loaded [declaration-name] limits))))))

(deftest legacy-no-evidence-env-never-falls-back-to-unrestricted-full-lookup
  (let [looked-up? (atom false)
        loaded (.withExternalLookup (Env.) (fn [_] (reset! looked-up? true) nil) 0)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"no captured bounded"
                          (storage/full-ci-evidence loaded [declaration-name] limits)))
    (is (false? @looked-up?))))

(deftest partition-reports-explicit-absence-with-one-shared-batch-cache
  (let [{:keys [sources reads]} (fixture)
        second-name (name/from-string "Evidence.second")
        absent-name (name/from-string "Evidence.absent")
        sources (assoc sources :shell (fn [n]
                                        (swap! reads conj [:shell n])
                                        (cond (= n declaration-name) shell
                                              (= n second-name) (assoc shell :name n :all [n]))))
        result (evidence/materialize-partition [declaration-name absent-name second-name]
                                               sources limits storage/resolve-ci-shell)]
    (is (= #{declaration-name second-name} (set (keys (:constants result)))))
    (is (= [absent-name] (:absent result)))
    (is (= 3 (get-in result [:usage :declarations])))
    (is (= 2 (get-in result [:usage :expr-nodes])))
    (is (= 1 (count (filter #{[:expr 0]} @reads))))
    (is (= 1 (count (filter #{[:expr 1]} @reads))))))

(deftest partition-admits-all-requested-names-before-any-shell-read
  (let [{:keys [sources reads]} (fixture)
        absent-name (name/from-string "Evidence.absent")]
    (is (thrown? clojure.lang.ExceptionInfo
                 (evidence/materialize-partition [declaration-name absent-name] sources
                                                 (assoc limits :name-chars 1) storage/resolve-ci-shell)))
    (is (empty? @reads))
    (is (thrown? clojure.lang.ExceptionInfo
                 (evidence/materialize-partition [declaration-name absent-name] sources
                                                 (assoc limits :declarations 1) storage/resolve-ci-shell)))
    (is (empty? @reads))
    (is (thrown? clojure.lang.ExceptionInfo
                 (evidence/materialize-partition [absent-name] (assoc sources :shell (constantly {}))
                                                 limits storage/resolve-ci-shell)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (evidence/materialize [absent-name] sources limits storage/resolve-ci-shell)))))

(deftest captured-partition-uses-original-roots-without-normal-hydration
  (with-captured-branch
    {:value-policy :defs-only}
    (fn [^Env loaded head reads]
      (reset! head {:env-root :replacement})
      (let [absent-name (name/from-string "Evidence.absent")
            result (storage/full-ci-evidence-partition loaded [absent-name declaration-name] limits)]
        (is (= [absent-name] (:absent result)))
        (is (constant-info/complete? (get (:constants result) declaration-name)))
        (is (= [[:branches "main"]] @reads))
        (is (nil? (.value ^ConstantInfo (.lookup loaded declaration-name)))
            "ordinary defs-only cache never receives the evidence proof")))))

(deftest partition-refuses-local-hidden-and-unsupported-external-views
  (let [absent-name (name/from-string "Evidence.absent")
        pure (Env.)
        result (storage/full-ci-evidence-partition pure [absent-name] limits)
        looked-up? (atom false)
        unknown (.withExternalLookup pure (fn [_] (reset! looked-up? true) nil) 0)
        local (.addConstant pure (ConstantInfo/mkAxiom absent-name (object-array [])
                                                       (Expr/sort Level/ZERO_LEVEL false) false))]
    (is (= [absent-name] (:absent result)))
    (is (= {} (:constants result)))
    (is (thrown? clojure.lang.ExceptionInfo (storage/full-ci-evidence-partition unknown [absent-name] limits)))
    (is (false? @looked-up?))
    (is (thrown? clojure.lang.ExceptionInfo (storage/full-ci-evidence-partition local [absent-name] limits))))
  (with-captured-branch
    {:visible? (constantly false)}
    (fn [loaded _ _]
      (is (thrown? clojure.lang.ExceptionInfo
                   (storage/full-ci-evidence-partition loaded [(name/from-string "absent")] limits))))))
