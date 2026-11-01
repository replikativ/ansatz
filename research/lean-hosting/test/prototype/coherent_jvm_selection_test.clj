(ns prototype.coherent-jvm-selection-test
  "Pure demanded-fact controls using captured IR, without hosted loading or owners."
  (:require [clojure.test :refer [deftest is]]
            [prototype.coherent-jvm-selection :as selection]
            [prototype.typed-tail-test :as fixture]
            [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]))

(defn input []
  (let [rows (vec (rest (fixture/read-rows "boxed-scalar-wrapper-programs.jsonl")))
        declarations (into {} (map (juxt :name identity)) rows)
        root (first (filter #(= "sum64" (last %)) (keys declarations)))
        reads (atom [])
        actual {:world {:functions (into {} (map abi/lower) rows)
                        :eval-const-authorizations {:declarations {root (get declarations root)}}}}
        independent {:catalogue {:read-declaration (fn [name] (swap! reads conj name) (get declarations name))}}]
    {:rows declarations :root root :reads reads :actual actual :independent independent}))

(defn select-input [{:keys [actual independent root]}]
  (selection/select actual independent root selection/limits))

(deftest demand-only-selection-uses-admitted-worker-and-original-catalogue
  (let [{:keys [root reads rows actual independent] :as in} (input)
        result (select-input in)
        selected (get-in result [:compiler-options :typed-tail])]
    (is (= #{:compiler-options :region-key :source-key} (set (keys result))))
    (is (= #{root} (set (keys (:typed-functions selected)))))
    (is (= 3 (count (:descriptors selected))))
    (is (= (set (keys (:descriptors selected))) (set @reads)))
    (is (not (some #{root} @reads)))
    (is (= selection/profile (:profile selected)))
    (doseq [k [:source-key :region-key]] (is (re-matches #"[a-f0-9]{64}" (get result k))))
    ;; A competing image-derived catalogue must never replace original authority.
    (is (= result (selection/select (assoc actual :catalogue {:read-declaration (fn [_] (throw (AssertionError. "live catalogue scanned")))})
                                   independent root selection/limits)))))

(deftest authority-and-installed-code-mismatches-fail-before-selection
  (let [{:keys [root actual independent] :as in} (input)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not an admitted"
                         (select-input (assoc-in in [:actual :world :eval-const-authorizations :declarations] {}))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"executable code"
                         (selection/select (assoc-in actual [:world :functions root :body] [:return [:imm 9]]) independent root selection/limits)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (selection/select actual independent root (assoc selection/limits :max-work 200000))))))

(deftest missing-demanded-facts-and-work-exhaustion-refuse-explicitly
  (let [{:keys [root actual independent] :as in} (input)]
    (is (= :missing-demanded-row (:reason (selection/select actual {:catalogue {:read-declaration (constantly nil)}} root selection/limits))))
    (let [huge (assoc-in actual [:world :eval-const-authorizations :declarations root :ir :fdecl :info :extra]
                         (apply str (repeat 100001 "x")))]
      (is (= :work-budget (:reason (selection/select huge independent root selection/limits)))))
    (let [bad (assoc-in actual [:world :eval-const-authorizations :declarations root :ir :fdecl :info :owner] (Object.))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"plain immutable" (selection/select bad independent root selection/limits))))))

(deftest demanded-extern-abi-is-checked-without-describing-unrelated-symbols
  (let [{:keys [root actual independent rows] :as in} (input)
        demanded (first (keys (get-in (select-input in) [:compiler-options :typed-tail :descriptors])))
        original (get rows demanded)
        with-row (fn [row]
                   (assoc independent :catalogue {:read-declaration (fn [name] (if (= demanded name) row (get rows name)))}))]
    (is (= :redirected-extern
           (:reason (selection/select actual (with-row (assoc original :redirect {:name root})) root selection/limits))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (selection/select actual (with-row (assoc-in original [:ir :extern :xs 0 :borrow] true)) root selection/limits)))
    (is (= :unsupported-extern
           (:reason (selection/select actual
                                      (with-row (assoc-in original [:ir :extern :ext :entries 0 :standard :fn] "unknown_user_callback"))
                                      root selection/limits))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"executable code"
                         (selection/select (assoc-in actual [:world :functions demanded :body] [:return [:imm 99]]) independent root selection/limits)))))

(deftest actual-image-copy-shares-the-demanded-facts-work-budget
  (let [{:keys [root actual independent]} (input)]
    (is (= :work-budget
           (:reason (selection/select (assoc-in actual [:world :functions root :extra]
                                               (apply str (repeat 100001 "x")))
                                      independent root selection/limits))))
    (is (= :unsupported-installed-data
           (:reason (selection/select (assoc-in actual [:world :functions root :unexpected-owner] (Object.))
                                      independent root selection/limits))))))

(deftest producer-metadata-cannot-retain-an-owner-in-selection-data
  (let [{:keys [root actual independent] :as in} (input)
        owner (Object.)
        annotate (fn annotate [value]
                   (let [value (cond
                                 (map? value) (into {} (map (fn [[k v]] [(annotate k) (annotate v)])) value)
                                 (vector? value) (mapv annotate value)
                                 :else value)]
                     (if (instance? clojure.lang.IObj value) (with-meta value {:owner owner}) value)))
        marked-root (annotate root)
        row (annotate (get-in actual [:world :eval-const-authorizations :declarations root]))
        marked (assoc-in actual [:world :eval-const-authorizations :declarations] {marked-root row})
        result (selection/select marked independent marked-root selection/limits)
        plain? (fn plain? [value]
                 (and (not (identical? owner value)) (nil? (meta value))
                      (cond (map? value) (every? plain? (mapcat identity value))
                            (coll? value) (every? plain? value)
                            :else true)))]
    (is (= (select-input in) result))
    (is (plain? result))))
