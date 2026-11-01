(ns original-runtime-limits-provider-checks-v1
  "Pure source/descriptor models only; no actual HostRequest execution."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.java.io :as io]
            [original-runtime-limits-provider-v1 :as provider]
            [ansatz.research.ir.source-setup :as source]))
(def directory (io/file (.getParentFile (io/file *file*)) "../data/limits"))
(defn- entries []
  (into {} (for [[_ spec] provider/specifications]
             [(:name spec) {:row (json/read-str (slurp (io/file directory (str (last (:name spec)) ".json")))) :sha256 (:sha spec)}])))
(defn- reject? [f] (try (f) false (catch Exception _ true)))
(deftest two-fixed-supported-target-values
  (is (= Long/MAX_VALUE (get-in provider/specifications ["lean_max_small_nat" :value])))
  (is (= 16 (get-in provider/specifications ["lean_closure_max_args" :value])))
  (is (every? #(instance? Long (:value %)) (vals provider/specifications)))
  (doseq [symbol [nil "unknown" "lean_libuv_version" "lean_io_get_num_heartbeats"]]
    (is (false? (provider/handles? symbol)))))
(deftest early-descriptors-authenticate-both-exact-source-rows
  (let [receipt (Object.) rows (entries) seen (atom [])]
    (with-redefs [source/lookup-entry (fn [actual name] (is (identical? receipt actual)) (swap! seen conj name) (get rows name))]
      (is (= [{:symbol "lean_max_small_nat" :parameters ["tagged"] :borrowed [false] :result "tobject"}
              {:symbol "lean_closure_max_args" :parameters ["tagged"] :borrowed [false] :result "tobject"}]
             (provider/early-specifications! receipt)))
      (is (= 2 (count @seen))))))
(deftest changed-original-abi-digest-or-runtime-never-produces-specification
  (let [name (get-in provider/specifications ["lean_max_small_nat" :name]) rows (entries)]
    (doseq [change [#(assoc % :sha256 (apply str (repeat 64 "0")))
                   #(assoc-in % [:row "ir" "extern" "xs" 0 "borrow"] true)
                   #(assoc-in % [:row "ir" "extern" "xs" 0 "ty"] "void")
                   #(assoc-in % [:row "runtime" "initializer"] true)
                   #(assoc-in % [:row "redirect"] ["str" ["anonymous"] "fake"])]]
      (with-redefs [source/lookup-entry (fn [_ n] (if (= name n) (change (get rows n)) (get rows n)))]
        (is (reject? #(provider/early-specifications! (Object.))))))))
(defn check! [] (run-tests 'original-runtime-limits-provider-checks-v1))
