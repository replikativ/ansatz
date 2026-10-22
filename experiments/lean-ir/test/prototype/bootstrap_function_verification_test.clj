(ns prototype.bootstrap-function-verification-test
  "Streaming archive function authentication: no whole-world restore claim."
  (:require [clojure.test :refer [deftest is]]
            [prototype.bootstrap-archive :as archive]
            [prototype.bootstrap-archive-test :as fixture]
            [prototype.checkpoint-wire :as wire]))

(defn verify-rows
  ([rows] (verify-rows rows (fn [name function] [name function])))
  ([rows verify]
   (let [file (fixture/path) text (fixture/text rows)]
     (try
       (spit file text)
       (archive/verify-function-rows file (assoc (fixture/options (fixture/sha text)) :verify-function verify))
       (finally (.delete file))))))
(defn function-rows []
  (let [rows (fixture/minimal-rows) function {:params [1] :body [:return [:var 1]]}
        header (assoc-in (second (first rows)) [:counts :functions] 1)]
    [[:header header] [:function ["f"] function] (second rows) [:end (:counts header)]]))

(deftest streamed-function-proof-reuses-exact-caller-canonical-entries
  (let [file (fixture/path) original (fixture/world)
        original-function (get-in original [:functions ["f"]])
        canonical-name [(String. "f")]
        canonical-function (with-meta (into {} original-function) (meta original-function))
        calls (atom [])]
    (try
      (let [written (archive/write! file original fixture/header)
            result (archive/verify-function-rows file
                     (assoc (fixture/options (:sha256 written)) :verify-function
                       (fn [name function]
                         ;; archive/worker is a raw Thread; report assertions
                         ;; only on the parent test thread, not inside callback.
                         (swap! calls conj {:name name :same-data? (wire/same-data? original-function function)})
                         [canonical-name canonical-function])))]
        (is (= [{:name ["f"] :same-data? true}] @calls))
        (is (identical? canonical-name (first (keys (:functions result)))))
        (is (identical? canonical-function (get-in result [:functions ["f"]])))
        (is (= (:header written) (:header result)))
        (is (= (:next-id original) (:next-id result)))
        (is (= (:sha256 written) (:sha256 result)))
        (is (= (.length file) (:bytes result)))
        (is (= #{:functions :header :next-id :sha256 :bytes} (set (keys result))))
        (is (not (contains? result :world))))
      (finally (.delete file)))))

(deftest explicit-digest-commit-and-trusted-callback-are-required
  (doseq [options [{} {:expected-sha256 "bad"} (fixture/options (apply str (repeat 64 "a")))
                   (assoc (fixture/options (apply str (repeat 64 "a"))) :verify-function :not-a-function)
                   (assoc (fixture/options (apply str (repeat 64 "a"))) :verify-function vector :expected-lean-commit "wrong")]]
    ;; Invalid authority is rejected before opening a nonexistent archive.
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"explicit pinned authority"
          (archive/verify-function-rows "/nonexistent/ansatz-archive-test" options)))))

(deftest callback-may-run-before-final-digest-but-no-result-is-issued
  (let [file (fixture/path) rows (function-rows) text (fixture/text rows) calls (atom 0)]
    (try
      (spit file text)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"SHA256 mismatch"
            (archive/verify-function-rows file
              (assoc (fixture/options (apply str (repeat 64 "0"))) :verify-function
                (fn [name function] (swap! calls inc) [name function])))))
      (is (= 1 @calls))
      (finally (.delete file)))))

(deftest canonical-callback-results-and-failures-are-checked
  (doseq [result [(list ["f"] {:params [] :body [:return [:imm 0]]}) [] [["f"]]
                  [["f"] {} :extra] [["wrong"] {:params [] :body [:return [:imm 0]]}]
                  [["f"] nil] [["f"] {:params '() :body []}] [["f"] {:params [] :body '()}]]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"invalid canonical entry"
          (verify-rows (function-rows) (fn [& _] result)))))
  (let [cause (ex-info "Comparison rejected" {})]
    (is (identical? cause
          (try (verify-rows (function-rows) (fn [& _] (throw cause))) nil
            (catch Throwable caught caught))))))

(deftest table-structure-counts-state-trailer-and-provenance-are-checked
  (let [rows (function-rows) h (second (first rows)) state (nth rows 2)]
    (doseq [changed [(pop rows) (conj rows [:extra]) (assoc-in rows [3 1 :functions] 0)
                     (assoc-in rows [0 1 :counts :functions] 2)
                     [[:header h] (nth rows 1) [:state {}] (last rows)]
                     [[:header h] (nth rows 1) state state (last rows)]
                     [[:header h] state (nth rows 1) (last rows)]
                     [[:header h] [:unknown] state (last rows)]
                     (assoc-in rows [0 1 :lean-commit] "wrong")
                     (assoc-in rows [0 1 :lean-version] "other")
                     (assoc-in rows [0 1 :format] "other")]]
      (is (thrown? Exception (verify-rows changed))))
    (doseq [[kind key value counter] [[:function ["f"] {:params [] :body [:return [:imm 0]]} :functions]
                                    [:heap 0 {:kind :ctor :fields [] :rc 1} :heap]
                                    [:global ["g"] {:status :ready :value 0} :globals]]]
      (let [header (assoc (second (first (fixture/minimal-rows))) :counts {:functions 0 :heap 0 :globals 0})
            header (assoc-in header [:counts counter] 2)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Duplicate"
              (verify-rows [[:header header] [kind key value] [kind key value] state [:end (:counts header)]])))))))

(deftest unknown-tags-and-reader-evaluation-never-run
  (doseq [form ["#=(throw (Exception.))" "#unknown {}" "#inst \"2020-01-01\""
                "#prototype.machine.Ref []"]]
    (let [file (fixture/path) text (str (pr-str (first (fixture/minimal-rows))) "\n" form "\n")]
      (try
        (spit file text)
        (is (thrown? Exception
              (archive/verify-function-rows file
                (assoc (fixture/options (fixture/sha text)) :verify-function vector))))
        (finally (.delete file))))))

(deftest skipped-heap-and-global-values-are-not-a-second-world-proof
  ;; The pinned bytes and record structure are authenticated; this API neither
  ;; reconstructs these tables nor checks guest reference/ownership validity.
  (let [rows (fixture/minimal-rows)
        header (assoc (second (first rows)) :counts {:functions 0 :heap 1 :globals 1})
        calls (atom 0)
        result (verify-rows [[:header header] [:heap 0 {:deliberately :not-a-guest-node}]
                             [:global ["g"] {:value :not-a-global-entry}]
                             (second rows) [:end (:counts header)]]
                 (fn [& _] (swap! calls inc) (throw (AssertionError. "No function row expected"))))]
    (is (= 0 @calls))
    (is (= {} (:functions result)))
    (is (= 0 (:next-id result)))))
