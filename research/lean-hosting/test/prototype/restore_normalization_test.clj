(ns prototype.restore-normalization-test
  (:require [clojure.test :refer [deftest is run-tests]]
            [prototype.restore-consumer :as restore]
            [prototype.restore-consumer-test :as parser]
            [prototype.checkpoint-wire :as wire]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]))

(defn normalize [rows]
  (let [{:keys [normalize! release!]} (#'restore/make-row-normalizer)]
    (try (mapv normalize! rows) (finally (release!)))))
(defn bytes= [a b] (java.util.Arrays/equals ^bytes (wire/encode a) ^bytes (wire/encode b)))
(def function-name ["str" ["anonymous"] "SharedAdd"])
(defn row [body] [:function function-name #{:prepared :imported} {:params [0 1] :body body}])

(deftest literal-metadata-and-extension-fields-are-not-operands
  (let [a (vector :var (long 0)) b (vector :var (long 0))
        literal (vector :var (long 0)) immediate (vector :var (long 0))
        debug (vector :var (long 0)) meta-leaf (with-meta b {:source 7})
        body [:let 2 [:literal literal]
              [:let 3 [:imm immediate]
               [:call 4 [:direct function-name] [a b meta-leaf [:var 0N] [:var -1] [:var 4096]]
                [:return a]]]]
        source [(with-meta (update (row body) 3 assoc :debug {:body debug}) {:body debug})]
        changed (normalize source) f (get-in changed [0 3]) cb (:body f)
        args (get-in cb [3 3 3])]
    (is (bytes= source changed))
    (is (identical? (first args) (second args)))
    (is (identical? literal (get-in cb [2 1])))
    (is (identical? immediate (get-in cb [3 2 1])))
    (is (identical? debug (get-in f [:debug :body])))
    (is (identical? debug (:body (meta (first changed)))))
    (is (identical? meta-leaf (nth args 2)))
    (is (instance? clojure.lang.BigInt (second (nth args 3))))
    (is (= [:var -1] (nth args 4))) (is (= [:var 4096] (nth args 5)))))

(deftest exact-scalar-and-name-metadata-roundtrip
  (doseq [name [(with-meta ["anonymous"] {:source :root})
                ["str" (with-meta ["anonymous"] {:source :prefix}) "x"]
                ["str" ["anonymous"] "λ😀"]]]
    (let [source [[:global name {:value (m/->Ref 300) :notes [-0.0 0.0 ##NaN 1N 1M 1/3]}]]]
      (is (bytes= source (normalize source))))))

(deftest independent-worlds-keep-three-backend-results
  (let [body [:let 2 [:prim :add [[:var 0] [:var 1]]] [:return [:var 2]]]
        original (get (row body) 3) shared (get-in (normalize [(row body)]) [0 3])]
    (doseq [backend [:reference :mutable :jvm]]
      (let [run (fn [f]
                  (let [functions {function-name f} world (m/world functions)
                        session (raw/open-functions functions {} {:backend backend :fuel 10000})
                        result (raw/call session world function-name [20 22])]
                    (is (nil? (:result world)))
                    (is (zero? (get-in world [:stats :steps]))) (:value result)))]
        (is (= 42 (run original) (run shared) (run original)))))))

(deftest parsed-registry-identities-and-separate-restore-scopes
  (let [counts (assoc parser/zero-counts :functions 2)
        body [:return [:var 0]]
        a ["str" ["anonymous"] "first"] b ["str" ["anonymous"] "second"]
        rows [[:header {:format restore/format-id :counts counts
                        :authority-present? true :authority-keys #{:functions}}]
              [:function a #{:prepared :imported} {:params [0] :body body}]
              [:function b #{:prepared :imported} {:params [0] :body body}]
              [:authority {}] [:state {}] [:end counts]]
        one (parser/parse-rows rows counts) two (parser/parse-rows rows counts)
        f (get-in one [:world :functions a])
        operand #(get-in % [:world :functions a :body 1])]
    ;; Parsing is not source/kernel authorization; it must preserve registry
    ;; identity for the later independent authorization checks.
    (is (identical? f (get-in one [:prepared-functions a])))
    (is (identical? f (get-in one [:world :eval-const-authorizations :functions a])))
    (is (identical? (operand one) (get-in one [:world :functions b :body 1])))
    (is (= (:world one) (:world two)))
    (is (not (identical? (operand one) (operand two))))))

(deftest name-strings-share-without-changing-name-shape-or-metadata
  (let [left (String. "same") right (String. "same")
        a ["str" ["str" ["anonymous"] "left"] left]
        b ["str" ["str" ["anonymous"] "right"] right]
        rows [[:global a {:value 1}] [:global b {:value 2}]]
        changed (normalize rows)]
    (is (not (identical? left right)))
    (is (identical? (get-in changed [0 1 2]) (get-in changed [1 1 2])))
    (is (= rows changed)) (is (bytes= rows changed))
    (is (every? vector? (map second changed)))))

(deftest operand-pool-range-types-and-false-code-contexts
  (doseq [operand [[:var -1] [:var 4096] [:var Long/MAX_VALUE] [:var 1N]
                   (with-meta [:var 1] {:origin :source})]]
    (let [source [(row [:return operand])] result (normalize source)]
      (is (bytes= source result))
      (is (identical? operand (get-in result [0 3 :body 1])))))
  (let [source [(row [:return [:var 4095]]) (row [:return [:var 4095]])]
        result (normalize source)]
    (is (identical? (get-in result [0 3 :body 1]) (get-in result [1 3 :body 1]))))
  (let [a (vector :var (long 0)) b (vector :var (long 0))
        rows [[:global ["anonymous"] {:value {:body [a b]}}]]
        result (normalize rows)]
    (is (identical? a (get-in result [0 2 :value :body 0])))
    (is (identical? b (get-in result [0 2 :value :body 1])))
    (is (not (identical? a b)))))

(deftest malformed-rows-and-direct-targets-are-not-code-contexts
  (let [a (vector :var (long 0)) b (vector :var (long 0))
        malformed (conj (row [:call 2 [:direct [a b]] [] [:return a]]) :extra)
        malformed-result (first (normalize [malformed]))
        ordinary-result (first (normalize [(pop malformed)]))]
    (is (bytes= malformed malformed-result))
    (is (identical? a (get-in malformed-result [3 :body 2 1 0])))
    (is (identical? b (get-in malformed-result [3 :body 2 1 1])))
    (is (identical? a (get-in ordinary-result [3 :body 2 1 0])))
    (is (identical? b (get-in ordinary-result [3 :body 2 1 1])))))
