(ns java-ir-int-checks
  "Original signed Int family: exact arithmetic, boxed owning boundaries and forks."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-int-runtime/original-rows.json")
(defn originals [] (json/read-str (slurp fixture)))
(defn rows [] (mapv #(get % "row") (originals)))
(defn context [] (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(into (rows) (x/raw [(second g/common)]))])))
(defn call [ctx engine name args] (j/call ctx engine (str "Int." name "._boxed") args))
(def huge (.shiftLeft java.math.BigInteger/ONE 100))
(def values [(.negate huge) Long/MIN_VALUE -1 0 1 Long/MAX_VALUE huge])
(def borrowed #{"Int.neg" "Int.natAbs" "Int.add" "Int.sub" "Int.decEq" "Int.decLt" "Int.decLe"})

(deftest original-source-rows-and-exact-abis
  (let [manifest (edn/read-string (slurp "test/fixtures/java-int-runtime/provenance.edn"))]
    (is (= 18 (count (originals))))
    (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
    (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (:lean-commit manifest)))
    (doseq [r (originals) :when (get-in r ["row" "ir" "extern"])]
      (is (string? (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                                              (into-array Class [java.util.Map])) [(get r "row")]))))))

(deftest signed-arithmetic-and-order-across-long-overflow-and-large-integers
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [a values b values :let [a* (biginteger a) b* (biginteger b)]]
        (is (= (.add a* b*) (biginteger (call ctx engine "add" [a b]))))
        (is (= (.subtract a* b*) (biginteger (call ctx engine "sub" [a b]))))
        (is (= (if (= a* b*) 1 0) (call ctx engine "decEq" [a b])))
        (is (= (if (neg? (.compareTo a* b*)) 1 0) (call ctx engine "decLt" [a b])))
        (is (= (if (pos? (.compareTo a* b*)) 0 1) (call ctx engine "decLe" [a b]))))
      (is (instance? java.math.BigInteger (call ctx engine "add" [Long/MAX_VALUE 1])))
      (is (instance? java.math.BigInteger (call ctx engine "sub" [Long/MIN_VALUE 1])))
      (is (instance? Long (call ctx engine "add" [huge (.negate huge)])))
      (finally (j/close! ctx engine)))))

(deftest unary-and-owned-nat-conversions-preserve-mathematical-values
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [a values :let [a* (biginteger a)]]
        (is (= (.negate a*) (biginteger (call ctx engine "neg" [a]))))
        (is (= (.abs a*) (biginteger (call ctx engine "natAbs" [a])))))
      (doseq [a [0 1 Long/MAX_VALUE huge]]
        (is (= (biginteger a) (biginteger (call ctx engine "ofNat" [a]))))
        (is (= (.negate (.add (biginteger a) java.math.BigInteger/ONE))
               (biginteger (call ctx engine "negSucc" [a])))))
      (is (= Long/MIN_VALUE (call ctx engine "negSucc" [Long/MAX_VALUE])))
      (is (= "9223372036854775808" (str (call ctx engine "neg" [Long/MIN_VALUE]))))
      (finally (j/close! ctx engine)))))

(deftest borrowed-raw-roots-closures-and-paps-require-owning-wrappers
  (let [ctx (context)]
    (doseq [label borrowed]
      (let [engine (j/machine ctx)
            target (get (first (filter #(= label (get % "label")) (originals))) "row")
            pap (c/decl "bad-pap" [] "object"
                  (c/let-ir 1 "object" {:pap {:c (get target "name") :ys []}} (c/ret 1)))]
        (try
          (is (re-find #"Borrowed Int primitive" (c/failure #(j/call ctx engine label []))))
          (is (re-find #"Borrowed Int primitive" (c/failure #(j/make-closure! ctx engine label []))))
          (is (re-find #"Borrowed Int primitive"
                       (c/failure #(j/invoke-static (:prepare *basis*) [(into (rows) (x/raw [pap]))]))))
          (finally (j/close! ctx engine)))))))

(deftest boxed-partial-application-and-signed-prepared-graph-fork
  (let [ctx (context) engine (j/machine ctx)
        closure (j/make-closure! ctx engine "Int.add._boxed" [-4])
        source (j/source-binding ctx (Object.))
        [negative] (j/install-graph! ctx engine
                     (j/selected-owner-graph ctx source (Object.) [] [] []
                       [(j/graph-int ctx (.negate huge))]))
        child (j/fork! ctx engine [negative closure]) child-engine (:engine child)]
    (try
      (is (= (.negate huge) negative))
      (is (= negative (first (:roots child))))
      (is (= 3 (j/call ctx engine "apply" [closure 7])))
      (is (= -11 (j/call ctx child-engine "apply" [(second (:roots child)) -7])))
      (is (= huge (call ctx engine "neg" [negative])))
      (is (= huge (call ctx child-engine "natAbs" [(first (:roots child))])))
      (finally (j/close! ctx engine) (j/close! ctx child-engine)))))

(deftest invalid-nat-and-nonnumeric-int-inputs-reject
  (doseq [[label value] [["ofNat" -1] ["negSucc" (.negate huge)] ["neg" "bad"] ["add" "bad"]]]
    (let [ctx (context) engine (j/machine ctx)]
      (is (not= "NO ERROR" (c/failure #(call ctx engine label (if (= label "add") [value 0] [value])))))
      (if (:explicit ctx) (is (g/bad? #(j/close! ctx engine))) (j/close! ctx engine)))))
(deftest imported-borrowed-closures-reject-before-graph-publication
  (doseq [record (originals) :when (contains? borrowed (get record "label"))]
    (let [base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
          h (j/declaration-header source (get record "row") (get record "sha256"))
          ctx (j/register-headers base [h]) engine (j/machine ctx)]
      (try
        (is (re-find #"Borrowed Int primitive|Prepared closure requires boxed result"
                     (c/failure #(j/install-graph! ctx engine
                       (j/prepared-graph ctx source (Object.)
                         [(j/graph-node ctx {:kind :closure :id 1 :target h :fields []})]
                         [] [] [(j/graph-ref ctx 1)])))))
        (is (false? (host/private-value engine "graphInstalled")))
        (is (= [] (j/install-graph! ctx engine (j/prepared-graph ctx source (Object.) [] [] [] []))))
        (finally (j/close! ctx engine))))))

(deftest invalid-owned-node-operands-are-validated-before-consumption
  (doseq [label ["neg" "natAbs" "add" "ofNat" "negSucc"]]
    (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))
          [node] (j/install-graph! ctx engine
                   (j/selected-owner-graph ctx source (Object.)
                     [(j/graph-node ctx {:kind :ctor :id 1 :rc 99 :tag 0 :fields [0]})]
                     [] [] [(j/graph-ref ctx 1)]))]
      (is (not= "NO ERROR" (c/failure #(call ctx engine label (if (= label "add") [node 0] [node])))))
      (is (= 1 (c/rc ctx node))) (is (false? (host/private-value node "dead")))
      (if (:explicit ctx) (is (g/bad? #(j/close! ctx engine)))
          (do (j/release! ctx engine node) (j/close! ctx engine))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-int-checks)))
