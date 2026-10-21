(ns ansatz.export.non-safe-replay-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [ansatz.export.non-safe :as non-safe]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as expr]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel ConstantInfo ExprStore]
           [java.security MessageDigest]))

;; Explicit admission models exercise the kernel, not a native compiler capture.
(defn- nm [s] (name/from-string s))
(defn- c [s] (expr/const' (nm s) []))
(def ^:private A (c "A"))
(def ^:private type0 (expr/sort' (level/succ level/zero)))
(defn- axiom [s] (env/mk-axiom (nm s) [] A))
(defn- foundation [] [(env/mk-axiom (nm "A") [] type0)])
(defn- definition [s value safety & options]
  (apply env/mk-def (nm s) [] A value :safety safety options))
(defn- ignore-argument [result argument]
  (expr/app (expr/lam (nm "ignored") A result :default) argument))
(defn- stream-model [declarations]
  (with-redefs [parser/parse-ndjson-file-streaming
                (fn [_ initial step]
                  {:final-state (reduce step initial declarations) :parser-meta {:fixture :model}})]
    (replay/replay-file-streaming "non-safe-SCC-model")))
(defn- both [declarations]
  [(replay/replay declarations) (stream-model declarations)])
(defn- assert-all-ok [declarations result]
  (is (zero? (get-in result [:stats :errors])))
  (is (= (count declarations) (get-in result [:stats :ok])))
  (is (= (count declarations) (get-in result [:stats :total])))
  (doseq [^ConstantInfo ci declarations]
    (is (some? (env/lookup (:env result) (.name ci))))))

(deftest single-self-and-misleading-all
  (doseq [safety [:unsafe :partial]]
    (let [declarations (into (foundation)
                             [(axiom "seed")
                              (definition "plain" (c "seed") safety :all [(nm "not-exported")])
                              (definition "self" (c "self") safety :all [(nm "phantom") (nm "other")])])]
      (doseq [result (both declarations)] (assert-all-ok declarations result))
      (let [base (:env (replay/replay (foundation)))
            [loaded result] (replay/replay-one base (last declarations))]
        (is (= :ok (:status result)))
        (is (some? (env/lookup loaded (nm "self"))))))))

(deftest mutual-body-references-determine-group
  (doseq [safety [:unsafe :partial]]
    (let [declarations (into (foundation)
                             [(definition "g" (c "f") safety :all [(nm "g")])
                              (definition "f" (c "g") safety :all [(nm "unrelated")])])]
      (doseq [result (both declarations)] (assert-all-ok declarations result))
      (let [result (replay/replay declarations)]
        (is (= (mapv #(str (.name ^ConstantInfo %)) declarations)
               (mapv :name (:results result))))))))

(deftest external-dependencies-may-separate-scc-members
  (doseq [safety [:unsafe :partial]]
    (let [declarations (into (foundation)
                             [(definition "g" (c "f") safety)
                              (axiom "external")
                              (definition "f" (ignore-argument (c "g") (c "external")) safety)])]
      (doseq [result (both declarations)] (assert-all-ok declarations result)))))

(deftest nested-external-scc-closes-before-parent
  (doseq [safety [:unsafe :partial]]
    (let [declarations (into (foundation)
                             [(definition "g" (c "f") safety)
                              (definition "innerB" (c "innerA") safety)
                              (definition "innerA" (c "innerB") safety)
                              (definition "f" (ignore-argument (c "g") (c "innerA")) safety)])]
      (doseq [result (both declarations)] (assert-all-ok declarations result)))))

(deftest group-failures-are-atomic-and-fully-counted
  (let [bad-groups [[(definition "f" (c "g") :unsafe)
                     (definition "g" (c "f") :partial)]
                    [(env/mk-def (nm "f") [] (c "g") (c "g") :safety :unsafe)
                     (env/mk-def (nm "g") [] (c "f") (c "f") :safety :unsafe)]
                    [(env/mk-def (nm "f") [(nm "u")] A (c "g") :safety :unsafe)
                     (env/mk-def (nm "g") [(nm "v")] A (c "f") :safety :unsafe)]
                    [(definition "f" (c "g") :unsafe)
                     (definition "g" (ignore-argument (c "f") type0) :unsafe)]]]
    (doseq [group bad-groups]
      (let [declarations (into (foundation) group)]
        (doseq [result (both declarations)]
          (is (pos? (get-in result [:stats :errors])))
          (is (= (count declarations) (get-in result [:stats :total])))
          (doseq [^ConstantInfo ci group]
            (is (nil? (env/lookup (:env result) (.name ci))))))))))

(deftest missing-and-out-of-order-dependencies-never-disappear
  (doseq [declarations [(into (foundation) [(definition "f" (c "missing") :unsafe)])
                        ;; Explicitly reject non-native order rather than scheduling or
                        ;; quietly retrying the definition after its dependency appears.
                        (into (foundation) [(definition "f" (c "later") :unsafe) (axiom "later")])]]
    (doseq [result (both declarations)]
      (is (= 1 (get-in result [:stats :errors])))
      (is (= (count declarations) (get-in result [:stats :total])))
      (is (nil? (env/lookup (:env result) (nm "f"))))))
  (let [declarations (into (foundation) [(definition "f" (c "missing") :unsafe)])]
    (is (thrown-with-msg? Exception #"Replay stopped"
                          (replay/replay declarations :stop-on-error? true)))))

(deftest safe-proofs-cannot-use-admitted-non-safe-definitions
  (doseq [safety [:unsafe :partial]]
    (let [P (c "P")
          declarations [(env/mk-axiom (nm "P") [] (expr/sort' level/zero))
                        (env/mk-def (nm "loop") [] P (c "loop") :safety safety)
                        (env/mk-thm (nm "badProof") [] P (c "loop"))]]
      (doseq [result (both declarations)]
        (is (= 2 (get-in result [:stats :ok])))
        (is (= 1 (get-in result [:stats :errors])))
        (is (nil? (env/lookup (:env result) (nm "badProof"))))))))

(deftest trust-mode-retains-unchecked-input-admission
  (let [declarations (into (foundation) [(definition "f" (c "missing") :unsafe)
                                         (definition "g" (c "not-present") :partial)])
        result (replay/replay declarations :verify? false)]
    (assert-all-ok declarations result)))

(deftest replay-from-env-preserves-checked-prefix
  (let [prefix (:env (replay/replay (foundation)))
        ci (definition "self" (c "self") :partial)
        result (replay/replay-from-env prefix [ci])]
    (assert-all-ok [ci] result)
    (is (identical? (env/lookup prefix (nm "A")) (env/lookup (:env result) (nm "A"))))
    (is (nil? (env/lookup prefix (nm "self"))))))

(deftest dependency-walker-retains-projection-and-literal-types
  (is (contains? (non-safe/expression-dependencies (expr/proj (nm "Record") 0 A)) (nm "Record")))
  (is (contains? (non-safe/expression-dependencies (expr/lit-nat 0)) (nm "Nat")))
  (is (contains? (non-safe/expression-dependencies (expr/lit-str "x")) (nm "String"))))

(defn- captured-quotients []
  (let [state (parser/parse-ndjson-string
               (slurp (io/resource "ansatz/export/fixtures/quotient-4.29.ndjson") :encoding "UTF-8"))]
    (try (:decls state) (finally (.close ^ExprStore (:exprs state))))))

(deftest streamed-tail-retains-pending-quotient-package
  (let [capture (captured-quotients)
        prefix (filterv #(not (.isQuot ^ConstantInfo %)) capture)
        qs (filterv #(.isQuot ^ConstantInfo %) capture)
        declarations (into (into prefix (foundation))
                           (concat [(first qs) (definition "loop" (c "loop") :unsafe)] (rest qs)))
        result (stream-model declarations)]
    (assert-all-ok declarations result)
    (is (env/quot-enabled? (:env result))))
  (let [capture (captured-quotients)
        declarations (into (into capture (foundation))
                           [(definition "loop" (c "loop") :unsafe) (last capture)])
        result (stream-model declarations)]
    (is (= 1 (get-in result [:stats :errors])))
    (is (= (count declarations) (get-in result [:stats :total])))))

(deftest malformed-pending-quotient-keeps-stream-error-counts
  (let [capture (captured-quotients)
        prefix (filterv #(not (.isQuot ^ConstantInfo %)) capture)
        q (first (filter #(.isQuot ^ConstantInfo %) capture))
        declarations (into (into prefix (foundation))
                           [q (definition "loop" (c "loop") :unsafe)])
        result (stream-model declarations)]
    (is (= 1 (get-in result [:stats :errors])))
    (is (= (count declarations) (get-in result [:stats :total])))
    (is (not (env/quot-enabled? (:env result))))
    (is (some? (env/lookup (:env result) (nm "loop"))))))

(deftest invalid-safety-is-not-an-additional-recursive-authority
  (let [^ConstantInfo ci (definition "loop" (c "loop") :unsafe)
        _ (set! (.safety ci) (byte 3))
        declarations (into (foundation) [ci])]
    (is (thrown-with-msg? Exception #"Invalid definition safety"
                          (replay/replay declarations)))
    (is (thrown-with-msg? Exception #"Invalid definition safety"
                          (stream-model declarations)))))

(deftest failed-prefix-quotient-package-cannot-be-retried-through-non-safe-tail
  (let [capture (captured-quotients)
        prefix (filterv #(not (.isQuot ^ConstantInfo %)) capture)
        qs (filterv #(.isQuot ^ConstantInfo %) capture)
        ;; Four records trigger prefix admission, but duplicate the first
        ;; primitive instead of providing the fourth. The failed attempt still
        ;; consumes the stream's single quotient-package opportunity.
        malformed (conj (vec (take 3 qs)) (first qs))
        declarations (into (into prefix (foundation))
                           (concat malformed [(definition "loop" (c "loop") :unsafe)] qs))
        result (stream-model declarations)]
    (is (= 8 (get-in result [:stats :errors])))
    (is (= (count declarations) (get-in result [:stats :total])))
    (is (not (env/quot-enabled? (:env result))))
    (is (some? (env/lookup (:env result) (nm "loop"))))
    (doseq [^ConstantInfo ci qs]
      (is (nil? (env/lookup (:env result) (.name ci)))))))

(defn- resource-bytes [resource]
  (with-open [input (io/input-stream (io/resource resource))] (.readAllBytes input)))
(defn- sha256 [bytes]
  (apply str (map #(format "%02x" (bit-and 255 %))
                  (.digest (MessageDigest/getInstance "SHA-256") ^bytes bytes))))

(deftest native-4-33-kernel-scc-capture-replays-with-safe-proof-boundary
  ;; Actual checked native kernel API capture; not a hand-built positive CI model
  ;; and not a claim about surface partial-def compiler companion generation.
  (let [provenance (json/read-str
                    (slurp (io/resource "ansatz/export/fixtures/non-safe-native-4.33.provenance.json")
                           :encoding "UTF-8") :key-fn keyword)
        bytes (resource-bytes (get-in provenance [:capture :resource]))
        source (resource-bytes (get-in provenance [:source :resource]))
        parsed (parser/parse-ndjson-string (String. ^bytes bytes "UTF-8"))]
    (try
      (is (= "ansatz-native-non-safe-scc/1" (:profile provenance)))
      (is (= {:version "4.33.1" :githash "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"} (:lean provenance)))
      (is (= (:lean provenance) (get-in (json/read-str (first (str/split-lines
                                                               (String. ^bytes bytes "UTF-8")))
                                                       :key-fn keyword) [:meta :lean])))
      (is (= "f418258c793b7a57da7484e6b68c83d519a3e0607b5cd1faa743677f16aab3a0" (sha256 bytes)
             (get-in provenance [:capture :sha256])))
      (is (= (sha256 source) (get-in provenance [:source :sha256])))
      (is (= 2 (get-in provenance [:native-checks :rejection-count])))
      (let [declarations (:decls parsed)
            expected ["NativeNonSafeSCC.P" "NativeNonSafeSCC.unsafeRight" "NativeNonSafeSCC.unsafeLeft"
                      "NativeNonSafeSCC.partialRight" "NativeNonSafeSCC.partialLeft"]
            vector-result (replay/replay declarations)
            stream-result (replay/replay-file-streaming
                           (io/resource (get-in provenance [:capture :resource])))]
        (is (= expected (mapv #(str (.name ^ConstantInfo %)) declarations)))
        (is (= [1 1 2 2] (mapv #(int (.safety ^ConstantInfo %)) (rest declarations))))
        (doseq [result [vector-result stream-result]]
          (assert-all-ok declarations result)
          (doseq [label ["unsafeLeft" "partialLeft"]]
            (let [proof-name (str "NativeNonSafeSCC." label ".invalidSafeProof")
                  proof (env/mk-thm (nm proof-name) [] (c "NativeNonSafeSCC.P")
                                    (c (str "NativeNonSafeSCC." label)))
                  [checked outcome] (replay/replay-one (:env result) proof)]
              (is (= :error (:status outcome)))
              (is (identical? (:env result) checked))
              (is (nil? (env/lookup checked (nm proof-name))))))))
      (finally (.close ^ExprStore (:exprs parsed))))))
