(ns ansatz.export.quotient-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as expr]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.quotient :as quotient])
  (:import [ansatz.kernel ConstantInfo ExprStore]))

;; Dependency-closed Eq/Quot capture from the shipped Lean 4.29.0-rc2
;; init-medium export (original producer header retained). This is real kernel
;; input, not a model and not evidence of compatibility with newer frontends.
(def ^:private captured-ndjson
  (slurp (io/resource "ansatz/export/fixtures/quotient-4.29.ndjson") :encoding "UTF-8"))

(def ^:private captured-declarations
  (delay (let [state (parser/parse-ndjson-string captured-ndjson)]
           (try (:decls state)
                (finally (.close ^ExprStore (:exprs state)))))))

(defn- package [] (filterv #(.isQuot ^ConstantInfo %) @captured-declarations))
(defn- bootstrap [] (filterv #(not (.isQuot ^ConstantInfo %)) @captured-declarations))
(defn- checked-eq []
  (first (replay/replay-inductive-bundle (env/empty-env) (bootstrap))))
(defn- replace-primitive [ci {:keys [nm lps type kind]}]
  (env/mk-quot (or nm (.name ^ConstantInfo ci))
               (or lps (vec (.levelParams ^ConstantInfo ci)))
               (or type (.type ^ConstantInfo ci))
               (or kind (.quotKind ^ConstantInfo ci))))
(defn- stream-model [declarations]
  ;; Drive the real streaming replay state machine; only file parsing is replaced.
  (with-redefs [parser/parse-ndjson-file-streaming
                (fn [_ initial step]
                  {:final-state (reduce step initial declarations) :parser-meta nil})]
    (replay/replay-file-streaming "captured-declaration-model")))
(defn- alias-declaration []
  (let [^ConstantInfo q (first (package))]
    (env/mk-def (name/from-string "QuotAlias") (vec (.levelParams q)) (.type q)
                (expr/const' (.name q) (mapv level/param (.levelParams q))))))
(defn- interleaved []
  (let [[q mk lift ind] (package)]
    (into (bootstrap)
          [q (alias-declaration) mk
           (env/mk-axiom (name/from-string "Independent") [] (expr/sort' level/zero))
           lift ind])))

(deftest canonical-quotient-package-test
  (let [original (checked-eq)
        admitted (quotient/admit-package! original (reverse (package)))]
    (is (not (env/quot-enabled? original)))
    (is (env/quot-enabled? admitted))
    (doseq [ci (package)]
      (is (identical? ci (env/lookup admitted (.name ^ConstantInfo ci)))))
    (is (thrown-with-msg? Exception #"canonical checked Eq"
                          (quotient/admit-package! (env/empty-env) (package))))))

(deftest malformed-quotient-package-test
  (let [original (checked-eq)
        qs (package)
        ^ConstantInfo q (first qs)]
    (doseq [bad [(pop qs)
                 (conj qs q)
                 (assoc qs 1 q)
                 (assoc qs 0 (replace-primitive q {:nm (name/from-string "BogusQuot")}))
                 (assoc qs 0 (replace-primitive q {:kind :ind}))
                 (assoc qs 0 (replace-primitive q {:type (expr/sort' level/zero)}))
                 (assoc qs 0 (replace-primitive q {:lps []}))
                 ;; Fail after earlier primitives have passed: no partial Env leaks.
                 (assoc qs 3 (replace-primitive (nth qs 3) {:type (expr/sort' level/zero)}))]]
      (is (thrown? Exception (quotient/admit-package! original bad)))
      (is (not (env/quot-enabled? original)))
      (is (nil? (env/lookup original (.name q)))))
    (let [[unchanged result] (replay/replay-one original q)]
      (is (identical? original unchanged))
      (is (= :error (:status result))))
    (let [[trusted result] (replay/replay-one original q false)]
      (is (= :ok (:status result)))
      (is (env/quot-enabled? trusted)))))

(deftest noncanonical-equality-bootstrap-test
  (let [fake (env/mk-axiom (name/from-string "Eq") [] (expr/sort' level/zero))
        unchecked (.addConstant (env/empty-env) fake)]
    (is (thrown-with-msg? Exception #"canonical checked Eq"
                          (quotient/admit-package! unchecked (package))))))

(deftest vector-and-stream-noncontiguous-quotients-test
  (doseq [result [(replay/replay (interleaved) :stop-on-error? true)
                  (stream-model (interleaved))]]
    (is (zero? (get-in result [:stats :errors])))
    (is (= (count (interleaved)) (get-in result [:stats :total])))
    (is (env/quot-enabled? (:env result)))
    (is (some? (env/lookup (:env result) (name/from-string "QuotAlias"))))
    (is (some? (env/lookup (:env result) (name/from-string "Independent"))))))

(deftest truncated-and-invalid-replay-test
  (let [missing (into (bootstrap) (pop (package)))]
    (is (thrown-with-msg? Exception #"complete canonical"
                          (replay/replay missing :stop-on-error? true)))
    (let [result (stream-model missing)]
      (is (= 3 (get-in result [:stats :errors])))
      (is (= (count missing) (get-in result [:stats :total])))
      (is (not (env/quot-enabled? (:env result)))))
    (is (env/quot-enabled? (:env (replay/replay missing :verify? false)))))
  (let [qs (package)
        bad (assoc qs 3 (replace-primitive (nth qs 3) {:type (expr/sort' level/zero)}))
        declarations (into (bootstrap) bad)]
    (doseq [result [(replay/replay declarations) (stream-model declarations)]]
      (is (= 4 (get-in result [:stats :errors])))
      (is (= (count declarations) (get-in result [:stats :total])))
      (is (not (env/quot-enabled? (:env result)))))))

(deftest duplicate-stream-primitive-test
  (let [declarations (conj @captured-declarations (first (package)))
        result (stream-model declarations)]
    (is (= 1 (get-in result [:stats :errors])))
    (is (= (count declarations) (get-in result [:stats :total])))))

(deftest actual-stream-parser-quotient-test
  (let [file (java.io.File/createTempFile "ansatz-quotient-" ".ndjson")]
    (try
      (spit file captured-ndjson)
      (let [result (replay/replay-file-streaming (.getPath file) :verbose? true)]
        (is (= (count @captured-declarations) (get-in result [:stats :ok])))
        (is (zero? (get-in result [:stats :errors])))
        (is (env/quot-enabled? (:env result))))
      (finally (io/delete-file file true)))))

(deftest noncanonical-equality-type-test
  (let [[^ConstantInfo eq ^ConstantInfo refl] (bootstrap)
        bad-eq (env/mk-induct (.name eq) (vec (.levelParams eq)) (expr/sort' level/zero)
                              :ctors (vec (.ctors eq)))
        unchecked (-> (env/empty-env) (.addConstant bad-eq) (.addConstant refl))]
    (is (thrown-with-msg? Exception #"noncanonical Eq"
                          (quotient/admit-package! unchecked (package))))))
