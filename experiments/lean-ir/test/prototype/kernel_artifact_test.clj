(ns prototype.kernel-artifact-test
  "Bounded kernel DATA admission only. The fixture is provider pinned; no native
   Init release/frontend compatibility or artifact-backed guest anchor is claimed."
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [prototype.kernel-artifact :as artifact]
            [prototype.imported-kernel :as kernel]
            [prototype.checked-delta :as delta]
            [prototype.module-store :as store]
            [prototype.machine :as m]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as expr]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.env :as env])
  (:import [ansatz.kernel Env ConstantInfo TypeChecker]))

(def fixture-path "fixtures/imported-kernel-native.jsonl")
(def pinned-digest "e6d3e40d1d1c00a3a4cbe98eb8642d6be5321b16ed18c8fbcdbc69028606c2f3")
(defn with-admission [f]
  (let [loaded (artifact/load-admitted (m/world {}) artifact/native17-profile fixture-path)]
    (try (f loaded) (finally (.close ^java.io.Closeable (:source loaded))))))

(deftest pinned-admission-installs-complete-eager-kernel-data-without-verification-or-association
  (let [loader store/load-file options-seen (atom nil)
        loaded (with-redefs [store/load-file (fn [world path options]
                                              (reset! options-seen options)
                                              (loader world path options))
                            kernel/verify-constants (fn [& _] (throw (ex-info "Unexpected kernel verifier" {})))
                            kernel/verify-module-data (fn [& _] (throw (ex-info "Unexpected module verifier" {})))]
                 (artifact/load-admitted (m/world {}) artifact/native17-profile fixture-path))]
    (try
      (let [{:keys [world source admission roots]} loaded
            projection (artifact/inspect-for-world world admission)
            ^Env base (:env projection)]
        (is (= pinned-digest (:sha256 @options-seen) (:digest source)))
        (is (= :trusted-artifact (:basis projection)))
        (is (= artifact/native17-profile (:profile projection)))
        (is (= :trusted-artifact (get-in projection [:base-assumptions :basis])))
        (is (= #{"A"} (set (map str (get-in projection [:base-assumptions :axioms])))))
        (is (= #{"unsafeA"} (set (map str (get-in projection [:base-assumptions :unsafe])))))
        (is (= 17 (count (:constants projection)) (count (:projected projection))
               (count (get-in projection [:base-assumptions :declarations]))))
        (is (= 17 (count (.allConstants base))))
        (is (.sameExternalView base (Env.)))
        (is (.isQuotEnabled base))
        (is (= roots (:roots projection)))
        (is (identical? source (:source projection)))
        (is (= projection (artifact/inspect-for-world world admission)))
        (is (= #{} (set (keys (:heap world)))))
        (is (nil? (:kernel-environments world)))
        (is (not (contains? loaded :certificate)))
        (is (not (contains? projection :certificate)))
        (is (not (contains? projection :order)))
        (doseq [[n ci] (:projected projection)]
          (is (identical? ci (.lookup base n)))))
      (finally (.close ^java.io.Closeable (:source loaded))))))

(deftest profile-and-pin-authority-cannot-be-supplied-by-the-caller
  (let [calls (atom 0)]
    (with-redefs [store/load-file (fn [& _] (swap! calls inc) (throw (ex-info "Should not open" {})))]
      (doseq [id [:unknown {:profile artifact/native17-profile :sha256 pinned-digest}]]
        (is (thrown-with-msg? Exception #"Unsupported provider-owned"
              (artifact/load-admitted (m/world {}) id fixture-path))))
      (is (zero? @calls))))
  (is (thrown? clojure.lang.ArityException
        (apply artifact/load-admitted [(m/world {}) artifact/native17-profile fixture-path {:sha256 pinned-digest}]))))

(deftest changed-bytes-cannot-be-readmitted-with-a-caller-selected-hash
  (let [path (java.io.File/createTempFile "kernel-artifact-pin-" ".jsonl" (io/file "target"))]
    (try
      ;; A semantically identical, canonical JSONL file with different bytes.
      (spit path (str " " (slurp fixture-path)))
      (is (thrown-with-msg? Exception #"digest mismatch"
            (artifact/load-admitted (m/world {}) artifact/native17-profile (.getPath path))))
      (finally (io/delete-file path true)))))

(deftest only-issued-tokens-and-exact-live-attached-sources-can-be-inspected
  (with-admission
    (fn [{:keys [world admission source]}]
      (doseq [fake [{} {:basis :trusted-artifact :profile artifact/native17-profile}
                    (artifact/->Admission)]]
        (is (thrown-with-msg? Exception #"issued in-process"
              (artifact/inspect-for-world world fake))))
      (is (thrown-with-msg? Exception #"absent, duplicated, overlapping or shadowed"
            (artifact/inspect-for-world (assoc world :native-imports []) admission)))
      (is (thrown-with-msg? Exception #"absent, duplicated, overlapping or shadowed"
            (artifact/inspect-for-world (assoc world :native-imports [source source]) admission)))
      (is (thrown-with-msg? Exception #"absent, duplicated, overlapping or shadowed"
            (artifact/inspect-for-world
             (assoc-in world [:heap (:base source)] {:kind :ctor :tag 0 :fields [] :rc 1}) admission)))
      (.close ^java.io.Closeable source)
      (is (thrown-with-msg? Exception #"source is closed"
            (artifact/inspect-for-world world admission))))))

(deftest borrowed-java-constant-and-expression-containers-remain-guarded
  (with-admission
    (fn [{:keys [world admission]}]
      (let [projection (artifact/inspect-for-world world admission)
            ^ConstantInfo ci (get (:projected projection) (name/from-string "aliasA"))
            original (.value ci)]
        (try
          (set! (.value ci) (.type ci))
          (is (thrown-with-msg? Exception #"Inherited Java ConstantInfo checking shape changed"
                (artifact/inspect-for-world world admission)))
          (finally (set! (.value ci) original)))
        (is (= projection (artifact/inspect-for-world world admission))))
      (let [projection (artifact/inspect-for-world world admission)
            [levels _] (first (filter #(seq (second %))
                                     (:expression-arrays (delta/snapshot-projection projection))))]
        (is (some? levels))
        (let [original (aget ^objects levels 0)]
          (try
            (aset ^objects levels 0 (level/succ original))
            (is (thrown-with-msg? Exception #"Java expression universe array changed"
                  (artifact/inspect-for-world world admission)))
            (finally (aset ^objects levels 0 original))))))))

(deftest failures-close-only-the-newly-opened-store-and-preserve-the-original-cause
  (let [caller (store/load-file (m/world {}) fixture-path)
        loader store/load-file project kernel/module-constants owned (atom nil)]
    (try
      (let [cause (ex-info "injected artifact projection failure" {:sentinel :original})
            caught (with-redefs [store/load-file (fn [& args]
                                                  (let [loaded (apply loader args)]
                                                    (reset! owned (:source loaded)) loaded))
                                 kernel/module-constants (fn [& _] (throw cause))]
                     (try (artifact/load-admitted (:world caller) artifact/native17-profile fixture-path)
                          nil (catch Throwable error error)))]
        (is (identical? cause caught))
        (is (true? @(:closed @owned)))
        (is (false? @(:closed (:source caller)))))
      (doseq [alter [(fn [entries] (conj (vec entries) (first entries)))
                     (fn [entries] (vec (rest entries)))]]
        (let [caught (with-redefs [store/load-file (fn [& args]
                                                    (let [loaded (apply loader args)]
                                                      (reset! owned (:source loaded)) loaded))
                                   kernel/module-constants (fn [& args] (alter (apply project args)))]
                       (try (artifact/load-admitted (:world caller) artifact/native17-profile fixture-path)
                            nil (catch Throwable error error)))]
          (is (some? caught))
          (is (re-find #"Duplicate|exact provider-owned declaration inventory" (.getMessage caught)))
          (is (true? @(:closed @owned)))
          (is (false? @(:closed (:source caller))))))
      (finally (.close ^java.io.Closeable (:source caller))))))

(deftest a-new-declaration-can-be-kernel-checked-relative-to-the-explicitly-trusted-base
  (with-admission
    (fn [{:keys [world admission]}]
      (let [projection (artifact/inspect-for-world world admission)
            ^Env base (:env projection)
            ^ConstantInfo alias (.lookup base (name/from-string "aliasA"))
            n (name/from-string "artifactExtension")
            declaration (env/mk-def n [] (.type alias) (expr/const' (.name alias) []))
            ^Env extended (TypeChecker/checkConstant base declaration 20000000)]
        (is (= 18 (count (.allConstants extended))))
        (is (identical? declaration (.lookup extended n)))
        (is (nil? (.lookup base n)))
        (is (= 17 (count (.allConstants base))))
        (is (= :trusted-artifact (:basis (artifact/inspect-for-world world admission))))))))
