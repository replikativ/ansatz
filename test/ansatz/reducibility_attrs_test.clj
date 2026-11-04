(ns ansatz.reducibility-attrs-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [ansatz.core :as a]
            [ansatz.attrs :as attrs]
            [ansatz.bundle-metadata :as metadata]
            [ansatz.meta :as meta]
            [ansatz.export.storage :as storage]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.name :as name])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(use-fixtures :once (fn [f] (a/load-init!) (binding [a/*verbose* false] (f))))

(def expected-statuses
  {"outParam" "reducible", "semiOutParam" "reducible"
   "ReducibilityFixture.regularReducible" "reducible"
   "ReducibilityFixture.abbreviation" "reducible"
   "ReducibilityFixture.hidden" "irreducible"
   "ReducibilityFixture.implicitOnly" "implicitReducible"
   "ReducibilityFixture.instanceOnly" "instanceReducible"
   "ReducibilityFixture.sample" "instanceReducible"
   "ReducibilityFixture.ordinary" "semireducible"
   "ReducibilityFixture.changedInImport" "irreducible"})

(defn- delete-directory! [directory]
  (doseq [file (reverse (file-seq directory))] (io/delete-file file)))

(defn- run-lean! [root directory args]
  (let [builder (ProcessBuilder. ^java.util.List (into [(str root "/bin/lean")] args))
        _ (.directory builder directory)
        _ (doto (.environment builder)
            (.put "LEAN_SYSROOT" root)
            (.put "LEAN_PATH" (str directory ":" root "/lib/lean")))
        err (io/file directory "lean.stderr")
        process (-> builder (.redirectError err) .start)
        output (slurp (.getInputStream process))
        exit (.waitFor process)]
    (when-not (zero? exit)
      (throw (ex-info "Lean reducibility fixture failed" {:exit exit :out output :err (slurp err)})))
    output))

(deftest lean-dump-import-and-derived-store-roundtrip
  (let [root (str (System/getProperty "user.home") "/.elan/toolchains/leanprover--lean4---v4.33.1")]
    (if-not (.exists (io/file root "bin/lean"))
      (println "SKIP reducibility dump roundtrip: Lean 4.33.1 unavailable")
      (let [directory (.toFile (Files/createTempDirectory "reducibility-attrs" (make-array FileAttribute 0)))]
        (try
          (doseq [source ["reducibility_attrs" "reducibility_attrs_extra"]]
            (io/copy (io/file (str "test/lean/" source ".lean")) (io/file directory (str source ".lean")))
            (is (empty? (run-lean! root directory ["-o" (str source ".olean") (str source ".lean")]))))
          (let [output (run-lean! root directory ["--run" (.getCanonicalPath (io/file "scripts/dump_attrs.lean"))
                                                  "Init" "reducibility_attrs_extra"])
                tuples (filterv #(and (= "reducibility" (first %)) (contains? expected-statuses (second %)))
                                (attrs/parse-attr-lines
                                 (filter (fn [line]
                                           (let [row (metadata/parse-attribute-row line)]
                                             (and (= "reducibility" (:kind row))
                                                  (contains? expected-statuses (:name row)))))
                                         (str/split-lines output))))
                store-path (io/file directory "store")]
            (is (= expected-statuses (into {} (map (fn [[_ n status _]] [n status])) tuples)))
            (let [sm (storage/open-store (.getPath store-path))]
              (try (storage/write-derived! (:store sm) "main" :attrs tuples)
                   (finally (storage/close-store sm))))
            (let [sm (storage/open-store (.getPath store-path))]
              (try
                (let [restored (storage/read-derived (:store sm) "main" :attrs)
                      base (reduce (fn [base n]
                                     (if (str/starts-with? n "ReducibilityFixture.")
                                       (env/check-constant base
                                                           (env/mk-def (name/from-string n) [] (e/const' (name/from-string "Nat") [])
                                                                       (e/lit-nat 1) :hints (if (= n "ReducibilityFixture.hidden") :abbrev :opaque)))
                                       base)) (a/env) (keys expected-statuses))
                      [loaded _] (attrs/import-attr-tuples base restored {})]
                  (is (= tuples restored))
                  (doseq [[n status] expected-statuses
                          :let [n (name/from-string n)]]
                    (is (= status (meta/get-reducibility-status loaded n)))
                    (doseq [mode [:none :reducible :instances :implicit :default :all]]
                      (is (= (case mode
                               :none false :all true :default (not= status "irreducible")
                               (or (= status "reducible")
                                   (and (#{:instances :implicit} mode) (= status "instanceReducible"))
                                   (and (= mode :implicit) (= status "implicitReducible"))))
                             (boolean (meta/can-unfold-default? loaded n mode (constantly true))))))
                    (when (str/starts-with? (name/->string n) "ReducibilityFixture.")
                      (doseq [mode [:reducible :instances :implicit :default :all]
                              :let [allowed? (meta/can-unfold-default? loaded n mode)
                                    expr (e/const' n [])]]
                        (is (= (if allowed? (e/lit-nat 1) expr)
                               (meta/whnf-at meta/empty-context {:env loaded :lctx {}} expr mode)))))))
                (finally (storage/close-store sm)))))
          (finally (delete-directory! directory)))))))

(deftest bundled-statuses-control-restricted-unfolding
  (doseq [n ["outParam" "semiOutParam"]
          :let [n (name/from-string n)]]
    (is (= "reducible" (meta/get-reducibility-status (a/env) n)))
    (is (not= :abbrev (env/get-reducibility-hints (env/lookup (a/env) n))))
    (is (not= (e/const' n [])
              (meta/whnf-at meta/empty-context {:env (a/env) :lctx {}} (e/const' n []) :reducible)))))

(deftest ordinary-local-definitions-default-to-semireducible
  (a/defn reducibilityOrdinary [n :- Nat] Nat n)
  (is (= "semireducible" (meta/get-reducibility-status (a/env) (name/from-string "reducibilityOrdinary")))))

(deftest invalid-status-is-rejected-before-presence-probes
  (doseq [line ["{\"kind\":\"reducibility\",\"name\":\"x\",\"status\":\"unknown\"}"
                "{\"kind\":\"reducibility\",\"name\":\"x\"}"]]
    (is (thrown? clojure.lang.ExceptionInfo (attrs/parse-attr-lines [line]))))
  (let [probes (atom 0)]
    (is (thrown? clojure.lang.ExceptionInfo
                 (attrs/import-attr-tuples (a/env) [["reducibility" "x" "unknown" nil]]
                                           {:present? #(do (swap! probes inc) true)})))
    (is (zero? @probes))))

(deftest irreducible-status-blocks-instance-projection-path
  (let [base (a/env)
        [hidden _] (attrs/import-attr-tuples base [["reducibility" "Add.add" "irreducible" nil]] {})
        expr (e/app* (e/const' (name/from-string "Add.add") [lvl/zero])
                     (e/const' (name/from-string "Nat") [])
                     (e/const' (name/from-string "instAddNat") []) (e/lit-nat 0) (e/lit-nat 1))
        normalize (fn [environment mode]
                    (meta/whnf-at meta/empty-context {:env environment :lctx {}} expr mode))]
    (doseq [mode [:instances :implicit]]
      (is (not= expr (normalize base mode)))
      (is (tc/is-def-eq (tc/mk-tc-state base) (normalize base mode) (e/lit-nat 1)))
      (is (= (normalize base :instances) (normalize base mode)))
      (is (= expr (normalize hidden mode))))
    (is (not= expr (normalize hidden :all)))
    (let [wrapper (name/from-string "projectionImplicitWrapper")
          wrapped (e/const' wrapper [])
          base (env/check-constant base (env/mk-def wrapper [] (e/const' (name/from-string "Nat") []) expr))
          [base _] (attrs/import-attr-tuples base [["reducibility" "projectionImplicitWrapper" "implicitReducible" nil]] {})]
      (is (= wrapped (meta/whnf-at meta/empty-context {:env base :lctx {}} wrapped :instances)))
      (is (= (normalize base :implicit)
             (meta/whnf-at meta/empty-context {:env base :lctx {}} wrapped :implicit))))))

(deftest implicit-projection-keeps-instance-reduction-at-instances
  (let [instance-name (name/from-string "projectionImplicitInstance")
        nat (e/const' (name/from-string "Nat") [])
        base (env/check-constant (a/env)
                                 (env/mk-def instance-name []
                                             (e/app (e/const' (name/from-string "Add") [lvl/zero]) nat)
                                             (e/const' (name/from-string "instAddNat") [])))
        [base _] (attrs/import-attr-tuples base [["reducibility" "projectionImplicitInstance" "implicitReducible" nil]] {})
        expr (e/app* (e/const' (name/from-string "Add.add") [lvl/zero])
                     nat (e/const' instance-name []) (e/lit-nat 0) (e/lit-nat 1))]
    (doseq [mode [:instances :implicit]]
      (is (= expr (meta/whnf-at meta/empty-context {:env base :lctx {}} expr mode))))))

(deftest reducible-class-field-reduces-instance-projection
  (let [[environment _] (attrs/import-attr-tuples (a/env) [["reducibility" "Add.add" "reducible" nil]] {})
        nat (e/const' (name/from-string "Nat") [])
        field (e/const' (name/from-string "Add.add") [lvl/zero])
        expr (e/app* field nat (e/const' (name/from-string "instAddNat") []) (e/lit-nat 0) (e/lit-nat 1))
        result (meta/whnf-at meta/empty-context {:env environment :lctx {}} expr :reducible)]
    (is (= "instanceReducible" (meta/get-reducibility-status environment (name/from-string "instAddNat"))))
    (is (not= expr result))
    (is (not (e/proj? (e/get-app-fn result))))
    (is (tc/is-def-eq (tc/mk-tc-state environment) result (e/lit-nat 1)))
    ;; A local instance stays stuck; unfoldDefault still returns its raw projection.
    (let [instance (e/fvar 99001)
          stuck (e/app* field nat instance (e/lit-nat 0) (e/lit-nat 1))
          lctx {99001 {:tag :local :id 99001 :name "inst"
                       :type (e/app (e/const' (name/from-string "Add") [lvl/zero]) nat)}}
          result (meta/whnf-at meta/empty-context {:env environment :lctx lctx} stuck :reducible)]
      (is (e/proj? (e/get-app-fn result)))
      (is (= instance (e/proj-struct (e/get-app-fn result)))))))
