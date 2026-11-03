(ns ansatz-lean-jvm-entry-v3-checks
  "Pure checks over a genuine private CLI receipt; no source/cohort admission."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [ansatz.lean.jvm.entry-v3 :as candidate]
            [ansatz.lean.jvm.used-products :as products])
  (:import [java.nio.file Path Files]))

(def ^:dynamic *fixture* "test/fixtures/nominal-entry-v3/entry-evidence.json")
(defn- n [& parts] (reduce #(vector "str" %1 %2) ["anonymous"] parts))
(def ^:dynamic *oracle-fixture* "test/fixtures/nominal-entry-v3/oracle-entry-evidence.json")
(defn- fixture
  ([] (fixture *fixture*))
  ([file]
  (let [path (Path/of file (make-array String 0))]
    (assert (<= (Files/size path) (* 16 1048576)))
    (json/read-str (Files/readString path)))))
(defn- context [doc]
  ;; Known producer-side fixtures only. A future issuer supplies its actual local
  ;; module set independently of this document, not this test convenience.
  {:root (get doc "compiledModule") :request (get doc "request")
   :module-products (get doc "moduleProducts")
   :local-modules (vec (distinct [(get doc "compiledModule") (n "NativeNominalFixtures")
                                 (n "NativeBuiltinWitnessFixtures")]))
   :installed-imports []})
(defn- checked [doc] (candidate/validate-document! (context doc) doc))
(defn- refusal [ctx doc]
  (try (candidate/validate-document! ctx doc) nil
       (catch clojure.lang.ExceptionInfo e
         (is (#{"InvalidEntryV3" "InvalidRepresentation" "InvalidTypeGraph" "InvalidUsedModuleProducts"} (:code (ex-data e))))
         (ex-data e))))
(defn- reason [ctx doc] (:reason (refusal ctx doc)))
(defn- reason-is [expected ctx doc] (is (= expected (reason ctx doc))))
(defn- entry-index [doc name]
  (first (keep-indexed #(when (= name (last (get %2 "name"))) %1) (get doc "entries"))))
(defn- row-index [doc name]
  (first (keep-indexed #(when (= name (get %2 "name")) %1) (get doc "declarations"))))

(deftest actual-cli-full-catalog-is-description-only
  (let [doc (fixture) result (checked doc)]
    (is (= :checked-description-only (:scope result)))
    (is (= :none (:authority result)))
    (is (true? (:native-defeq-requires-authenticated-producer result)))
    (is (= :required (:source-reconciliation result)))
    (is (= (get doc "entries") (:entries result)))
    (is (= (count (get-in doc ["typeGraph" "roots"])) (count (get-in result [:storage :normalized "roots"]))))
    (is (true? (:io? result)))
    (is (= (count (get doc "declarations")) (count (:declarations result))))
    (is (= (products/digest (get doc "moduleProducts")) (get-in doc ["request" "moduleProductsSHA256"])))
    (let [i (entry-index doc "echoHigher") root (first (get-in doc ["entries" i "typeCheck" "signature" "arguments"]))
          native (get-in doc ["rootTypes" root])]
      (is (= ["succ" ["zero"]] (get-in native [1 2 0])))
      (is (= native (get-in doc ["entries" i "typeCheck" "expectedType" 3]))))))

(deftest actual-oracle-full-catalog-and-declarations
  (let [doc (fixture *oracle-fixture*) result (checked doc)]
    (is (= :none (:authority result)))
    (is (= 10 (count (:entries result))))
    (is (= 163 (count (:declarations result))))
    (is (= 29 (count (get-in result [:storage :normalized "plans"]))))
    (is (= 8 (count (get-in result [:storage :normalized "roots"]))))
    (is (true? (:io? result)))))

(deftest exact-document-request-and-product-binding
  (let [doc (fixture) ctx (context doc)]
    (doseq [[path value] [[["unexpected"] true] [["schema"] "lean-native-entry-evidence/2"]
                        [["producer"] "Other.export"] [["leanVersion"] "4.33.0"]
                        [["guestKernelAdmission"] true] [["dynamicClosureProven"] true]
                        [["initializationPlanScope"] "admitted"]
                        [["runtimeProfile" "wordBits"] 32] [["compiledModule"] (n "Different")]]]
      (is (some? (refusal ctx (assoc-in doc path value)))))
    (reason-is :keys (assoc ctx :unexpected true) doc)
    (reason-is :keys (assoc ctx :request (assoc (:request ctx) "unexpected" true)) doc)
    (reason-is :document-profile ctx (assoc-in doc ["request" "moduleProductsSHA256"] (apply str (repeat 64 "0"))))
    (let [bad-products (assoc-in (:module-products ctx) ["modules" 0 "productSha256"] (apply str (repeat 64 "0")))]
      (is (some? (refusal (assoc ctx :module-products bad-products) (assoc doc "moduleProducts" bad-products)))))
    (reason-is :selected-entries (update ctx :request assoc "entries" []) (assoc-in doc ["request" "entries"] []))))

(deftest catalog-expected-function-and-native-claim-boundaries
  (let [doc (fixture) ctx (context doc) higher (entry-index doc "echoHigher")]
    (doseq [[path value] [[["entries" 0 "typeCheck" "signature" "effect"] "base-io"]
                        [["entries" 0 "typeCheck" "signature" "result"] 9999]
                        [["entries" 0 "typeCheck" "expectedType"] ["const" (n "String") []]]
                        [["entries" 0 "typeCheck" "transparency"] "all"]
                        [["entries" 0 "actualType"] ["bvar" 0]]
                        [["entries" 0 "actualType"] ["const" (n "Nat") [["param" "u"]]]]
                        [["rootTypes" 0] ["const" (n "String") []]]]]
      (is (some? (refusal ctx (assoc-in doc path value)))))
    (reason-is :expected-type ctx (assoc-in doc ["entries" higher "typeCheck" "expectedType" 3 1 2 0] ["zero"]))
    ;; Syntax cannot authenticate a native alias's meaning. Altering this claim
    ;; must fail outer issuer byte custody; it cannot confer authority here.
    (let [alias-claim (assoc-in doc ["entries" 0 "actualType"] ["const" (n "UnverifiedClosedAlias") []])
          result (candidate/validate-document! ctx alias-claim)]
      (is (= :none (:authority result)))
      (is (true? (:native-defeq-requires-authenticated-producer result))))
    (let [unused (update-in doc ["entries" 0 "typeCheck" "signature"] assoc "arguments" [] "result" 1)]
      (reason-is :root-usage ctx unused))))

(deftest exact-owned-abi-real-declaration-and-io-world
  (let [doc (fixture) ctx (context doc) io (entry-index doc "ioIdentity") scalar (entry-index doc "opValue")
        raw-name (get-in doc ["entries" 0 "raw" "name"]) row (row-index doc raw-name)]
    (doseq [[path value] [[["entries" 0 "callable" "xs" 0 "borrow"] true]
                        [["entries" 0 "argumentPlan" 0 "index"] 1]
                        [["entries" 0 "levelParams"] ["u"]]
                        [["entries" 0 "kind"] "axiom"]
                        [["entries" 0 "callable" "name"] (n "GuessedBoxedName")]
                        [["entries" 0 "compiledModule"] (n "Init" "Data" "Nat" "Basic")]
                        [["entries" io "raw" "xs" 1 "ty"] "tagged"]
                        [["entries" io "argumentPlan" 1 "representation"] "arbitrary-world"]
                        [["entries" scalar "resultABI" "lane"] "uint32"]
                        [["entries" scalar "resultABI" "resultRoot"] 0]
                        [["entries" scalar "resultABI" "extra"] true]
                        [["declarations" row "ir" "fdecl" "info"] {"sorryDep?" (n "sorryAx")}]
                        [["declarations" row "sourceModule"] (n "Different")]]]
      (is (some? (refusal ctx (assoc-in doc path value)))))
    (reason-is :boxed-abi-correspondence ctx (assoc-in doc ["entries" 0 "callable" "type"] "tagged"))
    (reason-is :argument-plan ctx (update-in doc ["entries" io "argumentPlan"] pop))))

(deftest declaration-closure-owner-and-initializer-custody
  (let [doc (fixture) ctx (context doc) raw-name (get-in doc ["entries" 0 "raw" "name"]) row (row-index doc raw-name)
        external (first (keep-indexed #(when (get-in %2 ["ir" "extern"]) %1) (get doc "declarations")))]
    (reason-is :redirect ctx (assoc-in doc ["declarations" external "redirect"] false))
    (is (some? (refusal ctx (-> doc (assoc-in ["declarations" external "runtime" "role"] "initialized")
                              (assoc-in ["declarations" external "runtime" "initializer"] false)))))
    (reason-is :declaration-dependencies ctx (assoc-in doc ["declarations" row "dependencies"] [(n "FakeDependency")]))
    (reason-is :dynamic-site-count ctx (update doc "dynamicAPSites" inc))
    (reason-is :duplicate-declaration ctx (update doc "declarations" conj (first (get doc "declarations"))))
    (reason-is :initializer-module-order ctx (update doc "initializerAttributeInventory" pop))
    (reason-is :initializer-pair ctx (assoc-in doc ["initializerAttributeInventory" 0 "regularModuleEntries"] [[(n "x")]]))
    (reason-is :imported-module-authorization ctx (update doc "importedModuleOrder" conj (n "Unlisted")))
    (reason-is :root-module-authorization
               (assoc ctx :local-modules (filterv #(not= (:root ctx) %) (:local-modules ctx))
                          :installed-imports [(:root ctx)]) doc)
    (reason-is :declaration-runtime ctx (assoc-in doc ["declarations" row "runtime" "initializationAction"] "unknown"))))

(deftest pre-json-work-and-escaped-byte-bounds
  (let [n (.subtract (.shiftLeft java.math.BigInteger/ONE 4096) java.math.BigInteger/ONE)]
    ;; These repeated refs are cheap inputs; refusal must precede decimal/JSON
    ;; materialization of an over-budget result, not an allocator failure.
    (is (some? (try (#'candidate/data-bound! (vec (repeat 200 n)) 1024) nil
                    (catch clojure.lang.ExceptionInfo e (ex-data e)))))
    (is (some? (try (#'candidate/data-bound! [(str (apply str (repeat 100 (char 0))))] 128) nil
                    (catch clojure.lang.ExceptionInfo e (ex-data e)))))
    (is (some? (try (#'candidate/data-bound! (.shiftLeft java.math.BigInteger/ONE 4096) 10000) nil
                    (catch clojure.lang.ExceptionInfo e (ex-data e)))))
    (is (nil? (#'candidate/data-bound! [n] 2000)))))

(defn check!
  ([] (run-tests 'ansatz-lean-jvm-entry-v3-checks))
  ([fixture-path]
   (let [primary (Path/of fixture-path (make-array String 0))
         oracle (.resolve (.getParent primary) "oracle-entry-evidence.json")]
     (check! fixture-path (str oracle))))
  ([fixture-path oracle-path]
   (binding [*fixture* fixture-path *oracle-fixture* oracle-path]
     (run-tests 'ansatz-lean-jvm-entry-v3-checks))))
