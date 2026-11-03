(ns ansatz-lean-jvm-used-products-checks
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.used-products :as products]
            [ansatz.lean.jvm.installed :as installed]))

(defn- n [& parts] (reduce #(vector "str" %1 %2) ["anonymous"] parts))
(def sha (apply str (repeat 64 "a")))
(def other-sha (apply str (repeat 64 "b")))
(defn- module-row [module]
  {"module" module "productSha256" sha
   "products" (mapv #(if (= ".olean" %)
                       {"role" % "present" true "bytes" 10 "sha256" sha}
                       {"role" % "present" false}) installed/suffixes)})
(defn- manifest [& names]
  {"schema" products/schema "modules" (mapv module-row names)})
(defn- reason [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e
                 (is (= "InvalidUsedModuleProducts" (:code (ex-data e)))) (:reason (ex-data e)))))

(deftest primary-and-optional-product-custody
  (let [doc (manifest (n "Example"))]
    (is (identical? doc (products/validate! doc)))
    (is (= :primary-digest (reason #(products/validate! (assoc-in doc ["modules" 0 "productSha256"] other-sha)))))
    (is (= :primary-missing (reason #(products/validate! (assoc-in doc ["modules" 0 "products" 0]
                                                                {"role" ".olean" "present" false})))))
    (is (= :roles (reason #(products/validate! (update-in doc ["modules" 0 "products"] pop)))))
    (is (= :presence (reason #(products/validate! (assoc-in doc ["modules" 0 "products" 1 "present"] 0)))))
    (is (= :keys (reason #(products/validate! (assoc-in doc ["modules" 0 "products" 1 "sha256"] sha)))))
    (is (= :roles (reason #(products/validate! (assoc-in doc ["modules" 0 "products" 1 "role"] ".olean")))))
    (is (= :product-bytes (reason #(products/validate! (assoc-in doc ["modules" 0 "products" 0 "bytes"] -1)))))
    (is (= :product-bytes (reason #(products/validate! (assoc-in doc ["modules" 0 "products" 0 "bytes"] 1.5)))))
    (is (= :duplicate-module (reason #(products/validate! (update doc "modules" into (get doc "modules"))))))))

(deftest inventory-is-not-import-authorization
  (let [local (n "App") init (n "Init" "Data" "Ord" "Basic") foreign (n "Package" "Type")
        doc (manifest local init foreign)]
    (is (= doc (products/authorize! doc [foreign local init] [local] [foreign])))
    (is (= :undeclared-origin (reason #(products/authorize! doc [local init foreign] [local] []))))
    (is (= :inventory-mismatch (reason #(products/authorize! doc [local init] [local] [foreign]))))
    (is (= :origin-shadowing (reason #(products/authorize! doc [local init foreign] [local] [local foreign]))))
    (is (= :init-shadowing (reason #(products/authorize! doc [local init foreign] [local init] [foreign]))))
    (is (= (manifest) (products/authorize! (manifest) [] [] [])))))

(deftest actual-origin-binds-logical-identity
  (let [module (n "App") doc (manifest module)
        graph {"schema" "lean-jvm-type-graph/3" "roots" [{"kind" "nominal" "id" 0}]
               "definitions" [{"id" 0 "name" (n "App" "Value")
                               "origin" {"module" module "productSha256" sha}
                               "arguments" [] "universes" []
                               "constructors" [{"name" (n "App" "Value" "mk") "fields" []}]}]}]
    (is (= doc (products/bind-graph! doc graph)))
    (is (= :graph-product (reason #(products/bind-graph! doc (assoc-in graph ["definitions" 0 "origin" "productSha256"] other-sha)))))
    (is (= :graph-origin-set (reason #(products/bind-graph! (manifest module (n "Extra")) graph)))))
  (is (= (manifest) (products/bind-graph! (manifest)
                          {"schema" "lean-jvm-type-graph/3" "roots" [{"kind" "nat"}] "definitions" []}))))

(deftest canonical-product-baseline
  (let [a (n "A") b (n "B") original (manifest a b)]
    (is (= (products/digest original) (products/digest (manifest b a))))
    (is (not= (products/digest original)
              (products/digest (assoc-in original ["modules" 0 "products" 1]
                                        {"role" ".olean.server" "present" true "bytes" 0 "sha256" other-sha})))))
    (is (= :module (reason #(products/validate! (manifest (n ".."))))))
    (is (= :module-utf16 (reason #(products/validate! (manifest (n (str (char 0xd800)))))))))

(defn check! [] (run-tests 'ansatz-lean-jvm-used-products-checks))
