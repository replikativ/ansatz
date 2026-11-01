(ns source-import-setup-checks-v1
  "Import-header binding models only; parser/Env construction is not simulated
   as successful module admission. Actual setup/runtime validation is separate."
  (:require [clojure.test :refer [deftest is run-tests]]
            [source-import-frontend-setup-v1 :as setup]
            [imported-frontend-setup-v4 :as fixed]
            [java-source-module-exchange-v1 :as exchange]
            [java-source-module-base-v1 :as base]
            [general-generated-batch-v1 :as batch]))
(defn import-model [f]
  (with-redefs-fn
    {#'exchange/array-values (fn [_ xs _] xs)
     #'exchange/scoped (fn [_ callback] (callback ::scope))
     #'exchange/ordinary (fn [_ x _ _ _] {:fields (object-array [(:module x)]) :bytes (byte-array (:flags x))})
     #'exchange/typed-name (fn [_ x] x) #'exchange/wire-name identity}
    f))
(def prelude {:module exchange/prelude-name :importAll false :isExported true :isMeta false})
(def source-a {:module ["str" ["anonymous"] "A"] :importAll false :isExported true :isMeta false})
(defn input [request] {:module (:module request) :flags [0 1 0]})
(deftest exact-parser-imports-must-match-closure-root-order-and-flags
  (import-model
    (fn []
      (is (nil? (#'setup/validate-imports! {:driver {:engine ::engine}} [prelude source-a] [(input prelude) (input source-a)])))
      (doseq [actual [[(input source-a) (input prelude)] [(input prelude)]
                      [(input prelude) (assoc (input source-a) :flags [1 1 0])]
                      [(input prelude) (assoc (input source-a) :flags [0 0 0])]
                      [(input prelude) (assoc (input source-a) :flags [0 1 1])]
                      [(input prelude) {:module ["str" ["anonymous"] "B"] :flags [0 1 0]}]]]
        (is (thrown? Exception (#'setup/validate-imports! {:driver {:engine ::engine}} [prelude source-a] actual)))))))
(deftest typed-module-names-are-compared-without-display-normalization
  (import-model
    (fn []
      (let [num {:module ["num" ["anonymous"] "7"] :importAll false :isExported true :isMeta false}
            str {:module ["str" ["anonymous"] "7"] :importAll false :isExported true :isMeta false}]
        (is (thrown? Exception (#'setup/validate-imports! {:driver {:engine ::engine}} [num] [(input str)])))))))
(deftest existing-fixed-wrapper-keeps-its-default-validator-and-runtime-path
  (with-redefs-fn {#'fixed/setup-classic* (fn [& args] (vec args))}
    (fn []
      (let [args (fixed/setup-prelude! ::driver ::env "text" "file")
            explicit (fixed/setup-prelude! ::driver ::env "text" "file" ["Custom"])]
        (is (= [::driver ::env "text" "file" ["Hosted" "SequentialProbe"]] (subvec args 0 5)))
        (is (identical? fixed/validate-prelude-imports! (nth args 5)))
        (is (nil? (nth args 6)))
        (is (= ["Custom"] (nth explicit 4)))
        (is (identical? fixed/validate-prelude-imports! (nth explicit 5)))))))

(deftest imported-code-scope-is-bound-to-issued-run-base-and-selected-modules
  (let [engine (Object.) source (Object.) run (Object.) closure (Object.) base-token (Object.)
        selected (Object.) other (Object.) name ["str" ["anonymous"] "sourceStep"]
        header (Object.) body (Object.) current-body (atom body) live (atom true)
        roots (atom [selected]) run-source (atom source) adapter {:engine engine :source source
                    :matched-base base-token :authority {:finalized-run run}}
        driver {:engine engine :source source} binding (atom nil)
        modules {selected {:engine engine :source source :rows {name {:header header :row {"name" name
                          "ir" {"fdecl" {"f" name}}}}}}
                 other {:engine engine :source source :rows {}}}]
    (with-redefs-fn
      {#'base/assert-session! (fn [b e s r]
           (assert (and @live (identical? b base-token) (identical? e engine)
                        (identical? s source) (identical? r run))))
       #'exchange/with-finalized! (fn [r callback] (assert (identical? r run))
           (callback {:basis :actual-source-closure-finalizer-only :closure closure :engine engine :source @run-source}))
       #'exchange/with-closure! (fn [c callback] (assert (identical? c closure))
           (callback {:engine engine :source source :module-roots @roots}))
       #'exchange/with-module! (fn [m callback] (callback (get modules m)))
       #'setup/ready-row! (fn [& _] @current-body)
       #'batch/open-scope* (fn [d a imports] (assert (identical? d driver))
                               (assert (identical? a adapter)) (reset! binding imports) ::scope)}
      #(do
         (is (= ::scope (setup/open-generated-scope! {:driver driver} adapter base-token run)))
         (is (= #{name} (set (keys (:entries @binding)))))
         (is (nil? ((:check! @binding))))
         (is (thrown? Exception (setup/open-generated-scope! {:driver driver} adapter base-token (Object.))))
         (reset! run-source (Object.)) (is (thrown? Exception ((:check! @binding))))
         (reset! run-source source) (reset! live false) (is (thrown? AssertionError ((:check! @binding))))
         (reset! live true) (reset! current-body (Object.)) (is (thrown? Exception ((:check! @binding))))
         (reset! current-body body) (reset! roots [other]) (is (thrown? Exception ((:check! @binding))))))))

(defn check! [] (run-tests 'source-import-setup-checks-v1))
