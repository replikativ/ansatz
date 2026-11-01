(ns prototype.runtime-shell-query-test
  (:require [prototype.runtime-prim :as runtime]
            [prototype.machine :as m]
            #?(:clj [clojure.data.json :as json])
            #?(:clj [clojure.edn :as edn])
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(defn profile []
  (let [text #?(:clj (slurp "fixtures/runtime-shell-build-queries.json")
                :cljs (.readFileSync (js/require "fs") "fixtures/runtime-shell-build-queries.json" "utf8"))]
    #?(:clj (json/read-str text) :cljs (js->clj (js/JSON.parse text)))))
(def ops {:runtime-build m/runtime-build-entry})

(deftest explicit-shell-build-defaults-match-pinned-native-oracle
  (let [profile (profile) world (assoc (m/world {}) :runtime-build profile)]
    (is (= 6 (count profile)))
    (doseq [[symbol expected] profile]
      (is (= {:arity 1} (get runtime/supported-symbols symbol)))
      (is (= [world expected] (runtime/evaluate ops world symbol [0])))
      (is (= [world expected] (m/expr world [:runtime symbol [[:imm 0]]])))
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"runtime build capability"
            (runtime/evaluate ops (m/world {}) symbol [0]))))
    #?(:clj (is (= profile (select-keys (:runtime-build (edn/read-string (slurp "fixtures/runtime-build-profile.edn")))
                                      (keys profile)))))))

(deftest explicit-bool-and-nat-metadata-remain-typed-and-snapshot-local
  (let [profile (profile) base (assoc (m/world {}) :runtime-build profile)
        symbol "lean_internal_has_llvm_backend"
        override (assoc base :runtime-build-overrides {symbol 0})]
    (is (= [override 0] (runtime/evaluate ops override symbol [0])))
    (is (= profile (:runtime-build override)))
    (doseq [symbol ["lean_internal_has_llvm_backend" "lean_internal_get_default_verbose" "lean_internal_is_multi_thread"]
            value [true false 2 -1 1.5 "1"]]
      (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
            (runtime/evaluate ops (assoc-in base [:runtime-build symbol] value) symbol [0]))))
    (doseq [symbol ["lean_internal_get_default_max_memory" "lean_internal_get_default_max_heartbeat"]]
      (let [world (assoc-in base [:runtime-build symbol] 1099511627776)]
        (is (= [world 1099511627776] (runtime/evaluate ops world symbol [0]))))
      (doseq [value [-1 1.5 "0"]]
        (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
              (runtime/evaluate ops (assoc-in base [:runtime-build symbol] value) symbol [0]))))
      #?(:clj (is (thrown-with-msg? clojure.lang.ExceptionInfo #"exact tagged profile"
                    (runtime/evaluate ops (assoc-in base [:runtime-build symbol] 9223372036854775808N) symbol [0])))
         :cljs (is (thrown-with-msg? js/Error #"exact guest Nat"
                     (runtime/evaluate ops (assoc-in base [:runtime-build symbol] 9007199254740992) symbol [0])))))))

#?(:cljs (do (defn -main [] (cljs.test/run-tests 'prototype.runtime-shell-query-test))
             (set! *main-cli-fn* -main)))
