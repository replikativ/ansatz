(ns prototype.runtime-ffi-query-test
  "Native-oracle build strings are supplied explicitly, without native codegen."
  (:require [prototype.runtime-prim :as runtime]
            [prototype.machine :as m]
            [prototype.native-scalar :as native]
            #?(:clj [prototype.mutable :as u])
            #?(:clj [clojure.data.json :as json])
            #?(:clj [clojure.edn :as edn])
            [clojure.string :as str]
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(defn rows []
  (let [text #?(:clj (slurp "fixtures/runtime-ffi-build-queries.jsonl")
                :cljs (.readFileSync (js/require "fs") "fixtures/runtime-ffi-build-queries.jsonl" "utf8"))]
    (mapv #?(:clj #(json/read-str % :key-fn keyword)
             :cljs #(js->clj (js/JSON.parse %) :keywordize-keys true)) (str/split-lines text))))
(defn flags [hex]
  #?(:clj (String. (byte-array (map #(unchecked-byte (Integer/parseInt (apply str %) 16)) (partition 2 hex)))
                   java.nio.charset.StandardCharsets/UTF_8)
     :cljs (.toString (.from (.-Buffer (js/require "buffer")) hex "hex") "utf8")))
(defn profile []
  (reduce (fn [profile {:keys [symbol selector utf8Hex]}]
            (case selector
              "unit" (assoc profile symbol (flags utf8Hex))
              "nonzero" profile
              (assoc-in profile [symbol (keyword selector)] (flags utf8Hex)))) {} (rows)))
(def ops {:runtime-build m/runtime-build-entry})

(deftest native-build-query-strings-match-byte-for-byte
  (let [world (assoc (m/world {}) :runtime-build (profile))]
    (is (= 7 (count (rows))))
    (doseq [{:keys [symbol selector utf8Hex]} (rows)]
      (is (= {:arity 1} (get runtime/supported-symbols symbol)))
      (let [argument (get {"unit" 0 "shared" 0 "static" 1 "nonzero" 2} selector)
            expected (flags utf8Hex)]
        (is (= [world expected] (runtime/evaluate ops world symbol [argument])))
        (is (= [world expected] (m/expr world [:runtime symbol [[:imm argument]]])))))
    (doseq [[argument selector] [[(native/native-scalar 0) :shared] [(native/native-scalar 1) :static]]]
      (is (= [world (get-in (profile) ["lean_get_linker_flags" selector])]
             (runtime/evaluate ops world "lean_get_linker_flags" [argument]))))
    #?(:clj (is (= (profile) (select-keys (:runtime-build (edn/read-string (slurp "fixtures/runtime-build-profile.edn")))
                                         (keys (profile))))))))

(deftest explicit-ffi-metadata-preconditions-and-overrides
  (let [symbol "lean_get_leanc_extra_flags"
        world (assoc (m/world {}) :runtime-build (profile))
        invalid-unicode #?(:clj (str (char 55296)) :cljs (js/String.fromCharCode 55296))]
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"runtime build capability"
          (runtime/evaluate {} world symbol [0])))
    (doseq [value [nil 42 invalid-unicode "bad\u0000flags"]]
      (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
            (runtime/evaluate ops (assoc-in world [:runtime-build symbol] value) symbol [0]))))
    (doseq [value ["" " ROOT  \"space\" \\flags é😀 "]]
      (let [overridden (assoc world :runtime-build-overrides {symbol value})]
        (is (= [overridden value] (runtime/evaluate ops overridden symbol [0])))))
    (doseq [entry [nil "flags" {:static "only static"} {:shared nil}]]
      (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
            (runtime/evaluate ops (assoc-in world [:runtime-build "lean_get_linker_flags"] entry)
                              "lean_get_linker_flags" [0]))))
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
          (runtime/evaluate ops world "lean_get_linker_flags" [256])))))

#?(:clj
   (deftest ffi-query-inputs-survive-mutable-freeze-and-fork
     (let [world (assoc (m/world {}) :runtime-build (profile)
                        :runtime-build-overrides {"lean_get_linker_flags" {:static "S" :shared "D"}})
           machine (u/thaw world) before (u/freeze machine)]
       (is (= "S" (u/runtime-value! machine "lean_get_linker_flags" [1])))
       (is (= "D" (u/runtime-value! machine "lean_get_linker_flags" [0])))
       (is (= before (u/freeze machine)))
       (is (= "S" (u/runtime-value! (u/thaw before) "lean_get_linker_flags" [1]))))))

#?(:cljs (do (defn -main [] (cljs.test/run-tests 'prototype.runtime-ffi-query-test))
             (set! *main-cli-fn* -main)))
