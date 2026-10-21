(ns prototype.runtime-query-test
  "Pinned native compiler ABI limits, independent of the host JVM/JS machine."
  (:require [prototype.runtime-prim :as runtime]
            [prototype.native-scalar :as native]
            [prototype.machine :as m]
            #?(:clj [prototype.mutable :as u])
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(def expected
  {"lean_get_max_ctor_fields" 256
   "lean_get_max_ctor_scalars_size" 1024
   "lean_get_max_ctor_tag" 243
   "lean_get_usize_size" 8
   "lean_closure_max_args" 16})

(deftest pinned-runtime-layout-queries-preserve-world-and-ignore-unit
  ;; lean.h:772 admits num_objs<256, scalar_sz<1024 and tag<=243. Returning
  ;; 255/1023 here would change the Lean compiler's independent limit checks.
  (doseq [[symbol value] expected]
    (is (= {:arity 1} (get runtime/supported-symbols symbol)))
    (doseq [unit [0 (native/native-scalar 0) ::opaque-unit]]
      (let [world {:sentinel :unchanged}]
        (is (= [world value] (runtime/evaluate {} world symbol [unit])))))
    (doseq [args [[] [0 0]]]
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"arity"
            (runtime/evaluate {} nil symbol args))))))

(deftest small-nat-limit-is-the-pinned-guest-limit-or-an-explicit-precision-failure
  (is (= {:arity 1} (get runtime/supported-symbols "lean_max_small_nat")))
  #?(:clj (is (= [nil 9223372036854775807N]
                 (runtime/evaluate {} nil "lean_max_small_nat" [0])))
     :cljs (is (thrown-with-msg? js/Error #"exact 64-bit"
                 (runtime/evaluate {} nil "lean_max_small_nat" [0])))))

(def producer-library-profile
  ;; Exact installed4.33.1 release oracle (runtime/libuv.cpp +openssl.cpp), not
  ;; a universal Leanversion→libraryversion mapping or hosted IO capability.
  {"lean_libuv_version" 77824 "lean_openssl_version" 811597824})

(deftest library-build-queries-require-explicit-snapshot-capabilities
  (doseq [[symbol expected] producer-library-profile]
    (is (= {:arity 1} (get runtime/supported-symbols symbol)))
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"runtime build capability"
          (runtime/evaluate {} nil symbol [0])))
    (let [world (assoc (m/world {}) :runtime-build producer-library-profile)
          ops {:runtime-build m/runtime-build-entry}]
      (is (= [world expected] (runtime/evaluate ops world symbol [0])))
      (is (= [world expected] (m/expr world [:runtime symbol [[:imm 0]]])))
      (let [world (assoc world :runtime-build-overrides {symbol 0})]
        (is (= [world 0] (runtime/evaluate ops world symbol [0]))))
      (doseq [bad-world [(m/world {})
                         (assoc world :runtime-build nil)
                         (assoc world :runtime-build {symbol -1})
                         (assoc world :runtime-build {symbol 4294967296})
                         (assoc world :runtime-build-overrides [])]]
        (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
              (runtime/evaluate ops bad-world symbol [0])))))))

#?(:clj
   (deftest mutable-build-inputs-preserve-profile-and-overrides-across-snapshots
     (let [world (assoc (m/world {}) :runtime-build producer-library-profile
                        :runtime-build-overrides {"lean_libuv_version" 42}
                        :eval-const-authorizations {:sentinel :preserved})
           machine (u/thaw world) before (u/freeze machine)]
       (is (= 42 (u/runtime-value! machine "lean_libuv_version" [0])))
       (is (= 811597824 (u/runtime-value! machine "lean_openssl_version" [0])))
       (is (= before (u/freeze machine)))
       (is (= producer-library-profile (:runtime-build before)))
       (is (= {"lean_libuv_version" 42} (:runtime-build-overrides before)))
       (is (= {:sentinel :preserved} (:eval-const-authorizations before))))))

#?(:cljs (do (defn -main [] (cljs.test/run-tests 'prototype.runtime-query-test))
             (set! *main-cli-fn* -main)))
