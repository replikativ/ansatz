(ns build-audit-test
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.edn :as edn] [clojure.java.io :as io]
            [build-audit :as audit]))

(defn fixture [f]
  (let [root (.toFile (java.nio.file.Files/createTempDirectory "lean-closure-test-" (make-array java.nio.file.attribute.FileAttribute 0)))
        runtime (io/file root "runtime") module (io/file root "module")
        source (io/file runtime "prototype/entry.clj") target (io/file runtime "prototype/target.clj")]
    (.mkdirs (.getParentFile source)) (.mkdirs module)
    (spit source "(ns prototype.entry) (defn invoke [] (requiring-resolve 'prototype.target/run!))")
    (spit target "(ns prototype.target) (defn run! [] :ok)")
    (try
      (f {:schema "lean-runtime-closure/2" :sources ["prototype/entry.clj" "prototype/target.clj"]
          :resources [] :java [] :compiler-profile audit/pattern-profile
          :dynamic-resolves [{:source "prototype/entry.clj" :var 'prototype.target/run! :feature :typed-compiler}]}
         runtime module source target)
      (finally (doseq [file (reverse (file-seq root))] (.delete file))))))

(deftest exact-dynamic-inventory-and-staged-target
  (fixture
   (fn [closure runtime module _ target]
     (is (= {:sources 2 :dynamic-resolves 1} (audit/verify! closure runtime module)))
     (doseq [bad [(assoc closure :dynamic-resolves [])
                  (update closure :dynamic-resolves conj (first (:dynamic-resolves closure)))
                  (assoc-in closure [:dynamic-resolves 0 :var] 'prototype.target/missing)
                  (assoc-in closure [:dynamic-resolves 0 :feature] :llvm)
                  (assoc-in closure [:compiler-profile :source-git/sha] (apply str (repeat 40 "0")))]]
       (is (thrown? clojure.lang.ExceptionInfo (audit/verify! bad runtime module))))
     (spit target "(ns prototype.target) (defn other [] :wrong)")
     (is (thrown? clojure.lang.ExceptionInfo (audit/verify! closure runtime module))))))

(deftest reader-never-executes-or-accepts-computed-resolvers
  (fixture
   (fn [closure runtime module source _]
     (doseq [body ["(requiring-resolve (symbol \"prototype.target\" \"run!\"))"
                   "(apply requiring-resolve ['prototype.target/run!])"
                   "(core/requiring-resolve 'prototype.target/run!)"
                   "(clojure.core/requiring-resolve 'prototype.target/other)"]]
       (spit source (str "(ns prototype.entry) " body))
       (is (thrown? clojure.lang.ExceptionInfo (audit/verify! closure runtime module))))
     (spit source "(ns prototype.entry (:require [pattern.never-load :as p])) (def marker ::p/example) (defn invoke [] (requiring-resolve 'prototype.target/run!))")
     (is (= {:sources 2 :dynamic-resolves 1} (audit/verify! closure runtime module)))
     (is (nil? (find-ns 'pattern.never-load)))
     (spit source "(ns prototype.entry) #=(throw (Exception. \"reader executed\"))")
     (is (thrown? RuntimeException (audit/verify! closure runtime module))))))

(deftest current-complete-inventory-requires-no-pattern
  (let [deps (edn/read-string (slurp "deps.edn"))]
    (is (audit/verify-dependency! deps))
    (is (thrown? clojure.lang.ExceptionInfo
                 (audit/verify-dependency! (assoc-in deps [:deps 'org.replikativ/pattern :mvn/version] "1.0.449"))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (audit/verify-dependency! (assoc-in deps [:aliases :pattern-git :override-deps 'org.replikativ/pattern :git/sha] "wrong")))))
  (is (= {:sources 65 :dynamic-resolves 5}
         (audit/verify! (edn/read-string (slurp "runtime-closure.edn")) "../../experiments/lean-ir/src" "src")))
  (is (nil? (find-ns 'pattern.nanopass.dialect)))
  (is (nil? (find-ns 'prototype.typed-tail-execution))))

(defn run-tests! [] (run-tests 'build-audit-test))
