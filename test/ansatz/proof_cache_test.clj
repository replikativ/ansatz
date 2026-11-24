(ns ansatz.proof-cache-test
  "The proof-term cache: a second proof of the same theorem uses the stored term, which the
   kernel checks against the statement elaborated now; an entry that is damaged, or holds a term
   that does not prove the statement, is refused and the tactics run instead."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [clojure.java.io :as io]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.proof-cache :as pc])
  (:import [ansatz.kernel ConstantInfo]))

(defn- setup [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (f)))

(use-fixtures :once fixtures/isolated-session setup)

(defn- temp-dir []
  (str (java.nio.file.Files/createTempDirectory "proof-cache" (make-array java.nio.file.attribute.FileAttribute 0))))

(defn- prove-fresh!
  "Prove `nm` in a copy of `env0` and return [the theorem's ConstantInfo, the cache's counts]."
  [env0 nm params prop tactics]
  (reset! pc/stats {})
  (reset! a/ansatz-env env0)
  (a/prove-theorem nm params prop tactics)
  [(env/lookup (a/env) (name/from-string (str nm))) @pc/stats])

(deftest a-stored-term-is-used-and-checked
  (let [env0 (a/env)
        dir (temp-dir)]
    (try
      (binding [pc/*dir* dir]
        (let [args ['pc-add-zero '[n :- Nat] '(= Nat (+ n 0) n) '[(simp)]]
              [^ConstantInfo first-ci first-stats] (apply prove-fresh! env0 args)
              [^ConstantInfo second-ci second-stats] (apply prove-fresh! env0 args)]
          (is (= {:miss 1 :stored 1} first-stats))
          (is (= {:hit 1} second-stats))
          (testing "the theorem is the same, with the same statement and proof term"
            (is (= (.type first-ci) (.type second-ci)))
            (is (= (.value first-ci) (.value second-ci))))
          (testing "a damaged entry is refused and the tactics prove the theorem"
            (doseq [f (file-seq (io/file dir)) :when (.isFile ^java.io.File f)]
              (spit f "not an entry"))
            (let [[^ConstantInfo ci stats] (apply prove-fresh! env0 args)]
              (is (= {:rejected 1 :stored 1} stats))
              (is (= (.value first-ci) (.value ci)))))
          (testing "an entry whose term does not prove the statement is refused by the kernel"
            (let [other ['pc-mul-one '[n :- Nat] '(= Nat (* n 1) n) '[(simp)]]
                  _ (apply prove-fresh! env0 other)
                  key-of (fn [[nm params prop tactics]]
                           (reset! a/ansatz-env env0)
                           ;; the key prove-theorem computes, from the statement it elaborates
                           (let [goal (:type-ansatz (a/elab-signature (a/env) (a/parse-params params) prop))]
                             (pc/entry-key nm goal (mapv (comp str first) (a/parse-params params)) tactics)))
                  file (fn [k] (io/file dir (subs k 0 2) (subs k 2)))
                  k-add (key-of args)
                  k-mul (key-of other)]
              ;; pc-add-zero's entry now holds pc-mul-one's proof (renamed: same name, wrong term)
              (let [^ConstantInfo mul (env/lookup (do (apply prove-fresh! env0 other) (a/env))
                                                  (name/from-string "pc-mul-one"))]
                (is (.isFile (file k-mul)))
                (binding [pc/*dir* dir]
                  (#'pc/store! k-add [] (env/mk-thm (name/from-string "pc-add-zero") [] (.type mul) (.value mul)))))
              (let [[^ConstantInfo ci stats] (apply prove-fresh! env0 args)]
                (is (= {:rejected 1 :stored 1} stats))
                (is (some? ci)))))))
      (finally
        (reset! a/ansatz-env env0)
        (doseq [f (reverse (file-seq (io/file dir)))] (io/delete-file f true))))))
