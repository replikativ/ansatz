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

(deftest the-key-ignores-printer-bindings
  (binding [pc/*dir* "unused"]
    (let [goal (:type-ansatz (a/elab-signature (a/env) (a/parse-params '[n :- Nat]) '(= Nat (+ n 0) n)))
          script '[(simp [Nat.add_zero Nat.zero_add]) (rfl)]
          k (pc/entry-key 'pc-key goal ["n"] script)]
      (is (string? k))
      (is (= k (binding [*print-length* 1 *print-level* 1] (pc/entry-key 'pc-key goal ["n"] script)))))))

(deftest added-theorems-are-found-in-an-env-with-an-external-store
  ;; With an external lookup (the Mathlib store) Env.size is the store's size and does not grow,
  ;; so additions are detected by the local count.
  (let [base (.withExternalLookup ^ansatz.kernel.Env (a/env) (fn [_] nil) 10000000)
        ^ConstantInfo t (env/lookup (a/env) (name/from-string "Nat.add_zero"))
        aux (env/mk-thm (name/from-string "pc-aux-copy") [] (.type t) (.value t))
        after (.addConstant ^ansatz.kernel.Env base aux)]
    (is (= (.size ^ansatz.kernel.Env base) (.size ^ansatz.kernel.Env after)))
    (is (= [aux] (pc/added-constants base after)))))

(deftest failures-to-key-or-decode-are-misses
  (let [goal (:type-ansatz (a/elab-signature (a/env) (a/parse-params '[n :- Nat]) '(= Nat (+ n 0) n)))
        dir (temp-dir)]
    (try
      (binding [pc/*dir* dir]
        (testing "a statement the codec cannot encode (mdata) gives no key, not an error"
          (is (nil? (pc/entry-key 'pc-md (ansatz.kernel.Expr/mdata {} goal) ["n"] '[(simp)]))))
        (testing "type hints are part of the key, source positions are not"
          (let [k (fn [script] (pc/entry-key 'pc-meta goal ["n"] script))]
            (is (not= (k [(list 'f (with-meta 'x {:tag 'Nat}))])
                      (k [(list 'f (with-meta 'x {:tag 'Bool}))])))
            (is (= (k [(with-meta (list 'simp) {:line 1 :column 2})])
                   (k [(with-meta (list 'simp) {:line 40 :column 7})])))))
        (testing "an entry with trailing bytes, or cut short, is unreadable"
          (let [^ConstantInfo t (env/lookup (a/env) (name/from-string "Nat.add_zero"))
                k (pc/entry-key 'pc-dec goal ["n"] '[(simp)])
                f (io/file dir (subs k 0 2) (subs k 2))]
            (#'pc/store! k [] t)
            (is (vector? (pc/lookup k)))
            (let [bytes (java.nio.file.Files/readAllBytes (.toPath f))]
              (java.nio.file.Files/write (.toPath f) (byte-array (concat bytes [7]))
                                         ^"[Ljava.nio.file.OpenOption;" (make-array java.nio.file.OpenOption 0))
              (is (= ::pc/unreadable (pc/lookup k)))
              (java.nio.file.Files/write (.toPath f) (java.util.Arrays/copyOf bytes (- (alength bytes) 3))
                                         ^"[Ljava.nio.file.OpenOption;" (make-array java.nio.file.OpenOption 0))
              (is (= ::pc/unreadable (pc/lookup k)))))))
      (finally
        (doseq [f (reverse (file-seq (io/file dir)))] (io/delete-file f true))))))

(deftest review-edge-cases
  (let [goal (:type-ansatz (a/elab-signature (a/env) (a/parse-params '[n :- Nat]) '(= Nat (+ n 0) n)))
        dir (temp-dir)]
    (try
      (binding [pc/*dir* dir]
        (testing "a script too deeply nested to print is a miss, not a StackOverflowError"
          (let [deep (reduce (fn [acc _] [acc]) [] (range 200000))]
            (is (nil? (pc/entry-key 'pc-deep goal ["n"] [(list 'rfl deep)])))))
        (testing "reader positions inside metadata values do not change the key"
          (let [k (fn [line] (pc/entry-key 'pc-mv goal ["n"]
                                           [(list 'f (with-meta 'x {:- (with-meta (list 'List 'Nat) {:line line})}))]))]
            (is (= (k 1) (k 99)))))
        (testing "strings round-trip, supplementary characters included; malformed UTF-8 is refused"
          (let [bytes (java.io.ByteArrayOutputStream.)
                out (java.io.DataOutputStream. bytes)]
            (#'pc/write-str! out "a😀b")
            (is (= "a😀b" (#'pc/read-str (java.io.DataInputStream. (java.io.ByteArrayInputStream. (.toByteArray bytes))))))
            (is (thrown? Exception (#'pc/write-str! out (str "x" (char 0xD800)))))
            (is (thrown? Exception (#'pc/read-str (java.io.DataInputStream.
                                                   (java.io.ByteArrayInputStream. (byte-array [0 0 0 2 (unchecked-byte 0xC3) 0x28]))))))))
        (testing "only plain theorems are written"
          (let [^ConstantInfo t (env/lookup (a/env) (name/from-string "Nat.add_zero"))
                odd (env/mk-thm (name/from-string "pc-odd") [] (.type t) (.value t)
                                :all [(name/from-string "pc-odd") (name/from-string "pc-other")])
                k (pc/entry-key 'pc-odd goal ["n"] '[(simp)])]
            (#'pc/store! k [] odd)
            (is (nil? (pc/lookup k)))))
        (testing "a step that replaced an earlier local constant is not an addition"
          (let [^ConstantInfo t (env/lookup (a/env) (name/from-string "Nat.add_zero"))
                base (a/env)
                with-a (.addConstant ^ansatz.kernel.Env base (env/mk-thm (name/from-string "pc-local-a") [] (.type t) (.value t)))
                with-b (.addConstant ^ansatz.kernel.Env base (env/mk-thm (name/from-string "pc-local-b") [] (.type t) (.value t)))]
            (is (= ::pc/uncacheable (pc/added-constants with-a with-b)))
            (is (= [] (pc/added-constants with-a with-a))))))
      (finally
        (doseq [f (reverse (file-seq (io/file dir)))] (io/delete-file f true))))))
