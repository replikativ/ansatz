(ns prototype.parser-snapshot-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.parser-snapshot :as snapshot]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]))

(def provenance {:lean-version "4.33.1" :lean-commit "test-pinned-commit"
                 :runtime-profile {:wordBits 64 :target "x86_64-unknown-linux-gnu"}
                 :runtime-abi "prototype-test/1"})
(def root ["str" ["anonymous"] "saved-helper"])
(def functions {root (with-meta {:params [1] :body [:return [:var 1]]}
                      {:runtime-param-types ["object"]})})
(defn fixture []
  (let [[world value] (m/allocate (m/world functions) :ctor 0 [(m/->Tag 1) (m/->Builtin :inc) m/erased])
        [world closure] (m/expr world [:closure root []])]
    (assoc world :status :done :result closure :globals {root {:status :ready :value value}}
           :environment {:test value} :modules {:test {:status :ready}})))
(defn with-file [f]
  (let [file (java.io.File/createTempFile "parser-snapshot-test-" ".edn")]
    (try (f file) (finally (.delete file)))))

(deftest parser-checkpoint-roundtrip-and-callbacks
  (with-file
    (fn [file]
      (let [before (fixture) counts (snapshot/write! file before provenance)
            restored (snapshot/read! file functions provenance)]
        (is (= {:functions 1 :heap 2 :globals 1} counts))
        (is (= before restored))
        (is (identical? functions (:functions restored)))
        (is (= {root {:runtime-param-types ["object"]}} (update-vals (:functions restored) meta)))
        (doseq [backend [:reference :mutable :jvm]]
          (let [session (raw/open-functions functions {} {:backend backend})
                result (raw/call session restored root [(:result restored)])]
            (is (= (:result restored) (:value result)))
            (is (= (:heap before) (get-in result [:state :heap])))))))))

(deftest rebase-is-exact-with-additions-only
  (with-file
    (fn [file]
      (snapshot/write! file (fixture) provenance)
      (let [more (assoc functions :new {:params [] :body [:return [:imm 7]]})]
        (is (identical? more (:functions (snapshot/read! file more provenance)))))
      (doseq [bad [{}
                   (assoc-in functions [root :body] [:return [:imm 0]])
                   (update functions root with-meta {:runtime-param-types ["tobject"]})]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"executable or ABI mismatch"
                             (snapshot/read! file bad provenance))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"provenance mismatch"
                           (snapshot/read! file functions (assoc provenance :runtime-abi "changed")))))))

(deftest rejects-opaque-unfinished-or-resource-worlds
  (with-file
    (fn [file]
      (doseq [bad [(assoc (fixture) :status :paused)
                   (assoc (fixture) :kernel-environments {:opaque (Object.)})
                   (assoc (fixture) :other (Object.))
                   (first (m/resource (fixture) "native"))
                   (assoc (fixture) :other Float/NaN)
                   (assoc (fixture) :other Double/NaN)]]
        (is (thrown? clojure.lang.ExceptionInfo (snapshot/write! file bad provenance))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Nested executable metadata"
            (snapshot/write! file (assoc-in (fixture) [:functions root :body]
                                            (with-meta [:return [:imm 1]] {:hidden :abi})) provenance))))))

(deftest rejects-dangling-references-and-closure-targets
  (with-file
    (fn [file]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Dangling guest reference"
            (snapshot/write! file (assoc (fixture) :result (m/->Ref 999)) provenance)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"no executable target"
            (snapshot/write! file (assoc-in (fixture) [:heap 1 :function] :missing) provenance))))))

(deftest truncated-file-is-not-a-checkpoint
  (with-file
    (fn [file]
      (snapshot/write! file (fixture) provenance)
      (let [text (slurp file) end (.lastIndexOf text "[:end")]
        (spit file (subs text 0 end)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Truncated"
                           (snapshot/read! file functions provenance))))))
