(ns ansatz.export.writer-test
  "lean4export writer: what it writes reads back through our parser, checks in
   our kernel and re-exports to the same bytes; when tools/lean-replay is built,
   Lean 4's own kernel accepts it too."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [clojure.java.io :as io]
            [clojure.java.shell :as sh]
            [clojure.string :as str]
            [ansatz.core :as a]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.export.writer :as w]
            [ansatz.fixtures :as fixtures]))

(use-fixtures :once fixtures/isolated-session
  (fn [f] (binding [*ns* (the-ns 'ansatz.export.writer-test) a/*verbose* false]
            (a/load-init!) (f))))

(defn- export-str [env roots]
  (let [sw (java.io.StringWriter.)
        summary (w/write-closure! env roots sw)]
    [(str sw) summary]))

(defn- replay-text
  "Parse an export and replay it from an empty Env through the checked path."
  [text]
  (parser/with-parser-state
    (parser/parse-ndjson-string text)
    (fn [parsed]
      (let [{:keys [env stats]} (replay/replay (:decls parsed) :verify? true :stop-on-error? true)]
        {:env env :errors (:errors stats) :decls (count (:decls parsed))}))))

(def ^:private lean-replay "tools/lean-replay/.lake/build/bin/lean-replay")

(defn- lean-check
  "Run Lean's kernel on an export when tools/lean-replay is built; nil otherwise."
  [text]
  (when (.exists (io/file lean-replay))
    (let [f (java.io.File/createTempFile "ansatz-lean-export" ".ndjson")]
      (try (spit f text)
           (sh/sh lean-replay (str f))
           (finally (.delete f))))))

(def ^:private init-roots
  ;; theorems and definitions, an inductive with its recursor, the quotient
  ;; package (through Quot.sound) and a nested inductive (Lean.Syntax)
  ["Nat.add_comm" "List.length_append" "List.rec" "Quot.sound" "Lean.Syntax"])

(deftest init-closure-round-trips
  (let [[text summary] (export-str (a/env) init-roots)
        {:keys [env errors decls]} (replay-text text)]
    (is (= 0 errors))
    (is (= (:constants summary) decls))
    (is (str/starts-with? text "{\"meta\":"))
    (is (not (str/includes? text "\n\n")) "Lean's reader stops at the first empty line")
    (testing "writing what we read back gives the same file"
      (is (= text (first (export-str env init-roots)))))
    (is (= ["propext" "Quot.sound"] (filterv #{"propext" "Quot.sound"} (:axioms summary))))))

(deftest generated-declarations-round-trip
  (a/inductive WxShape [] (dot) (box [w Nat] [h Nat]))
  (a/defn wx-area [s :- WxShape] Nat (match s [dot 0] [(box w h) (* w h)]))
  (a/defn ^Nat wx-fact [^Nat n] :termination-by n (if (== n 0) 1 (* n (wx-fact (- n 1)))))
  (a/defn wx-greet [] String "héllo \"λ\"\n")
  (a/theorem wx-area-dot [] (= (wx-area WxShape.dot) 0) (rfl))
  (a/theorem wx-le [n :- Nat] (<= n (+ n (wx-area WxShape.dot))) (simp [wx-area]))
  (let [roots ["WxShape" "wx-area" "wx-fact" "wx-greet" "wx-area-dot" "wx-le"]
        [text summary] (export-str (a/env) roots)
        {:keys [env errors decls]} (replay-text text)]
    (is (= 0 errors))
    (is (= (:constants summary) decls))
    (is (str/includes? text "\"strVal\":\"héllo \\\"λ\\\"\\n\""))
    (is (= text (first (export-str env roots))))
    (when-let [{:keys [exit out err]} (lean-check text)]
      (testing "Lean 4's kernel accepts it"
        (is (= 0 exit) (str out err))
        (is (str/includes? out "Accepted"))))))

(deftest non-safe-constants-are-reported
  (let [summary (w/write-closure! (a/env) ["Nat.add_comm"] (java.io.StringWriter.))]
    (is (= [] (:non-safe summary)))))

(deftest unknown-root-throws
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unknown constant"
                        (w/write-closure! (a/env) ["no.such.constant"] (java.io.StringWriter.)))))
