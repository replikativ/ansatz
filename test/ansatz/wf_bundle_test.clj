(ns ansatz.wf-bundle-test
  "Lazy-prelude cohort guards. Parsing is stubbed where noted: these tests cover
   the resource/session boundary, not prelude kernel replay correctness."
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [ansatz.bundle :as bundle]
            [ansatz.core :as a]
            [ansatz.wf :as wf]
            [ansatz.state :as state]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as expr]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name]
            [ansatz.export.replay :as replay]
            [ansatz.export.parser :as parser])
  (:import [ansatz.kernel Env ExprStore]))

(defn- with-environment [environment f]
  (locking state/session-lock
    (let [before @state/ansatz-env]
      (try
        (reset! state/ansatz-env environment)
        (binding [a/*verbose* false] (f))
        (finally (reset! state/ansatz-env before))))))

(defn- stub-parser-state [declarations]
  ;; Parser clients own a Closeable expression store, even for an empty prelude.
  (assoc (parser/mk-parser-state) :decls declarations))

(deftest lazy-preludes-reject-another-bundle-before-parsing-or-mutation
  (let [manifest (bundle/verify!)
        old-manifest (assoc manifest :artifact/cohort "previous-generation")
        base (env/with-extension (Env.) :bundled-artifacts old-manifest)
        parsed? (atom false)]
    (with-environment base
      (fn []
        (with-redefs [parser/parse-ndjson-string (fn [_] (reset! parsed? true) (stub-parser-state []))]
          (doseq [load [wf/wf-fix-ensure-lex-prelude! wf/wf-fix-ensure-sizeof-prelude!]]
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"do not match requirements" (load)))
            (is (identical? base @state/ansatz-env))))
        (is (false? @parsed?))))))

(deftest lazy-preludes-use-the-matching-scoped-snapshot-without-reopening
  (bundle/with-verified
    (fn [manifest]
      (let [base (env/with-extension (Env.) :bundled-artifacts manifest)
            parsed (atom 0)]
        (with-environment base
          (fn []
            (with-redefs [bundle/classpath-bytes (fn [_] (throw (AssertionError. "snapshot must not reopen")))
                          parser/parse-ndjson-string (fn [_] (swap! parsed inc) (stub-parser-state []))]
              (wf/wf-fix-ensure-lex-prelude!)
              (wf/wf-fix-ensure-sizeof-prelude!)
              (is (= 2 @parsed))
              (is (identical? base @state/ansatz-env)))))))))

(deftest independently-checked-environments-without-bundle-provenance-still-use-the-prelude-path
  (let [base (Env.)
        parsed? (atom false)]
    (with-environment base
      (fn []
        (with-redefs [parser/parse-ndjson-string (fn [_] (reset! parsed? true) (stub-parser-state []))]
          (wf/wf-fix-ensure-lex-prelude!)
          (is @parsed?)
          (is (identical? base @state/ansatz-env)))))))

;; These explicit CI models test lazy admission through the real kernel. They do
;; not model native frontend execution or complete companion metadata activation.
(defn- constant [s] (expr/const' (name/from-string s) []))
(defn- model-base []
  (let [base (:env (replay/replay [(env/mk-axiom (name/from-string "A") []
                                                 (expr/sort' (level/succ level/zero)))]))
        instances {(name/from-string "FixtureClass") [{:name (name/from-string "prior")}]}]
    (-> base
        (env/with-extension :instances instances)
        (env/with-extension :simp-lemmas #{"prior"})
        (env/with-extension :matcher-info {"prior" {:fixture true}})
        (env/with-extension :custom {:preserve true}))))

(defn- model-prelude [safety]
  (let [A (constant "A")
        sentinel "Prod.Lex.right'"
        definition (fn [n value]
                     (env/mk-def (name/from-string n) [] A value :safety safety
                                 :all [(name/from-string "irrelevant-compiler-group")]))]
    [(definition "dependency" (constant sentinel))
     (env/mk-axiom (name/from-string "external") [] A)
     (definition sentinel
       (expr/app (expr/lam (name/from-string "ignored") A (constant "dependency") :default)
                 (constant "external")))]))

(defn- parser-state-for [declarations]
  (let [state (parser/mk-parser-state)
        ^ExprStore expressions (:exprs state)]
    (.storeBvar expressions 0 0)
    (.finishParsing expressions)
    (is (bytes? (.readRaw expressions 0)) "fixture backing store is readable before loading")
    (assoc state :decls declarations)))

(deftest lazy-prelude-replays-interleaved-non-safe-sccs-without-replacing-metadata
  (doseq [safety [:unsafe :partial]]
    (let [base (model-base)
          original-index @state/ansatz-instance-index
          parsed (parser-state-for (model-prelude safety))
          ^ExprStore expressions (:exprs parsed)
          calls (atom 0)]
      (try
        (with-environment base
          (fn []
            (with-redefs [parser/parse-ndjson-string (fn [_] (swap! calls inc) parsed)]
              (wf/wf-fix-ensure-lex-prelude!)
              (let [loaded @state/ansatz-env]
                (is (some? (env/lookup loaded (name/from-string "Prod.Lex.right'"))))
                (is (some? (env/lookup loaded (name/from-string "dependency"))))
                (doseq [key [:instances :simp-lemmas :matcher-info :custom]]
                  (is (= (env/get-extension base key nil) (env/get-extension loaded key nil))))
                (is (identical? original-index @state/ansatz-instance-index))
                (wf/wf-fix-ensure-lex-prelude!)
                (is (identical? loaded @state/ansatz-env))
                (is (= 1 @calls) "sentinel keeps repeated loading idempotent")))))
        (is (thrown? Exception (.readRaw expressions 0)) "parser backing store was closed")
        (finally (.close expressions))))))

(deftest failed-lazy-prelude-keeps-global-state-and-closes-parser-store
  (let [base (model-base)
        original-index @state/ansatz-instance-index
        parsed (parser-state-for [(env/mk-def (name/from-string "Prod.Lex.right'") []
                                              (constant "A") (constant "missing") :safety :unsafe)])
        ^ExprStore expressions (:exprs parsed)]
    (try
      (with-environment base
        (fn []
          (with-redefs [parser/parse-ndjson-string (fn [_] parsed)]
            (is (thrown-with-msg? Exception #"Replay stopped" (wf/wf-fix-ensure-lex-prelude!)))
            (is (identical? base @state/ansatz-env))
            (is (identical? original-index @state/ansatz-instance-index)))))
      (is (thrown? Exception (.readRaw expressions 0)))
      (finally (.close expressions)))))

(deftest lazy-prelude-rejects-partial-inductive-packages-before-publication
  (let [n (name/from-string "FixtureInductive")
        ctor-name (name/from-string "FixtureInductive.mk")
        inductive (env/mk-induct n [] (expr/sort' (level/succ level/zero)) :ctors [ctor-name])
        ctor (env/mk-ctor ctor-name [] (expr/const' n []) n 0 0 0)
        base (.addConstant (model-base) inductive)]
    (with-environment base
      (fn []
        (with-redefs [parser/parse-ndjson-string (fn [_] (stub-parser-state [inductive ctor]))]
          (is (thrown-with-msg? Exception #"Partially present inductive" (wf/wf-fix-ensure-lex-prelude!)))
          (is (identical? base @state/ansatz-env)))))))

(deftest lazy-prelude-skips-complete-existing-inductive-and-quotient-packages
  (let [parsed (parser/parse-ndjson-string
                (slurp (io/resource "ansatz/export/fixtures/quotient-4.29.ndjson") :encoding "UTF-8"))
        capture (:decls parsed)]
    (try
      (let [base (:env (replay/replay capture))
            base (.addConstant base (env/mk-axiom (name/from-string "A") []
                                                  (expr/sort' (level/succ level/zero))))
            declarations (into capture (model-prelude :partial))]
        (with-environment base
          (fn []
            (with-redefs [parser/parse-ndjson-string (fn [_] (stub-parser-state declarations))]
              (wf/wf-fix-ensure-lex-prelude!)
              (is (identical? (env/lookup base (name/from-string "Eq"))
                              (env/lookup @state/ansatz-env (name/from-string "Eq")))))
            (is (some? (env/lookup @state/ansatz-env (name/from-string "Prod.Lex.right'")))))))
      (finally (.close ^ExprStore (:exprs parsed))))))

(deftest lazy-prelude-rejects-partial-quotient-packages-before-publication
  (let [parsed (parser/parse-ndjson-string
                (slurp (io/resource "ansatz/export/fixtures/quotient-4.29.ndjson") :encoding "UTF-8"))
        capture (:decls parsed)
        q (first (filter #(.isQuot ^ansatz.kernel.ConstantInfo %) capture))
        base (.addConstant (model-base) q)]
    (try
      (with-environment base
        (fn []
          (with-redefs [parser/parse-ndjson-string (fn [_] (stub-parser-state capture))]
            (is (thrown-with-msg? Exception #"Partially present quotient" (wf/wf-fix-ensure-lex-prelude!)))
            (is (identical? base @state/ansatz-env)))))
      (finally (.close ^ExprStore (:exprs parsed))))))
