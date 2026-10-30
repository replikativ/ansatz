(ns java-ir-header-checks
  "Header-only admission and selected-body preparation, without Init restoration."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x]
            [java-ir-host-checks :as h]
            [java-ir-generation-checks :as g]))

(def ^:dynamic *basis* nil)
(def digest (apply str (repeat 64 "a")))
(defn empty-program [] (j/prepare-host-program *basis* [] []))
(defn header [binding row] (j/declaration-header binding (first (x/raw [row])) digest))
(def identity-row (c/decl "identity" [(c/p 1 "object")] "object" (c/ret 1)))
(defn slots [ctx] (g/field (:program ctx) "preparedBodies"))

(deftest authentic-headers-do-not-demand-or-retain-executable-bodies
  (let [base (empty-program) binding (j/source-binding base (Object.))
        original (assoc-in identity-row [:ir :fdecl :body] "deliberately not parsed")
        h (header binding original) ctx (assoc (j/register-headers base [h]) :explicit false)
        engine (j/machine ctx)]
    (try
      (is (= 1 (.functionCount (:program ctx))))
      (is (nil? (aget (slots ctx) 0)))
      (let [closure (j/make-closure! ctx engine "identity" [])]
        (is (= 1 (c/rc ctx closure)))
        (is (g/bad? #(j/call ctx engine "identity" [closure])))
        (is (= "idle" (j/phase ctx engine)))
        (is (= 1 (c/rc ctx closure)))
        (j/release! ctx engine closure))
      (finally (j/close! ctx engine)))))

(deftest materialization-links-one-body-and-preserves-ancestor-closures
  (let [base (empty-program) binding (j/source-binding base (Object.))
        caller (c/decl "caller" [(c/p 1 "object")] "object"
                       (c/let-ir 2 "object" (c/fap "identity" [(c/v 1)]) (c/ret 2)))
        f (header binding caller) target (header binding identity-row)
        headers (j/register-headers base [f])
        linked (j/materialize-body headers f (first (x/raw [caller])) [target])
        ready (j/materialize-body linked target (first (x/raw [identity-row])) [])]
    (is (some? (aget (slots linked) (j/function-id linked "caller"))))
    (is (nil? (aget (slots linked) (j/function-id linked "identity"))))
    (is (identical? (aget (slots linked) 0) (aget (slots ready) 0)))
    (doseq [explicit? [false true]
            :let [ctx (assoc headers :explicit explicit?) engine (j/machine ctx)
                  old (j/make-closure! ctx engine "caller" [])]]
      (try
        (j/install-program! ready engine)
        (is (= 42 (j/call ready engine "caller" [42])))
        (is (identical? old (j/call ready engine "caller" [old])))
        (is (= 1 (c/rc ctx old)))
        (j/release! ready engine old)
        (finally (j/close! ready engine))))))

(deftest rejected-row-or-dependency-preparation-never-publishes-partial-code
  (let [base (empty-program) binding (j/source-binding base (Object.))
        other-binding (j/source-binding base (Object.))
        caller (c/decl "caller" [(c/p 1 "object")] "object"
                       (c/let-ir 2 "object" (c/fap "identity" [(c/v 1)]) (c/ret 2)))
        f (header binding caller) target (header binding identity-row)
        foreign (header other-binding identity-row)
        extra (header binding (g/literal "extra" 99))
        ctx (j/register-headers base [f target])]
    (doseq [[row dependencies]
            [[(assoc-in caller [:ir :fdecl :type] "uint8") [target]]
             [caller [foreign]]
             [caller []]
             [caller [target extra]]
             [(assoc-in caller [:ir :fdecl :xs 0 :borrow] true) [target]]
             [(assoc-in caller [:ir :fdecl :body] ["ret" (c/v 99)]) [target]]]]
      (is (g/bad? #(j/materialize-body ctx f (first (x/raw [row])) dependencies)))
      (is (every? nil? (seq (slots ctx))))
      (is (= 2 (.functionCount (:program ctx)))))
    (let [ready (j/materialize-body ctx f (first (x/raw [caller])) [target])]
      (is (some? (aget (slots ready) 0)))
      (is (every? nil? (seq (slots ctx)))))))

(deftest header-registration-rejects-conflicting-name-identities
  (let [base (empty-program) binding (j/source-binding base (Object.))
        a (header binding identity-row)
        b (header (j/source-binding base (Object.)) identity-row)
        ctx (j/register-headers base [a])]
    (is (g/bad? #(j/register-headers ctx [b])))
    (is (= 1 (.functionCount (:program ctx))))
    (is (nil? (aget (slots ctx) 0)))))

(deftest known-unsupported-lanes-remain-metadata-and-cannot-execute
  (let [base (empty-program) binding (j/source-binding base (Object.))
        row (c/decl "wide" [(c/p 1 "uint64")] "uint64" (c/ret 1))
        h (header binding row) ctx (j/register-headers base [h])
        engine (j/machine ctx)]
    (try
      (is (nil? (aget (slots ctx) 0)))
      (is (g/bad? #(j/start! ctx engine "wide" [0])))
      (is (= "idle" (j/phase ctx engine)))
      (is (g/bad? #(j/materialize-body ctx h (first (x/raw [row])) [])))
      (is (g/bad? #(j/make-closure! ctx engine "wide" [])))
      (finally (j/close! ctx engine)))))

(deftest recursive-root-refuses-unprepared-code-before-taking-owned-input
  (let [base (empty-program) binding (j/source-binding base (Object.))
        h (header binding identity-row) ctx (assoc (j/register-headers base [h]) :explicit false)
        engine (j/machine ctx) closure (j/make-closure! ctx engine "identity" [])]
    (try
      (is (g/bad? #(j/call ctx engine "identity" [closure])))
      (is (= 1 (c/rc ctx closure)))
      (is (= "idle" (j/phase ctx engine)))
      (j/release! ctx engine closure)
      (finally (j/close! ctx engine)))))

(deftest header-keys-are-snapshotted-before-caller-mutation
  (let [base (empty-program) binding (j/source-binding base (Object.))
        row (first (x/raw [identity-row]))
        name (java.util.ArrayList. ["str" (java.util.ArrayList. ["anonymous"]) "identity"])
        mutable (assoc row "name" name "ir" (assoc-in (get row "ir") ["fdecl" "f"] name))
        h (j/declaration-header binding mutable digest)]
    (.set name 2 "changed")
    (let [ctx (j/register-headers base [h]) ready (j/materialize-body ctx h row [])
          engine (j/machine ready)]
      (try
        (is (= 0 (j/function-id ctx "identity")))
        (is (g/bad? #(j/function-id ctx "changed")))
        (is (= 42 (j/call ready engine "identity" [42])))
        (finally (j/close! ready engine))))))

(deftest unready-initialized-globals-refuse-sentinel-evaluation
  (let [base (empty-program) binding (j/source-binding base (Object.))
        row (assoc (c/decl "global" [] "object" ["unreachable"])
                   :runtime {:role "initialized" :initializer (c/name-ir "init-global")})
        h (header binding row) ctx (j/register-headers base [h])
        engine (j/machine ctx)]
    (try
      (let [message (c/failure #(j/start! ctx engine "global" []))]
        (is (re-find #"(?i)(initializ|global)" message))
        (is (not (re-find #"Unreachable" message))))
      (is (= "idle" (j/phase ctx engine)))
      (finally (j/close! ctx engine)))))

(deftest unprepared-ap-preserves-closure-and-captures-before-failing
  (doseq [explicit? [false]]
    (let [base (empty-program) binding (j/source-binding base (Object.))
          target (header binding (c/decl "target" [(c/p 1 "object") (c/p 2 "object")]
                                         "object" (c/ret 1)))
          ctx (assoc (j/extend-program (j/register-headers base [target])
                       (x/raw [(c/decl "fresh" [(c/p 1 "object")] "object"
                                       (c/let-ir 2 "object" (c/ctor 0 [] 1) (c/ret 2)))
                               (c/decl "pap" [(c/p 1 "object")] "object"
                                       (c/let-ir 2 "object" {:pap {:c (c/name-ir "target") :ys [(c/v 1)]}}
                                         (c/ret 2)))
                               (second g/common)])) :explicit explicit?)
          engine (j/machine ctx) capture (j/call ctx engine "fresh" [0])
          closure (j/call ctx engine "pap" [capture])]
      (try
        (is (nil? (aget (slots ctx) (j/function-id ctx "target"))))
        (is (= 1 (c/rc ctx capture) (c/rc ctx closure)))
        (is (re-find #"(?i)unprepared" (c/failure #(j/call ctx engine "apply" [closure 42]))))
        (is (= 1 (c/rc ctx capture) (c/rc ctx closure)))
        (finally
          (j/release! ctx engine closure)
          ;; General failed-frame cleanup remains outside this runtime profile.
          (c/failure #(j/close! ctx engine)))))))

(deftest static-extern-dispatch-cannot-bypass-initialized-global-readiness
  (let [base (empty-program) binding (j/source-binding base (Object.))
        spec (h/spec "research_global" [] [] "object")
        global (assoc (h/ext "global" spec)
                      :runtime {:role "initialized" :initializer (c/name-ir "init-global")})
        caller (c/decl "caller" [(c/p 1 "object")] "object"
                       (c/let-ir 2 "object" (c/fap "global" []) (c/ret 2)))
        gh (header binding global) ch (header binding caller)
        ctx (j/materialize-body (j/register-headers base [gh ch] [spec]) ch
                                (first (x/raw [caller])) [gh])
        engine (j/machine ctx)]
    (try
      (j/start! ctx engine "caller" [0])
      (is (re-find #"(?i)initialized global" (c/failure #(j/advance! ctx engine 1))))
      (is (nil? (j/host-request ctx engine)))
      (finally (c/failure #(j/close! ctx engine))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-header-checks)))
